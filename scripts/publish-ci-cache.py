#!/usr/bin/env python3
"""Publish opaque CI cache deltas; promote equivalent successful builds without rebuilding.

Run this workflow-pinned script in a fresh hosted job. --expected comes from trusted
GitHub/git metadata, separately from the candidate's staging artifact. It is the
only authority for revision names and build outcome. No candidate Lean environment,
project configuration, executable or proof is imported here.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import nullcontext
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile

_SPEC = importlib.util.spec_from_file_location("rh_cache_transport", Path(__file__).with_name("publish-lake-cache.py"))
transport = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(transport)

SCHEMA = 1
SHA40 = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
HASH = re.compile(r"[0-9a-f]{16}\Z")
ARTIFACT = re.compile(r"[0-9a-f]{16}\.ltar\Z")
ROOT = re.compile(r"[A-Za-z0-9_-]+(?:/[A-Za-z0-9_.-]+)*\Z")
MAX_JSON = 64 * 1024 * 1024
MAX_ARTIFACT = 1024 * 1024 * 1024
MAX_ENTRIES = 500000
MAX_UPLOAD_WORKERS = 32
UPLOAD_PROGRESS_INTERVAL = 250
REVALIDATE = "no-cache"
BASE_MANIFEST_SHA256 = transport.settings.MANIFEST_SHA
BASE_MANIFEST_URL = transport.PUBLIC_BASE_URL + f"/bootstrap/{transport.settings.REVISION}/modules.jsonl.gz"
IDENTITY = ("candidate_head", "candidate_tree", "source_tree", "build_roots", "lakefile_sha256", "manifest_sha256", "toolchain")
FINGERPRINT = ("source_tree", "build_roots", "lakefile_sha256", "manifest_sha256", "toolchain")
_HASH_HELPER = '''import Lake.Build.Trace
import Lean.Data.Json.FromToJson
open Lake Lean
 def main (args : List String) : IO Unit := do
  let [jobs, report] := args | throw <| IO.userError "expected jobs and report"
  let input ← IO.FS.Handle.mk jobs .read
  let output ← IO.FS.Handle.mk report .write
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let .ok value := Json.parse line | throw <| IO.userError "invalid hash job"
    let .ok file := value.getObjValAs? String "file" | throw <| IO.userError "missing file"
    let .ok name := value.getObjValAs? String "name" | throw <| IO.userError "missing name"
    let actual := (← computeBinFileHash file).toString
    output.putStrLn (Json.mkObj [("name", toJson name), ("actual", toJson actual)]).compress
  output.flush
'''


def canonical(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _pairs(values):
    result = {}
    for key, value in values:
        if key in result:
            raise ValueError(f"Duplicate JSON field: {key}")
        result[key] = value
    return result


def decode_json(value: bytes):
    return json.loads(value, object_pairs_hook=_pairs)


def regular_bytes(path: Path, maximum=MAX_JSON) -> bytes:
    """Read an ordinary bounded file without following an artifact-supplied symlink."""
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as handle:
        info = os.fstat(handle.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size > maximum:
            raise ValueError(f"Expected a bounded regular file: {path.name}")
        value = handle.read(maximum + 1)
        if len(value) > maximum:
            raise ValueError(f"File exceeds limit: {path.name}")
        return value


def fingerprint(identity: dict) -> str:
    return sha256(canonical({key: identity[key] for key in FINGERPRINT}))


def identity_fields(value: dict, *, toolchain=None) -> dict:
    if not isinstance(value, dict) or value.get("schema") != SCHEMA:
        raise ValueError("Expected receipt/metadata schema 1")
    for key in ("candidate_head", "candidate_tree", "source_tree"):
        if not isinstance(value.get(key), str) or not SHA40.fullmatch(value[key]):
            raise ValueError(f"Invalid {key}")
    for key in ("lakefile_sha256", "manifest_sha256"):
        if not isinstance(value.get(key), str) or not SHA256.fullmatch(value[key]):
            raise ValueError(f"Invalid {key}")
    roots = value.get("build_roots")
    if not isinstance(roots, dict) or len(roots) > 100:
        raise ValueError("build_roots must be a bounded path/tree dictionary")
    for name, tree in roots.items():
        if (not ROOT.fullmatch(name) or any(part in (".", "..") for part in name.split("/"))
                or name == "src" or not isinstance(tree, str) or not SHA40.fullmatch(tree)):
            raise ValueError("Invalid additional build root")
    approved = transport.TOOLCHAIN if toolchain is None else transport.settings.for_toolchain(toolchain).TOOLCHAIN
    if value.get("toolchain") != approved:
        raise ValueError("Only the workflow-pinned stock toolchain is allowed")
    return {key: value[key] for key in IDENTITY}



def select_toolchain(toolchain):
    global BASE_MANIFEST_SHA256, BASE_MANIFEST_URL
    changed = toolchain != transport.TOOLCHAIN
    selected = transport.select_toolchain(toolchain)
    if changed:
        BASE_MANIFEST_SHA256 = selected.MANIFEST_SHA
        BASE_MANIFEST_URL = transport.PUBLIC_BASE_URL + f"/bootstrap/{selected.REVISION}/modules.jsonl.gz"
    return selected

def expected_metadata(value: dict, *, promotion=False) -> dict:
    if not isinstance(value, dict):
        raise ValueError("expected trusted workflow metadata")
    select_toolchain(value.get("toolchain"))
    result = identity_fields(value)
    allowed = {"schema", *IDENTITY, "input_fingerprint"}
    if promotion:
        pass
    else:
        allowed |= {"base_revision", "base_map_sha256", "pr_head", "pr_number", "build_exit_code"}
        for key in ("base_revision", "pr_head"):
            if not isinstance(value.get(key), str) or not SHA40.fullmatch(value[key]):
                raise ValueError(f"Invalid trusted {key}")
        if not isinstance(value.get("base_map_sha256"), str) or not SHA256.fullmatch(value["base_map_sha256"]):
            raise ValueError("Invalid trusted base-map SHA256")
        if type(value.get("pr_number")) is not int or value["pr_number"] <= 0:
            raise ValueError("Expected an actual PR number from the trusted workflow")
        if type(value.get("build_exit_code")) is not int or not 0 <= value["build_exit_code"] <= 255:
            raise ValueError("Expected actual build exit code from the trusted workflow")
        result.update({key: value[key] for key in allowed - {"schema", *IDENTITY, "input_fingerprint"}})
    if set(value) - allowed:
        raise ValueError("Unexpected trusted metadata fields")
    if "input_fingerprint" in value and value["input_fingerprint"] != fingerprint(result):
        raise ValueError("Trusted input fingerprint does not match its fields")
    result.update(schema=SCHEMA, input_fingerprint=fingerprint(result))
    return result


def parse_map(contents: bytes) -> dict[str, str]:
    if len(contents) > MAX_JSON:
        raise ValueError("Output map exceeds limit")
    lines = contents.splitlines()
    if not lines or decode_json(lines[0]) != transport.SCHEMA:
        raise ValueError("Invalid Lake output-map schema")
    if len(lines) - 1 > MAX_ENTRIES:
        raise ValueError("Too many cache mappings")
    result = {}
    for line in lines[1:]:
        item = decode_json(line)
        if (not isinstance(item, list) or len(item) != 2 or not isinstance(item[0], str)
                or not HASH.fullmatch(item[0]) or not isinstance(item[1], str) or not ARTIFACT.fullmatch(item[1])):
            raise ValueError("Output map contains an unsafe input hash or artifact filename")
        if item[0] in result:
            raise ValueError("Duplicate output-map input hash")
        result[item[0]] = item[1]
    if not result:
        raise ValueError("No completed outputs to publish")
    return result


def encode_map(value: dict[str, str]) -> bytes:
    return canonical(transport.SCHEMA) + b"\n" + b"".join(canonical([key, artifact]) + b"\n" for key, artifact in sorted(value.items()))


def module_name(name) -> bool:
    return (isinstance(name, str) and len(name) <= 1024
            and re.fullmatch(r"[\w']+(?:\.[\w']+)*", name) is not None)


def parse_manifest(data: bytes, entries: dict[str, str], identity: dict | None = None) -> tuple[dict, dict]:
    with gzip.GzipFile(fileobj=io.BytesIO(data)) as source:
        plain = source.read(MAX_JSON + 1)
    if len(plain) > MAX_JSON:
        raise ValueError("Module manifest exceeds decompressed size limit")
    lines = plain.splitlines()
    header = decode_json(lines[0]) if lines else None
    if (not isinstance(header, dict) or header.get("schema") != SCHEMA
            or header.get("toolchain") != transport.TOOLCHAIN
            or type(header.get("modules")) is not int or header["modules"] != len(entries)):
        raise ValueError("Invalid module manifest header/count")
    if identity is not None:
        for key in FINGERPRINT:
            if header.get(key) != identity[key]:
                raise ValueError("Module manifest differs from trusted build inputs")
        if header.get("input_fingerprint") != fingerprint(identity):
            raise ValueError("Module manifest input fingerprint mismatch")
    rows, names = {}, set()
    for line in lines[1:]:
        row = decode_json(line)
        if (not isinstance(row, list) or len(row) != 4 or not module_name(row[0])
                or not isinstance(row[1], str) or not HASH.fullmatch(row[1])
                or not isinstance(row[2], str) or not ARTIFACT.fullmatch(row[2])
                or not isinstance(row[3], str) or not SHA256.fullmatch(row[3])):
            raise ValueError("Unsafe module manifest row")
        if row[1] in rows or row[0] in names or entries.get(row[1]) != row[2]:
            raise ValueError("Module manifest does not uniquely match its map")
        rows[row[1]] = row
        names.add(row[0])
    if set(rows) != set(entries):
        raise ValueError("Module manifest does not exactly cover output map")
    return header, rows


def encode_manifest(identity: dict, contents: bytes, rows: dict) -> bytes:
    header = {key: identity[key] for key in FINGERPRINT}
    header.update(schema=SCHEMA, map_sha256=sha256(contents), modules=len(rows), input_fingerprint=fingerprint(identity))
    plain = canonical(header) + b"\n" + b"".join(canonical(row) + b"\n" for row in sorted(rows.values(), key=lambda row: row[0]))
    return gzip.compress(plain, mtime=0)


def lake_hashes(paths: dict[str, Path], temporary: Path) -> dict[str, str]:
    """Hash bytes with stock Lake only: no archive unpacking or project imports."""
    if not paths:
        return {}
    helper = temporary / "HashArtifacts.lean"
    helper.write_text(_HASH_HELPER)
    jobs, report = temporary / "hash-jobs.jsonl", temporary / "hash-report.jsonl"
    jobs.write_bytes(b"".join(canonical({"name": name, "file": str(path)}) + b"\n" for name, path in paths.items()))
    env = transport.isolated_environment()
    elan = shutil.which("elan")
    if not elan:
        raise ValueError("elan with the pinned stock toolchain is required to verify artifact hashes")
    command = [elan, "run", transport.TOOLCHAIN, "lean"]
    library = subprocess.run([*command, "--print-libdir"], cwd=temporary, env=env, check=True, capture_output=True, text=True).stdout.strip()
    shared = "libLake_shared.dylib" if sys.platform == "darwin" else "libLake_shared.so"
    subprocess.run([*command, "--load-dynlib=" + str(Path(library) / shared), "--run", str(helper), str(jobs), str(report)],
                   cwd=temporary, env=env, check=True, capture_output=True, text=True)
    result = {}
    for line in regular_bytes(report).splitlines():
        item = decode_json(line)
        name, actual = item.get("name"), item.get("actual")
        if name not in paths or name in result or not isinstance(actual, str) or not HASH.fullmatch(actual):
            raise ValueError("Invalid result from stock artifact hasher")
        result[name] = actual
    if set(result) != set(paths):
        raise ValueError("Stock artifact hasher returned an incomplete report")
    return result


def snapshot(staging: Path, expected: dict, base: bytes, temporary: Path, base_manifest: bytes) -> dict:
    """Validate and privately snapshot data before loading publishing credentials."""
    if staging.is_symlink() or not staging.is_dir() or {p.name for p in staging.iterdir()} != {"receipt.json", "outputs.jsonl", "module-manifest.jsonl.gz", "artifacts"}:
        raise ValueError("Unexpected staging layout")
    artifacts = staging / "artifacts"
    if artifacts.is_symlink() or not artifacts.is_dir():
        raise ValueError("artifacts/ must be a real directory")
    receipt = decode_json(regular_bytes(staging / "receipt.json"))
    identity = identity_fields(receipt)
    permitted = {"schema", *IDENTITY, "input_fingerprint", "base_map_sha256", "build_exit_code", "map_sha256", "artifacts", "module_manifest_sha256", "module_manifest_bytes"}
    if set(receipt) - {"cache_map_sha256"} != permitted:
        raise ValueError("Receipt fields do not match the CI staging protocol")
    additional_maps = receipt.get("cache_map_sha256", [])
    if (not isinstance(additional_maps, list) or len(additional_maps) > 100
            or any(not isinstance(item, str) or not SHA256.fullmatch(item) for item in additional_maps)):
        raise ValueError("Invalid additional cache-map provenance")
    if any(identity[key] != expected[key] for key in IDENTITY):
        raise ValueError("Receipt identity differs from trusted workflow metadata")
    if receipt["input_fingerprint"] != expected["input_fingerprint"]:
        raise ValueError("Receipt input fingerprint does not match trusted build inputs")
    if type(receipt["build_exit_code"]) is not int or receipt["build_exit_code"] != expected["build_exit_code"]:
        raise ValueError("Receipt build outcome differs from trusted workflow outcome")
    if receipt["base_map_sha256"] != expected["base_map_sha256"] or sha256(base) != expected["base_map_sha256"]:
        raise ValueError("Baseline output map does not match its trusted SHA256")
    base_entries = parse_map(base)
    if sha256(base_manifest) != BASE_MANIFEST_SHA256:
        raise ValueError("Initial baseline module manifest does not match its pinned SHA256")
    base_header, base_rows = parse_manifest(base_manifest, base_entries)
    if base_header.get("map_sha256") != sha256(base):
        raise ValueError("Initial baseline manifest and output map differ")
    contents = regular_bytes(staging / "outputs.jsonl")
    if sha256(contents) != receipt["map_sha256"]:
        raise ValueError("Output map SHA256 differs from receipt")
    entries = parse_map(contents)
    module_manifest = regular_bytes(staging / "module-manifest.jsonl.gz")
    if (type(receipt["module_manifest_bytes"]) is not int
            or len(module_manifest) != receipt["module_manifest_bytes"]
            or sha256(module_manifest) != receipt["module_manifest_sha256"]):
        raise ValueError("Module manifest compressed size/SHA256 mismatch")
    header, rows = parse_manifest(module_manifest, entries, identity)
    if header.get("map_sha256") != sha256(contents):
        raise ValueError("Module manifest is not bound to the staged map")
    listed = receipt["artifacts"]
    if not isinstance(listed, list) or len(listed) > MAX_ENTRIES:
        raise ValueError("Invalid delta artifact list")
    declared = {}
    for item in listed:
        if not isinstance(item, dict) or set(item) != {"file", "size", "sha256"}:
            raise ValueError("Invalid delta artifact metadata")
        name = item["file"]
        if not isinstance(name, str) or not ARTIFACT.fullmatch(name) or name in declared:
            raise ValueError("Invalid or duplicate delta artifact filename")
        if type(item["size"]) is not int or not 0 < item["size"] <= MAX_ARTIFACT:
            raise ValueError("Invalid delta artifact size")
        if not isinstance(item["sha256"], str) or not SHA256.fullmatch(item["sha256"]):
            raise ValueError("Invalid delta artifact SHA256")
        declared[name] = item
    needed = set(entries.values()) - set(base_entries.values())
    if set(declared) != needed or {p.name for p in artifacts.iterdir()} != needed:
        raise ValueError("Delta files must exactly cover new map artifacts absent from the baseline")
    copied = temporary / "artifacts"
    copied.mkdir()
    paths = {}
    for name, item in declared.items():
        data = regular_bytes(artifacts / name, MAX_ARTIFACT)
        if len(data) != item["size"] or sha256(data) != item["sha256"]:
            raise ValueError(f"Delta artifact size/SHA256 mismatch: {name}")
        target = copied / name
        target.write_bytes(data)
        paths[name] = target
    actual = lake_hashes(paths, temporary)
    if any(actual[name] != name[:16] for name in paths):
        raise ValueError("Delta artifact filename differs from its actual stock Lake content hash")
    known = {row[2]: row[3] for row in base_rows.values()}
    known.update({name: item["sha256"] for name, item in declared.items()})
    if any(known.get(row[2]) != row[3] for row in rows.values()):
        raise ValueError("Module manifest artifact SHA256 lacks verified delta/baseline provenance")
    return {"receipt": receipt, "contents": contents, "entries": entries, "paths": paths, "expected": expected, "module_manifest": module_manifest}


class Object:
    def __init__(self, data: bytes, etag: str, metadata: dict | None = None):
        self.data, self.etag, self.metadata = data, etag, metadata or {}


class S3Store:
    def __init__(self, directory: Path, token_file=None, credentials_file=None):
        import boto3.session
        import botocore.loaders
        import botocore.session
        from botocore.config import Config
        from botocore.configprovider import ConstantProvider

        access, secret, token = transport.credentials(token_file, credentials_file)
        self.redactions = (access, secret, token)
        class PublisherSession(botocore.session.Session):
            # This pinned SDK hook otherwise imports ambient client plugins.
            def _register_client_plugins(self, client):
                pass

        # Keep SDK defaults, but remove every environment/file config provider.
        variables = {name: (None, None, value[2], None)
                     for name, value in PublisherSession.SESSION_VARIABLES.items()}
        variables.update(config_file=(None, None, "/dev/null", None),
                         credentials_file=(None, None, "/dev/null", None),
                         csm_enabled=(None, None, False, None))
        session = PublisherSession(session_vars=variables)
        for section in ("s3", "proxies_config"):
            session.get_component("config_store").set_config_provider(section, ConstantProvider({}))
        # Load only installed SDK models, including no ~/.aws/models overrides.
        session.register_component("data_loader", botocore.loaders.Loader(
            extra_search_paths=[botocore.loaders.Loader.BUILTIN_DATA_PATH], include_default_search_paths=False))
        self.client = boto3.session.Session(botocore_session=session).client(
            "s3", endpoint_url=transport.S3_ENDPOINT, region_name="auto",
            aws_access_key_id=access, aws_secret_access_key=secret, aws_session_token="", verify=True,
            config=Config(signature_version="s3v4", s3={"addressing_style": "path"},
                          max_pool_connections=MAX_UPLOAD_WORKERS, connect_timeout=30, read_timeout=120,
                          retries={"mode": "standard", "total_max_attempts": 5},
                          request_checksum_calculation="when_required", response_checksum_validation="when_required",
                          use_fips_endpoint=False, use_dualstack_endpoint=False, ignore_configured_endpoint_urls=True))

    def _call(self, operation: str, allowed=(), **kwargs) -> dict | str:
        from botocore.exceptions import BotoCoreError, ClientError

        try:
            return getattr(self.client, operation)(Bucket=transport.BUCKET, **kwargs)
        except ClientError as error:
            code = error.response.get("Error", {}).get("Code", "")
            if code in allowed:
                return code
            # Never expose SDK exception messages, request headers, or credentials.
            code = code if (isinstance(code, str) and re.fullmatch(r"[A-Za-z0-9_.-]{1,80}", code)
                            and not any(secret and secret in code for secret in self.redactions)) else "service failure"
            raise RuntimeError(f"R2 {operation} failed: {code}") from None
        except BotoCoreError:
            raise RuntimeError(f"R2 {operation} failed: transport failure") from None

    def get(self, key: str, maximum=MAX_JSON) -> Object | None:
        from botocore.exceptions import BotoCoreError

        result = self._call("get_object", ("NoSuchKey", "404"), Key=key, Range=f"bytes=0-{maximum}")
        if isinstance(result, str):
            return None
        body = result["Body"]
        try:
            if type(result.get("ContentLength")) is not int or not 0 <= result["ContentLength"] <= maximum:
                raise ValueError("Stored object exceeds size limit or has no valid size")
            data = body.read(maximum + 1)
            if len(data) > maximum or len(data) != result["ContentLength"]:
                raise ValueError("Stored object exceeds size limit or has inconsistent size")
            return Object(data, result["ETag"], result.get("Metadata", {}))
        except BotoCoreError:
            raise RuntimeError("R2 get_object failed: transport failure") from None
        finally:
            body.close()

    def put(self, key: str, data: bytes | Path, *, content_type: str, metadata: dict, etag: str | None = None) -> bool:
        """Create or compare-and-swap. Never silently overwrite an existing object."""
        with nullcontext(data) if isinstance(data, bytes) else data.open("rb") as body:
            condition = {"IfNoneMatch": "*"} if etag is None else {"IfMatch": etag}
            result = self._call("put_object", ("PreconditionFailed", "ConditionalRequestConflict"), Key=key, Body=body,
                                ContentType=content_type, Metadata=metadata,
                                CacheControl=transport.IMMUTABLE_CACHE_CONTROL if key.startswith(("artifacts/", "ci/maps/", "ci/module-manifests/")) else REVALIDATE,
                                **condition)
            return not isinstance(result, str)


def map_key(revision: str) -> str:
    if not SHA40.fullmatch(revision):
        raise ValueError("Invalid revision")
    return f"revisions/{transport.REPOSITORY}/tc/{transport.TOOLCHAIN_DIR}/{revision}.jsonl"


def receipt_key(revision: str, contents: bytes) -> str:
    return f"ci/receipts/{revision}/{sha256(contents)}.json"


def immutable(store, key: str, data: bytes | Path, *, content_type: str, metadata: dict, maximum=MAX_JSON):
    if store.put(key, data, content_type=content_type, metadata=metadata):
        return
    old = store.get(key, maximum)
    expected = data if isinstance(data, bytes) else regular_bytes(data, maximum)
    if old is None or old.data != expected:
        raise ValueError(f"Existing content-addressed object differs; preserved unchanged: {key}")


def record_blobs(store, record: dict, contents: bytes, manifest: bytes) -> dict:
    entries = parse_map(contents)
    header, _ = parse_manifest(manifest, entries, record["receipt"])
    if header.get("map_sha256") != sha256(contents):
        raise ValueError("Publication manifest/map binding mismatch")
    mkey, okey = f"ci/module-manifests/{sha256(manifest)}.jsonl.gz", f"ci/maps/{sha256(contents)}.jsonl"
    immutable(store, mkey, manifest, content_type="application/gzip", metadata={})
    immutable(store, okey, contents, content_type=transport.MAP_CONTENT_TYPE, metadata={})
    return {**record, **{key: record["receipt"][key] for key in IDENTITY},
            "input_fingerprint": record["receipt"]["input_fingerprint"],
            "build_exit_code": record["receipt"]["build_exit_code"],
            "map_sha256": sha256(contents), "map_key": okey,
            "module_manifest_sha256": sha256(manifest), "module_manifest_bytes": len(manifest), "module_manifest_key": mkey}


def bound_record(store, obj: Object, revision: str) -> dict:
    key = obj.metadata.get("receipt-key", "")
    if not re.fullmatch(r"ci/receipts/" + revision + r"/[0-9a-f]{64}\.json", key):
        raise ValueError("Candidate map has no correctly scoped immutable receipt")
    value = store.get(key)
    if value is None or sha256(value.data) != key.rsplit("/", 1)[1][:-5]:
        raise ValueError("Candidate receipt missing or content address mismatch")
    record = decode_json(value.data)
    if (not isinstance(record, dict) or record.get("schema") != SCHEMA
            or record.get("repository") != transport.REPOSITORY or record.get("map_sha256") != sha256(obj.data)):
        raise ValueError("Candidate receipt does not match its map")
    receipt = record.get("receipt")
    identity_fields(receipt)
    if receipt.get("candidate_head") != revision or receipt.get("input_fingerprint") != fingerprint(receipt):
        raise ValueError("Candidate receipt identity is invalid")
    return record


def record_manifest(store, record: dict) -> bytes:
    digest = record.get("module_manifest_sha256", "")
    if not isinstance(digest, str) or not SHA256.fullmatch(digest):
        raise ValueError("Receipt module manifest SHA256 is invalid")
    key = f"ci/module-manifests/{digest}.jsonl.gz"
    if record.get("module_manifest_key") != key:
        raise ValueError("Receipt module manifest key is invalid")
    value = store.get(key)
    if value is None or sha256(value.data) != digest or len(value.data) != record.get("module_manifest_bytes"):
        raise ValueError("Receipt module manifest bytes do not match")
    return value.data


def update_index(store, revision: str, record: dict):
    key = f"ci/revisions/{revision}.json"
    for _ in range(8):
        old = store.get(key)
        if old:
            previous = decode_json(old.data)
            if (previous.get("candidate_head") == record["candidate_head"]
                    and previous.get("build_exit_code") == 0 and record["build_exit_code"] != 0):
                return
        if store.put(key, canonical(record) + b"\n", content_type="application/json", metadata={}, etag=old.etag if old else None):
            return
    raise ValueError("Concurrent public receipt updates did not settle")


def update_input_index(store, record: dict):
    """Retain one complete build for equivalent source/config across revisions."""
    if record["build_exit_code"] != 0:
        return
    key = f"ci/inputs/{record['input_fingerprint']}.json"
    for _ in range(8):
        old = store.get(key)
        if old:
            previous = decode_json(old.data)
            if (previous.get("input_fingerprint") != record["input_fingerprint"]
                    or previous.get("repository") != transport.REPOSITORY):
                raise ValueError("Existing build-input index has a different scope")
            if previous.get("build_exit_code") == 0:
                return
        if store.put(key, canonical(record) + b"\n", content_type="application/json", metadata={}, etag=old.etag if old else None):
            return
    raise ValueError("Concurrent build-input index updates did not settle")


def update_map(store, revision: str, contents: bytes, record: dict, *, alias=False):
    """Keep successful candidate maps, union useful partial/PR-alias input keys."""
    key = map_key(revision)
    incoming = parse_map(contents)
    success = record["receipt"]["build_exit_code"] == 0
    identity = record["receipt"]["input_fingerprint"]
    for _ in range(8):
        old = store.get(key)
        old_success = (old is not None and old.metadata.get("build-success") == "true"
                       and old.metadata.get("map-kind") == "candidate")
        if (old and not alias and old.metadata.get("map-kind") != "pr-alias"
                and old.metadata.get("input-fingerprint") != identity):
            raise ValueError("Existing candidate map has a different or unbound input fingerprint")
        if old_success and not success and not alias:
            previous = bound_record(store, old, revision)
            update_index(store, revision, previous)
            update_input_index(store, previous)
            return old.data, previous
        value = contents
        if old and (alias or not success and old.metadata.get("map-kind") != "pr-alias"):
            merged = dict(incoming)
            merged.update(parse_map(old.data))  # Existing bytes win input-key conflicts.
            value = encode_map(merged)
        actual_record = record
        if not alias and value != contents:
            previous = bound_record(store, old, revision)
            _, before = parse_manifest(record_manifest(store, previous), parse_map(old.data), previous["receipt"])
            _, after = parse_manifest(record_manifest(store, record), incoming, record["receipt"])
            after.update(before)
            if len({row[0] for row in after.values()}) != len(after):
                raise ValueError("Same-candidate retries disagree on a module's build input")
            actual_record = record_blobs(store, record, value, encode_manifest(record["receipt"], value, after))
        encoded_record = canonical(actual_record) + b"\n"
        rkey = receipt_key(record["receipt"]["candidate_head"], encoded_record)
        immutable(store, rkey, encoded_record, content_type="application/json", metadata={})
        metadata = {"build-success": "true" if success or old_success and not alias else "false",
                    "input-fingerprint": identity, "receipt-key": rkey,
                    "map-kind": "pr-alias" if alias else "candidate"}
        if store.put(key, value, content_type=transport.MAP_CONTENT_TYPE, metadata=metadata, etag=old.etag if old else None):
            update_index(store, revision, actual_record)
            if not alias:
                update_input_index(store, actual_record)
            return value, actual_record
    raise ValueError("Concurrent cache publications did not settle; no unconditional overwrite attempted")


def publish(prepared: dict, store, *, upload_workers=MAX_UPLOAD_WORKERS) -> dict:
    if type(upload_workers) is not int or not 1 <= upload_workers <= MAX_UPLOAD_WORKERS:
        raise ValueError(f"upload_workers must be an integer from 1 to {MAX_UPLOAD_WORKERS}")
    expected, receipt = prepared["expected"], prepared["receipt"]
    paths = prepared["paths"]
    metadata = {item["file"]: item for item in receipt["artifacts"]}
    def upload(item):
        name, path = item
        immutable(store, f"artifacts/{transport.REPOSITORY}/{name[:16]}.art", path,
                  content_type=transport.ARTIFACT_CONTENT_TYPE,
                  metadata={"sha256": metadata[name]["sha256"]}, maximum=MAX_ARTIFACT)
    print(f"Uploading {len(paths)} cache artifacts with {upload_workers} workers", file=sys.stderr, flush=True)
    with ThreadPoolExecutor(max_workers=upload_workers) as pool:
        futures = [pool.submit(upload, item) for item in paths.items()]
        for completed, future in enumerate(as_completed(futures), 1):
            future.result()
            if completed % UPLOAD_PROGRESS_INTERVAL == 0 or completed == len(paths):
                print(f"Uploaded {completed}/{len(paths)} cache artifacts", file=sys.stderr, flush=True)
    # Names and digests already live in the complete module manifest. Keep the
    # discovery receipt small even when a build changes the whole project.
    public_receipt = {key: value for key, value in receipt.items() if key != "artifacts"}
    record = {"schema": SCHEMA, "repository": transport.REPOSITORY, "receipt": public_receipt,
              "build_receipt_sha256": sha256(canonical(receipt)), "delta_artifacts": len(paths),
              "map_sha256": sha256(prepared["contents"]), "verification": "opaque artifacts; stock Lake content hashes; no proof imports"}
    record = record_blobs(store, record, prepared["contents"], prepared["module_manifest"])
    contents, record = update_map(store, expected["candidate_head"], prepared["contents"], record)
    revisions = [expected["candidate_head"]]
    if expected["pr_head"] != expected["candidate_head"]:
        update_map(store, expected["pr_head"], contents, record, alias=True)
        revisions.append(expected["pr_head"])
    return {"published_revisions": revisions, "delta_artifacts": len(paths), "map_entries": len(prepared["entries"]), "build_success": receipt["build_exit_code"] == 0}


def promote(store, expected: dict, source: str, *, check_only=False) -> dict:
    # Index-body ETags change for an outcome-only transition. Map-body ETags
    # do not, so the public receipt is authoritative for partial/full races.
    index = store.get(f"ci/revisions/{source}.json")
    if index is None:
        raise ValueError("Promotion requires a published successful candidate map")
    record = decode_json(index.data)
    if (not isinstance(record, dict) or record.get("schema") != SCHEMA
            or record.get("repository") != transport.REPOSITORY):
        raise ValueError("Invalid published candidate receipt")
    immutable_record = store.get(receipt_key(source, index.data))
    if immutable_record is None or immutable_record.data != index.data:
        raise ValueError("Public candidate index is not bound to its immutable receipt")
    receipt = record.get("receipt")
    identity_fields(receipt)
    if (receipt.get("candidate_head") != source or receipt.get("build_exit_code") != 0
            or receipt.get("input_fingerprint") != fingerprint(receipt)
            or record.get("build_exit_code") != 0
            or any(record.get(key) != receipt[key] for key in IDENTITY)):
        raise ValueError("Promotion requires a successful exact-candidate receipt")
    if fingerprint(receipt) != expected["input_fingerprint"]:
        raise ValueError("Main build inputs differ; no promotion or rebuild was performed")
    digest = record.get("map_sha256", "")
    if (not isinstance(digest, str) or not SHA256.fullmatch(digest)
            or record.get("map_key") != f"ci/maps/{digest}.jsonl"):
        raise ValueError("Invalid receipt map key")
    source_map = store.get(record["map_key"])
    if source_map is None or sha256(source_map.data) != digest or receipt.get("map_sha256") != digest:
        raise ValueError("Successful candidate map bytes differ from the receipt")
    parse_map(source_map.data)
    manifest = record_manifest(store, record)
    parse_manifest(manifest, parse_map(source_map.data), expected)
    if not check_only:
        promoted = dict(receipt)
        promoted.update({key: expected[key] for key in IDENTITY})
        record = record_blobs(store, {**record, "receipt": promoted, "promoted_from": source}, source_map.data, manifest)
        update_map(store, expected["candidate_head"], source_map.data, record)
    return {"promoted_revision": expected["candidate_head"], "from_revision": source,
            "input_fingerprint": expected["input_fingerprint"], "check_only": check_only}


def public_map(revision: str) -> bytes:
    url = transport.PUBLIC_BASE_URL + "/" + map_key(revision)
    result = subprocess.run(["curl", "--disable", "--fail", "--silent", "--show-error", "--max-time", "120", "--max-filesize", str(MAX_JSON), url],
                            env=transport.isolated_environment(), check=True, capture_output=True)
    return result.stdout


def public_baseline_manifest() -> bytes:
    result = subprocess.run(["curl", "--disable", "--fail", "--silent", "--show-error", "--max-time", "120", "--max-filesize", str(MAX_JSON), BASE_MANIFEST_URL],
                            env=transport.isolated_environment(), check=True, capture_output=True)
    if sha256(result.stdout) != BASE_MANIFEST_SHA256:
        raise ValueError("Public baseline manifest failed its pinned SHA256")
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("publish", "promote"):
        command = commands.add_parser(name)
        command.add_argument("--expected", type=Path, required=True, help="trusted workflow/GitHub metadata, never candidate-provided")
        command.add_argument("--check-only", action="store_true")
        credentials = command.add_mutually_exclusive_group()
        credentials.add_argument("--token-file", type=Path)
        credentials.add_argument("--credentials-file", type=Path)
        if name == "publish":
            command.add_argument("staging", type=Path)
            command.add_argument("--upload-workers", type=int, choices=range(1, MAX_UPLOAD_WORKERS + 1),
                                 default=MAX_UPLOAD_WORKERS, help="bounded concurrent artifact uploads (default: %(default)s)")
            command.add_argument("--base-map", type=Path, help="optional local map, still checked against trusted SHA256")
            command.add_argument("--base-manifest", type=Path, help="optional local initial module manifest, still checked against its fixed SHA256")
        else:
            command.add_argument("--from-rev", required=True)
    args = parser.parse_args()
    expected = expected_metadata(decode_json(regular_bytes(args.expected)), promotion=args.command == "promote")
    with tempfile.TemporaryDirectory(prefix="rh-ci-cache-publisher-") as name:
        temporary = Path(name)
        if args.command == "publish":
            base = regular_bytes(args.base_map) if args.base_map else public_map(expected["base_revision"])
            baseline_manifest = regular_bytes(args.base_manifest) if args.base_manifest else public_baseline_manifest()
            prepared = snapshot(args.staging, expected, base, temporary, baseline_manifest)
            if args.check_only:
                print(json.dumps({"validated": True, "delta_artifacts": len(prepared["paths"]), "map_entries": len(prepared["entries"])}))
                return
            store = S3Store(temporary, args.token_file, args.credentials_file)
            result = publish(prepared, store, upload_workers=args.upload_workers)
        else:
            if not SHA40.fullmatch(args.from_rev):
                parser.error("--from-rev must be a full lowercase commit hash")
            store = S3Store(temporary, args.token_file, args.credentials_file)
            result = promote(store, expected, args.from_rev, check_only=args.check_only)
        print(json.dumps(result, sort_keys=True))
        if not args.check_only:
            revisions = result.get("published_revisions", [result.get("promoted_revision")])
            for revision in revisions:
                current = store.get(map_key(revision))
                if current is None:
                    raise ValueError("Published map disappeared before public verification")
                transport.verify_public(transport.PUBLIC_BASE_URL + "/" + map_key(revision), current.data)


if __name__ == "__main__":
    main()
