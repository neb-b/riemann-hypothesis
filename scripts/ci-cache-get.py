#!/usr/bin/env python3
"""Restore a successful public CI cache for the current clean build inputs.

Exit 3 means no equivalent successful CI receipt was found. Other failures must
not silently fall back: a matching receipt with corrupt bytes is an error.
"""
import argparse
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib
import urllib.error
import urllib.request

PUBLIC_BASE = "https://rh-cache.taucetiproject.org"
REPOSITORY = "leanprover-community/riemann-hypothesis"
BOOTSTRAP = "e50d09817ad81469f737e8f637561e6ccf86c670"
FIELDS = ("source_tree", "build_roots", "lakefile_sha256", "manifest_sha256", "toolchain")
SHA40 = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
HASH = re.compile(r"[0-9a-f]{16}\Z")
ARTIFACT = re.compile(r"[0-9a-f]{16}\.ltar\Z")
MAX_JSON = 64 * 1024 * 1024
MAX_RECEIPT = 2 * 1024 * 1024
MAX_MODULES = 500000

_SPEC = importlib.util.spec_from_file_location("rh_initial_restore", Path(__file__).with_name("restore-cache.py"))
restore = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(restore)
_SETTINGS = importlib.util.spec_from_file_location("rh_client_baseline", Path(__file__).with_name("cache-settings.py"))
settings = importlib.util.module_from_spec(_SETTINGS)
_SETTINGS.loader.exec_module(settings)


def digest(value):
    return hashlib.sha256(value).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def fingerprint(identity):
    return digest(canonical({key: identity[key] for key in FIELDS}))


def _pairs(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f"duplicate JSON field: {key}")
        value[key] = item
    return value


def decode(value):
    return json.loads(value, object_pairs_hook=_pairs)


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def current_identity(root):
    """Bind actual files and the clean Git src tree, without the initial archive's pins."""
    checked = set()
    files = {}
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        path = restore.local_path(root, Path(name), checked)
        if not path.is_file() or path.stat().st_size > MAX_JSON:
            raise ValueError(f"expected a bounded regular input: {name}")
        files[name] = path.read_bytes()
    restore.local_path(root, Path("src"), checked)
    subprocess.run(["git", "-C", str(root), "diff", "--no-ext-diff", "--no-textconv", "--quiet",
                    "HEAD", "--", "src", *files], check=True)
    if git(root, "ls-files", "--others", "--", "src"):
        raise ValueError("untracked source files differ from HEAD")
    config = tomllib.loads(files["lakefile.toml"].decode())
    if (config.get("srcDir", ".") != "src" or config.get("extern_lib")
            or any(key in config for key in ("buildDir", "leanLibDir", "irDir", "packagesDir", "manifestFile"))
            or any(lib.get("srcDir", ".") != "." for lib in config.get("lean_lib", []))):
        raise ValueError("public CI restoration currently supports the attested src/default build layout")
    identity = {
        "source_tree": git(root, "rev-parse", "HEAD:src"), "build_roots": {},
        "lakefile_sha256": digest(files["lakefile.toml"]),
        "manifest_sha256": digest(files["lake-manifest.json"]),
        "toolchain": files["lean-toolchain"].decode().strip(),
    }
    if not SHA40.fullmatch(identity["source_tree"]):
        raise ValueError("invalid current src Git tree")
    return identity


def fetch(key, maximum=MAX_JSON):
    request = urllib.request.Request(
        PUBLIC_BASE + "/" + key,
        headers={"User-Agent": "RiemannHypothesisCache/1.0", "Cache-Control": "no-cache"})
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            if response.status != 200:
                raise ValueError(f"unexpected cache HTTP status: {response.status}")
            data = response.read(maximum + 1)
    except urllib.error.HTTPError as error:
        if error.code == 404:
            return None
        raise
    if len(data) > maximum:
        raise ValueError(f"public metadata exceeds size limit: {key}")
    return data


def matching_record(data, identity):
    record = decode(data)
    if (not isinstance(record, dict) or type(record.get("schema")) is not int or record["schema"] != 1
            or record.get("repository") != REPOSITORY):
        raise ValueError("unexpected public CI receipt scope/schema")
    code = record.get("build_exit_code")
    if type(code) is not int or not 0 <= code <= 255:
        raise ValueError("invalid CI build exit code")
    if code != 0 or any(record.get(key) != identity[key] for key in FIELDS):
        return None
    if record.get("input_fingerprint") != fingerprint(identity):
        raise ValueError("successful CI receipt input fingerprint mismatch")
    for key in ("candidate_head", "candidate_tree"):
        if not isinstance(record.get(key), str) or not SHA40.fullmatch(record[key]):
            raise ValueError(f"invalid CI receipt {key}")
    for field, prefix, suffix in (("map", "ci/maps/", ".jsonl"),
                                  ("module_manifest", "ci/module-manifests/", ".jsonl.gz")):
        value = record.get(field + "_sha256")
        if (not isinstance(value, str) or not SHA256.fullmatch(value)
                or record.get(field + "_key") != prefix + value + suffix):
            raise ValueError(f"invalid immutable CI {field} identity")
    size = record.get("module_manifest_bytes")
    if type(size) is not int or not 0 < size <= MAX_JSON:
        raise ValueError("invalid CI module manifest size")
    nested = record.get("receipt")
    if nested is not None:
        if not isinstance(nested, dict) or any(nested.get(key) != record[key]
                for key in (*FIELDS, "candidate_head", "candidate_tree", "input_fingerprint", "build_exit_code")):
            raise ValueError("nested CI receipt differs from its public identity")
    return record


def find_record(root, identity, ancestor_limit=100, fetcher=fetch):
    lookup = f"ci/inputs/{fingerprint(identity)}.json"
    data = fetcher(lookup, MAX_RECEIPT)
    if data is not None:
        record = matching_record(data, identity)
        if record is not None:
            return record
    revisions = git(root, "rev-list", f"--max-count={ancestor_limit}", "HEAD").splitlines()
    for revision in revisions:
        # Do not issue HTTP requests for ancestors whose build inputs already differ.
        same = subprocess.run(["git", "-C", str(root), "diff", "--no-ext-diff", "--quiet", "HEAD", revision,
                               "--", "src", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]).returncode
        if same == 0:
            data = fetcher(f"ci/revisions/{revision}.json", MAX_RECEIPT)
            if data is not None:
                record = matching_record(data, identity)
                if record is not None:
                    if record["candidate_head"] != revision:
                        raise ValueError("CI revision index names a different candidate")
                    return record
        elif same != 1:
            raise ValueError("could not compare ancestor build inputs")
        if revision == BOOTSTRAP:
            break
    return None


def validated_blobs(record, identity, fetcher=fetch):
    contents = fetcher(record["map_key"], MAX_JSON)
    manifest = fetcher(record["module_manifest_key"], MAX_JSON)
    if contents is None or digest(contents) != record["map_sha256"]:
        raise ValueError("successful CI receipt's immutable map is missing or corrupt")
    if (manifest is None or digest(manifest) != record["module_manifest_sha256"]
            or len(manifest) != record["module_manifest_bytes"]):
        raise ValueError("successful CI receipt's immutable module manifest is missing or corrupt")
    lines = contents.splitlines()
    if not lines or decode(lines[0]) != "2026-03-17" or not 0 < len(lines) - 1 <= MAX_MODULES:
        raise ValueError("unsupported or empty CI Lake map")
    entries = {}
    for line in lines[1:]:
        row = decode(line)
        if (not isinstance(row, list) or len(row) != 2 or not all(isinstance(x, str) for x in row)
                or not HASH.fullmatch(row[0]) or not ARTIFACT.fullmatch(row[1]) or row[0] in entries):
            raise ValueError("invalid or duplicate CI map entry")
        entries[row[0]] = row[1]
    with gzip.GzipFile(fileobj=io.BytesIO(manifest)) as stream:
        plain = stream.read(MAX_JSON + 1)
    if len(plain) > MAX_JSON:
        raise ValueError("CI module manifest exceeds decompressed size limit")
    rows = plain.splitlines()
    header = decode(rows[0]) if rows else None
    if (not isinstance(header, dict) or type(header.get("schema")) is not int or header["schema"] != 1
            or any(header.get(key) != identity[key] for key in FIELDS)
            or header.get("input_fingerprint") != fingerprint(identity)
            or header.get("map_sha256") != record["map_sha256"]
            or type(header.get("modules")) is not int or header["modules"] != len(entries)):
        raise ValueError("CI module manifest is not bound to the current inputs and immutable map")
    # Only these two metadata globals change. The initial archive's configuration
    # allowlist/check_project stay intact; this path has its own exact Git/file binding.
    restore.HEADER = header
    restore.MANIFEST_SHA256 = record["module_manifest_sha256"]
    module_rows = restore.manifest_rows(manifest)
    inputs = set()
    for name, input_hash, artifact, sha256 in module_rows:
        if input_hash in inputs or entries.get(input_hash) != artifact:
            raise ValueError("CI module manifest does not uniquely cover its immutable map")
        inputs.add(input_hash)
    if inputs != set(entries):
        raise ValueError("CI module manifest does not completely cover its immutable map")
    return contents, module_rows


def consume(root, cache, record, identity, workers=24, fetcher=fetch):
    contents, rows = validated_blobs(record, identity, fetcher)
    if current_identity(root) != identity:
        raise ValueError("project inputs changed during cache lookup")
    restore.local_path(root, Path(".lake"), set()).mkdir(exist_ok=True)
    env = os.environ.copy()
    for key in list(env):
        if (key.startswith(("AWS_", "CLOUDFLARE_", "CF_"))
                or key in ("LAKE_CACHE_KEY", "LAKE_CACHE_ARTIFACT_ENDPOINT", "LAKE_CACHE_REVISION_ENDPOINT",
                           "LAKE_CACHE_SERVICE", "GH_TOKEN", "GITHUB_TOKEN", "HF_TOKEN")):
            env.pop(key)
    env.update(LAKE_CONFIG=str(root / "lakefile.toml"), LAKE_CACHE_DIR=str(cache),
               LAKE_ARTIFACT_CACHE="true", LAKE_RESTORE_ARTIFACTS="true", ELAN_TOOLCHAIN=identity["toolchain"])
    print(f"Fetching successful CI cache {record['candidate_head']} for current build inputs...", flush=True)
    with tempfile.TemporaryDirectory(prefix="ci-cache-", dir=root / ".lake") as temporary:
        path = Path(temporary) / "outputs.jsonl"
        path.write_bytes(contents)
        subprocess.run(["lake", "-q", "cache", "get", str(path), "--repo", REPOSITORY],
                       cwd=root, env=env, check=True)
    jobs = restore.restore_jobs(root, cache, rows)
    if current_identity(root) != identity:
        raise ValueError("project inputs changed before restoration")
    for job in jobs:
        for base in job["base"]:
            Path(base).mkdir(parents=True, exist_ok=True)
    env["RUST_MIN_STACK"] = str(max(int(env.get("RUST_MIN_STACK", "0")), 8388608))
    lean = Path(subprocess.check_output(["elan", "which", "lean"], cwd=root, env=env, text=True).strip())
    print(f"Restoring {len(jobs)} CI modules with stock leantar ({workers} workers)...", flush=True)
    subprocess.run([str(lean.with_name("leantar")), "--jobs", str(workers), "-f", "-x", "-j", "-"],
                   input=json.dumps(jobs), text=True, cwd=root, env=env, check=True)



def baseline_record(identity, fetcher=fetch):
    """Pinned compiled baseline for this toolchain, never a historic cross-version fallback."""
    if identity["toolchain"] != settings.TOOLCHAIN or settings.BASELINE is None:
        return None, {}
    revision = settings.REVISION
    map_key = f"revisions/{REPOSITORY}/tc/{settings.TOOLCHAIN_DIR}/{revision}.jsonl"
    manifest_key = f"bootstrap/{revision}/modules.jsonl.gz"
    contents, manifest = fetcher(map_key, MAX_JSON), fetcher(manifest_key, MAX_JSON)
    if (contents is None or manifest is None or digest(contents) != settings.MAP_SHA or
            digest(manifest) != settings.MANIFEST_SHA):
        raise ValueError("configured baseline map/manifest is missing or corrupt")
    with gzip.GzipFile(fileobj=io.BytesIO(manifest)) as stream:
        first = stream.readline(MAX_RECEIPT)
    header = decode(first)
    if any(header.get(key) != identity[key] for key in FIELDS):
        return None, {}
    record = {"schema": 1, "repository": REPOSITORY, **identity,
              "candidate_head": revision, "candidate_tree": "0" * 40,
              "input_fingerprint": fingerprint(identity), "build_exit_code": 0,
              "map_key": map_key, "map_sha256": settings.MAP_SHA,
              "module_manifest_key": manifest_key, "module_manifest_sha256": settings.MANIFEST_SHA,
              "module_manifest_bytes": len(manifest)}
    return record, {map_key: contents, manifest_key: manifest}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    parser.add_argument("--cache-dir", type=Path)
    parser.add_argument("--ancestor-limit", type=int, default=100)
    parser.add_argument("--jobs", type=int, default=24)
    args = parser.parse_args()
    if args.jobs < 1 or not 1 <= args.ancestor_limit <= 1000:
        parser.error("jobs must be positive; ancestor limit must be 1..1000")
    root = args.project.resolve()
    identity = current_identity(root)
    record = find_record(root, identity, args.ancestor_limit)
    cached = {}
    if record is None:
        record, cached = baseline_record(identity)
    if record is None:
        print("No equivalent successful cache found for the current build inputs.", flush=True)
        return 3
    cache = (args.cache_dir or Path(os.environ.get("LAKE_CACHE_DIR", str(root / ".lake/cache")))).resolve()
    consume(root, cache, record, identity, args.jobs,
            fetcher=lambda key, maximum=MAX_JSON: cached[key] if key in cached else fetch(key, maximum))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, EOFError, subprocess.CalledProcessError) as error:
        sys.exit(f"CI cache restore stopped: {error}")
