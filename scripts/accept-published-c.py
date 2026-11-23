#!/usr/bin/env python3
"""Install pinned, independently built C after exact/lint-only olean attestation.

The frozen oleans are rehashed before acceptance. Previously accepted C is never
replaced: the concurrent indexer/packer may already have observed those bytes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import runpy
import subprocess

REVISION = "d4a057ad21e2f699743f0ed061fa2be73edfd68b"
MANIFEST_SHA = "f5617e6efd433d24be871a9a34d52def5a316a2c09adc84c0c2cfdfd839cb7ff"
LIB_MANIFEST_SHA = "7bc0a0d8b3161a9457a2aab99ac5c4ff0ba09b871a6afbfa10b5c8119b1ddf27"


def sha(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        while data := stream.read(1024 * 1024):
            result.update(data)
    return result.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = args.project.resolve()
    work, extras = root / ".lake/bootstrap", root / ".lake/published-extras"
    code = runpy.run_path(str(root / "scripts/codegen-cache.py"))
    common = runpy.run_path(str(root / "scripts/bootstrap-cache.py"))
    provenance = common["PUBLISHED_PROVENANCE"]
    tree = subprocess.check_output(["git", "rev-parse", "HEAD:src"], cwd=root, text=True).strip()
    if tree != provenance["source_tree"] or sha(root / "lakefile.toml") not in provenance["lakefile_sha256"]:
        raise SystemExit("published C requires the original pinned source and compiler configuration")
    subprocess.run(["git", "diff", "HEAD", "--exit-code", "--", "src", "lean-toolchain", "lake-manifest.json"], cwd=root, check=True)
    if subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "--", "src"], cwd=root).strip():
        raise SystemExit("untracked source files are unsupported")
    if sha(root / "lake-manifest.json") != provenance["manifest_sha256"]:
        raise SystemExit("dependency manifest mismatch")
    manifest = extras / "project-ir.files.sha256"
    if sha(manifest) != MANIFEST_SHA:
        raise SystemExit("published C manifest checksum mismatch")
    lib_manifest = extras / "project-lib-traces-hashes.files.sha256"
    if sha(lib_manifest) != LIB_MANIFEST_SHA:
        raise SystemExit("published olean-hash manifest checksum mismatch")
    hash_checksums = {}
    for line in lib_manifest.read_text().splitlines():
        checksum, filename = line.split(maxsplit=1)
        filename = filename.lstrip("*").removeprefix("./")
        if filename.endswith(".olean.hash"):
            name = filename.removeprefix(".lake/build/lib/lean/").removesuffix(".olean.hash").replace("/", ".")
            hash_checksums[name] = checksum
    published = {}
    for line in manifest.read_text().splitlines():
        checksum, name = line.split(maxsplit=1)
        name = name.lstrip("*")
        if name.endswith(".c"):
            published[name.removeprefix(".lake/build/ir/").removesuffix(".c").replace("/", ".")] = checksum
    jobs = {j["name"]: j for j in common["read_jsonl"](work / "jobs.jsonl")}
    runtime = {r["name"] for p in work.glob("report-*.jsonl") for r in common["read_jsonl"](p) if r["needsCompile"]}
    attestations = {r["name"]: r for r in common["read_jsonl"](extras / "runtime-attestation.jsonl")}
    if set(attestations) != runtime:
        raise SystemExit("runtime attestation is incomplete")
    accepted = {name: row for name, row in attestations.items()
                if row.get("compatible") is True and row.get("mode") in ("exact", "lint-only")}
    for name, row in accepted.items():
        if hashlib.sha256(row["expected"].encode("ascii")).hexdigest() != hash_checksums.get(name):
            raise SystemExit(f"attestation is not bound to the published olean hash: {name}")
        if row["mode"] == "exact" and row["actual"] != row["expected"]:
            raise SystemExit(f"inconsistent exact attestation: {name}")
        if row["mode"] == "lint-only" and row.get("candidate") != row["expected"]:
            raise SystemExit(f"inconsistent diagnostic-only attestation: {name}")
    recheck_jobs = extras / "recheck-frozen.jsonl"
    with recheck_jobs.open("w") as stream:
        for name, row in accepted.items():
            if row["olean"] != jobs[name]["olean"]:
                raise SystemExit(f"attestation path mismatch: {name}")
            stream.write(json.dumps({"name": name, "file": jobs[name]["olean"], "expected": row["actual"]}) + "\n")
    tools = root / "scripts/cache-bootstrap"
    subprocess.run(["lake", "-d", str(tools), "build", "hash-outputs"], cwd=root, check=True)
    rechecks = extras / "recheck-frozen-results.jsonl"
    subprocess.run([str(tools / ".lake/build/bin/hash-outputs"), str(recheck_jobs), str(rechecks)], cwd=root, check=True)
    if any(not row["match"] for row in common["read_jsonl"](rechecks)):
        raise SystemExit("a frozen olean changed after attestation")
    checker = sha(tools / "CheckRuntime.lean")
    records = work / "codegen-records"
    records.mkdir(exist_ok=True)
    kept, installed = 0, 0
    for name, row in accepted.items():
        job = jobs[name]
        value = {"source": sha(job["source"]), "olean": sha(job["olean"]),
                 "setup": job["setup"], "args": job["leanArgs"], "checker": checker,
                 "manifest": provenance["manifest_sha256"], "toolchain": "leanprover/lean4:v4.33.1"}
        fingerprint = hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()
        identifier = hashlib.sha256(name.encode()).hexdigest()[:24]
        destination = Path(job["c"])
        record_path = records / (identifier + ".json")
        prior = None
        for path in (record_path, work / "c-delivery" / (identifier + ".json")):
            if path.exists():
                candidate = json.loads(path.read_text())
                if candidate.get("fingerprint") == fingerprint and destination.exists() and sha(destination) == candidate.get("cSha256"):
                    prior = candidate
                    break
        if prior is not None:
            if not record_path.exists():
                code["atomic_json"](record_path, prior)
            kept += 1
            continue
        source = extras / "incoming-c" / (name.replace(".", "/") + ".c")
        checksum = sha(source)
        if checksum != published.get(name):
            raise SystemExit(f"published C checksum mismatch: {name}")
        if destination.exists() and sha(destination) != checksum:
            raise SystemExit(f"unrecorded existing C differs; preserve and inspect: {name}")
        if not destination.exists():
            destination.parent.mkdir(parents=True, exist_ok=True)
            temporary = destination.with_suffix(".c.accepting")
            temporary.unlink(missing_ok=True)
            import os
            os.link(source, temporary)
            temporary.replace(destination)
        record = {"name": name, "id": identifier, "fingerprint": fingerprint,
                  "cSha256": checksum, "validation": {"basis": "published-olean-attestation",
                    "revision": REVISION, "mode": row["mode"], "externalHash": row["expected"]}}
        code["atomic_json"](record_path, record)
        installed += 1
        if installed % 1000 == 0:
            print(f"accepted {installed} published C files; preserved {kept}", flush=True)
    print(json.dumps({"installed": installed, "kept": kept, "unattested": len(runtime) - len(accepted)}), flush=True)


if __name__ == "__main__":
    main()
