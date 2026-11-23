#!/usr/bin/env python3
"""Optionally restore the pinned cache in one stock leantar process, after lake cache get."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.request

URL = "https://rh-cache.taucetiproject.org/bootstrap/e50d09817ad81469f737e8f637561e6ccf86c670/modules.jsonl.gz"
MANIFEST_SHA256 = "292caa386a620d935cfc736b56fcceaab9fe7073086693b62e899c1ee4725f04"
HEADER = {"schema": 1, "source_tree": "24df20b62d9976ccd20da819bc20b16f808f0fdd",
          "toolchain": "leanprover/lean4:v4.33.1",
          "map_sha256": "fed2443b161bd8194d9507e5c9c0e555b865dbba6963a0d57172723a439e6941",
          "modules": 175187}
CONFIG_HASHES = {"32af981ad33964a949f3e4d1e188e4afd0f85fecf6bf86e8ed133f00f16727ca",
                 "a1b98b41c96ad1e78906a210f5c6806218bda1701356215983033b2f77d44c99",
                 "e4686772edd6823c948d7cd6b0dbcf6168e1bfcce9d1e6713f884f646ce4bd0b"}
DEPENDENCIES_SHA256 = "fee57ee9ed399d0a638ca955e5ad40a37a36eeb9b6dfd9f5964114fa7bbe4774"
MODULE = re.compile(r"[\w']+(?:\.[\w']+)*\Z")  # Unicode names occur in the pinned tree.
HASH = re.compile(r"[0-9a-f]{16}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def check_project(root):
    tree = subprocess.check_output(["git", "rev-parse", "HEAD:src"], cwd=root, text=True).strip()
    if (tree != HEADER["source_tree"] or
            (root / "lean-toolchain").read_text().strip() != HEADER["toolchain"] or
            sha256(root / "lakefile.toml") not in CONFIG_HASHES or
            sha256(root / "lake-manifest.json") != DEPENDENCIES_SHA256):
        raise ValueError("source tree, toolchain, or configuration differs from the pinned cache")
    subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "src", "lean-toolchain", "lake-manifest.json"],
                   cwd=root, check=True)
    if subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "--", "src"], cwd=root):
        raise ValueError("untracked source files differ from the pinned cache")


def manifest_rows(contents):
    if hashlib.sha256(contents).hexdigest() != MANIFEST_SHA256:
        raise ValueError("bootstrap manifest SHA256 mismatch")
    lines = gzip.decompress(contents).splitlines()
    if not lines or json.loads(lines[0]) != HEADER:
        raise ValueError("bootstrap manifest metadata mismatch")
    rows = [json.loads(line) for line in lines[1:]]
    if len(rows) != HEADER["modules"]:
        raise ValueError("incomplete bootstrap manifest")
    seen = set()
    for row in rows:
        if not isinstance(row, list) or len(row) != 4 or not all(isinstance(x, str) for x in row):
            raise ValueError("invalid bootstrap module record")
        name, dep_hash, artifact, digest = row
        if (not MODULE.fullmatch(name) or not HASH.fullmatch(dep_hash) or
                not artifact.endswith(".ltar") or not HASH.fullmatch(artifact[:-5]) or
                not SHA256.fullmatch(digest) or name in seen):
            raise ValueError("invalid or duplicate bootstrap module")
        seen.add(name)
    return rows


def local_path(root, relative, checked):
    """Reject symlinks in source/output paths, including existing output files.

    Populate the ancestor-closed ``checked`` set only through this helper.
    """
    if any(part in ("", ".", "..") or "/" in part or "\\" in part
           for part in relative.parts):
        raise ValueError("unsafe module path")
    path = root / relative
    pending = []
    current = path
    while current != root and current not in checked:
        pending.append(current)
        current = current.parent
    for current in reversed(pending):
        if current.is_symlink():
            raise ValueError(f"symlink in source/output path: {current}")
        checked.add(current)
    return path


def restore_jobs(root, cache, rows):
    jobs, checked = [], set()
    for name, dep_hash, artifact, digest in rows:
        module = Path(*name.split("."))
        source = local_path(root, Path("src") / module.with_suffix(".lean"), checked)
        if not source.is_file():
            raise ValueError(f"missing source for {name}")
        archive = cache / "artifacts" / artifact
        if archive.is_symlink() or not archive.is_file() or sha256(archive) != digest:
            raise ValueError(f"missing or corrupt cached archive: {archive}; remove any corrupt copy and rerun lake cache get")
        bases = []
        for directory, suffixes in (("lib/lean", (".trace", ".olean", ".ilean")), ("ir", (".c",))):
            relative = Path(".lake/build") / directory / module
            for suffix in suffixes:
                local_path(root, relative.with_suffix(suffix), checked)
            bases.append(str(root / relative.parent))
        jobs.append({"file": str(archive), "hash": dep_hash, "base": bases})
    return jobs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    parser.add_argument("--cache-dir", type=Path, help="defaults to LAKE_CACHE_DIR or .lake/cache")
    parser.add_argument("--manifest", type=Path, help="use an already downloaded pinned modules.jsonl.gz")
    parser.add_argument("--jobs", type=int, default=24)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    root = args.project.resolve()
    check_project(root)
    if args.manifest:
        contents = args.manifest.read_bytes()
    else:
        request = urllib.request.Request(URL, headers={"User-Agent": "RiemannHypothesisCache/1.0"})
        with urllib.request.urlopen(request, timeout=60) as response:
            contents = response.read()
    rows = manifest_rows(contents)
    cache = (args.cache_dir or Path(os.environ.get("LAKE_CACHE_DIR", str(root / ".lake/cache")))).resolve()
    print(f"Checking {len(rows)} completed cached archives...", flush=True)
    jobs = restore_jobs(root, cache, rows)
    for job in jobs:
        for base in job["base"]:
            Path(base).mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    for key in list(env):
        if key.startswith(("AWS_", "CLOUDFLARE_", "CF_")) or key == "LAKE_CACHE_KEY":
            env.pop(key)
    env["ELAN_TOOLCHAIN"] = HEADER["toolchain"]
    env["RUST_MIN_STACK"] = str(max(int(env.get("RUST_MIN_STACK", "0")), 8388608))
    lean = Path(subprocess.check_output(["elan", "which", "lean"], cwd=root, env=env, text=True).strip())
    print(f"Restoring {len(jobs)} modules with stock leantar ({args.jobs} workers)...", flush=True)
    subprocess.run([str(lean.with_name("leantar")), "--jobs", str(args.jobs), "-f", "-x", "-j", "-"],
                   input=json.dumps(jobs), text=True, cwd=root, env=env, check=True)
    print("Restored. Check with: lake build --no-build", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        sys.exit(f"Bulk restore stopped: {error}\n"
                 "For other source/configurations, stock Lake reuses downloaded outputs of unchanged modules:\n"
                 "  source scripts/cache-env.sh && lake build")
