#!/usr/bin/env python3
"""Fetch the pinned Lake build extras without modifying any build outputs.

Run after bootstrap-cache.py --stop-after normalize. This prepares published C,
external olean hashes, and jobs for attest-extras. It does not attest or install C.
Existing derived files are reused only after checking their pinned per-file
SHA256 hashes; verification-summary.json never substitutes for those checks.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import runpy
import stat
import subprocess
import tarfile
import tempfile
import time

REVISION = "d4a057ad21e2f699743f0ed061fa2be73edfd68b"
BASE_URL = f"https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/resolve/{REVISION}/lake-extras"
FILES = {
    "project-ir.tar.zst": (42061265, "bed9e8a1ff1457540dbfc81ea712e42b5fee8d1119146e5afb8751c2c08054c3"),
    "project-lib-traces-hashes.tar.zst": (47727949, "1805536dd130d6ed769aa8133e20ff8424229be14b22afa46eac3dd5a3ff75f9"),
    "project-ir.files.sha256": (61760691, "f5617e6efd433d24be871a9a34d52def5a316a2c09adc84c0c2cfdfd839cb7ff"),
    "project-lib-traces-hashes.files.sha256": (98334614, "7bc0a0d8b3161a9457a2aab99ac5c4ff0ba09b871a6afbfa10b5c8119b1ddf27"),
}
LIB_PREFIX = ".lake/build/lib/lean/"
IR_PREFIX = ".lake/build/ir/"
HASH = re.compile(r"[0-9a-f]{16}\Z")


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while data := stream.read(8 * 1024 * 1024):
            digest.update(data)
    return digest.hexdigest()


def regular(path):
    try:
        return stat.S_ISREG(path.lstat().st_mode)
    except FileNotFoundError:
        return False


def reject_symlinks(path):
    for parent in (path, *path.parents):
        if parent.is_symlink():
            raise ValueError(f"symlink path is unsupported: {parent}")


def checked_directory(path):
    """Reject symlink ancestors before creating or reading derived files."""
    reject_symlinks(path)
    path.mkdir(parents=True, exist_ok=True)


def atomic_bytes(path, data):
    checked_directory(path.parent)
    if path.is_symlink():
        raise ValueError(f"symlink destination: {path}")
    fd, temporary = tempfile.mkstemp(prefix=".published-extra-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
        os.chmod(temporary, 0o644)
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def atomic_json(path, value):
    atomic_bytes(path, (json.dumps(value, separators=(",", ":")) + "\n").encode())


def fetch(directory, name):
    path = directory / name
    size, expected = FILES[name]

    def verify(candidate):
        if not regular(candidate) or candidate.stat().st_size != size or sha256(candidate) != expected:
            raise ValueError(f"published {name} size or SHA256 mismatch: {candidate}")

    if path.exists() or path.is_symlink():
        verify(path)
        return
    partial = path.with_name(path.name + ".part")
    if partial.is_symlink() or (partial.exists() and not regular(partial)):
        raise ValueError(f"invalid partial download: {partial}")
    if not partial.exists() or partial.stat().st_size != size:
        subprocess.run(["curl", "--silent", "--show-error", "--fail", "--location", "--retry", "5", "--continue-at", "-",
                        "--output", str(partial), f"{BASE_URL}/{name}"], check=True)
    verify(partial)
    partial.replace(path)


def clean_path(name):
    while name.startswith("./"):
        name = name[2:]
    parts = PurePosixPath(name).parts
    if not parts or name.startswith("/") or ".." in parts or "\\" in name:
        raise ValueError(f"unsafe archive path: {name!r}")
    return str(PurePosixPath(name))


def module_name(path, prefix, suffix):
    return path[len(prefix):-len(suffix)].replace("/", ".")


def read_manifest(path, prefix, suffixes, selected):
    result = {}
    seen = set()
    with path.open() as stream:
        for number, line in enumerate(stream, 1):
            match = re.fullmatch(r"([0-9a-f]{64}) [ *](.+)\n?", line)
            if not match:
                raise ValueError(f"malformed manifest line {number}: {path}")
            digest, name = match.groups()
            name = clean_path(name)
            if not name.startswith(prefix) or not name.endswith(suffixes) or name in seen:
                raise ValueError(f"unexpected or duplicate manifest path: {name}")
            seen.add(name)
            if selected(name):
                result[name] = digest
    if not result:
        raise ValueError(f"manifest selects no files: {path}")
    return result


@contextmanager
def archive_members(path, prefix, suffixes):
    proc = subprocess.Popen(["zstd", "-dc", str(path)], stdout=subprocess.PIPE)
    assert proc.stdout is not None
    try:
        with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
            seen = set()

            def entries():
                for member in archive:
                    name = clean_path(member.name)
                    if not member.isfile() or not name.startswith(prefix) or not name.endswith(suffixes) or name in seen:
                        raise ValueError(f"unexpected archive member: {name}")
                    seen.add(name)
                    yield name, archive.extractfile(member)

            yield entries()
        # Drain tar padding before waiting, avoiding a blocked decompressor pipe.
        while proc.stdout.read(1024 * 1024):
            pass
        if proc.wait() != 0:
            raise RuntimeError(f"zstd decompression failed: {path}")
    finally:
        proc.stdout.close()
        if proc.poll() is None:
            proc.terminate()
            proc.wait()


def load_plan(project):
    common = runpy.run_path(str(Path(__file__).with_name("bootstrap-cache.py")))
    provenance = common["PUBLISHED_PROVENANCE"]
    if (project / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.1":
        raise ValueError("published extras require stock Lean 4.33.1")
    tree = subprocess.check_output(["git", "rev-parse", "HEAD:src"], cwd=project, text=True).strip()
    if tree != provenance["source_tree"] or sha256(project / "lakefile.toml") not in provenance["lakefile_sha256"]:
        raise ValueError("source/configuration differ from the pinned published build")
    if sha256(project / "lake-manifest.json") != provenance["manifest_sha256"]:
        raise ValueError("dependency manifest differs from the published build")
    subprocess.run(["git", "diff", "HEAD", "--exit-code", "--", "src", "lean-toolchain", "lake-manifest.json"], cwd=project, check=True)
    if subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "--", "src"], cwd=project).strip():
        raise ValueError("untracked source files are unsupported")
    work = project / ".lake/bootstrap"
    if not json.loads((work / "state.json").read_text()).get("normalized"):
        raise ValueError("first run bootstrap-cache.py --stop-after normalize")
    jobs = {}
    for job in common["read_jsonl"](work / "jobs.jsonl"):
        name = job["name"]
        parts = name.split(".")
        if name in jobs or any(not p or p in (".", "..") or "/" in p or "\\" in p for p in parts):
            raise ValueError(f"invalid or duplicate module: {name!r}")
        expected = project.joinpath(".lake/build/lib/lean", *parts).with_suffix(".olean")
        reject_symlinks(expected)
        if not regular(expected):
            raise ValueError(f"missing normalized olean: {name}")
        if not Path(job["olean"]).is_absolute() or Path(job["olean"]).resolve() != expected.resolve():
            raise ValueError(f"unexpected olean path: {name}")
        jobs[name] = job
    classified = {}
    for report in sorted(work.glob("report-*.jsonl")):
        for row in common["read_jsonl"](report):
            name, value = row["name"], row["needsCompile"]
            if name not in jobs or not isinstance(value, bool) or (name in classified and classified[name] != value):
                raise ValueError(f"inconsistent normalizer classification: {name}")
            classified[name] = value
    if set(classified) != set(jobs):
        raise ValueError("normalizer reports are incomplete")
    return jobs, {name for name, value in classified.items() if value}


def collect_hashes(base, expected):
    path = base / "external-olean-hashes.json"
    if regular(path):
        try:
            prior = json.loads(path.read_text())
            if set(prior) == {module_name(n, LIB_PREFIX, ".olean.hash") for n in expected} and all(
                isinstance(value, str) and HASH.fullmatch(value)
                and hashlib.sha256(value.encode()).hexdigest() == expected[LIB_PREFIX + name.replace(".", "/") + ".olean.hash"]
                for name, value in prior.items()
            ):
                return prior
        except (ValueError, TypeError, KeyError):
            pass
    result = {}
    with archive_members(base / "project-lib-traces-hashes.tar.zst", LIB_PREFIX,
                         (".trace", ".olean.hash", ".ilean.hash")) as entries:
        for name, stream in entries:
            if not name.endswith(".olean.hash"):
                continue
            if name not in expected:
                raise ValueError(f"hash missing from manifest: {name}")
            data = stream.read()
            value = data.decode("ascii")
            if not HASH.fullmatch(value) or hashlib.sha256(data).hexdigest() != expected[name]:
                raise ValueError(f"native hash verification failed: {name}")
            result[module_name(name, LIB_PREFIX, ".olean.hash")] = value
    if len(result) != len(expected):
        raise ValueError("external olean hashes are incomplete")
    atomic_json(path, result)
    return result


def collect_c(base, expected):
    incoming = base / "incoming-c"
    checked_directory(incoming)
    needed = set()
    for name, digest in expected.items():
        path = incoming / name[len(IR_PREFIX):]
        checked_directory(path.parent)
        if not regular(path) or sha256(path) != digest:
            needed.add(name)
    if needed:
        seen = set()
        with archive_members(base / "project-ir.tar.zst", IR_PREFIX, (".c", ".c.hash")) as entries:
            for name, stream in entries:
                if name not in needed:
                    continue
                data = stream.read()
                if hashlib.sha256(data).hexdigest() != expected[name]:
                    raise ValueError(f"published C verification failed: {name}")
                atomic_bytes(incoming / name[len(IR_PREFIX):], data)
                seen.add(name)
        if seen != needed:
            raise ValueError("runtime C archive is incomplete")
    return sum((incoming / n[len(IR_PREFIX):]).stat().st_size for n in expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    args = parser.parse_args()
    project = args.project.resolve(strict=True)
    jobs, runtime = load_plan(project)
    base = project / ".lake/published-extras"
    checked_directory(base)
    started = time.monotonic()
    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(lambda name: fetch(base, name), FILES))
    expected_hashes = read_manifest(base / "project-lib-traces-hashes.files.sha256", LIB_PREFIX,
                                    (".trace", ".olean.hash", ".ilean.hash"), lambda n: n.endswith(".olean.hash"))
    external = collect_hashes(base, expected_hashes)
    if set(external) != set(jobs):
        raise ValueError("published hash coverage differs from the planned source modules")
    expected_c = read_manifest(base / "project-ir.files.sha256", IR_PREFIX, (".c", ".c.hash"),
                               lambda n: n.endswith(".c") and module_name(n, IR_PREFIX, ".c") in runtime)
    if {module_name(n, IR_PREFIX, ".c") for n in expected_c} != runtime:
        raise ValueError("published C does not cover every runtime module")
    total = collect_c(base, expected_c)
    attestation = b"".join((json.dumps({"name": name, "olean": jobs[name]["olean"], "expected": external[name]},
                                      separators=(",", ":")) + "\n").encode() for name in sorted(runtime))
    atomic_bytes(base / "runtime-attest-jobs.jsonl", attestation)
    summary = {"schemaVersion": 1, "revision": REVISION, "complete": True,
               "toolchain": "leanprover/lean4:v4.33.1", "module_count": len(jobs),
               "external_olean_hashes": len(external), "runtime_c_files": len(runtime), "runtime_c_bytes": total,
               "pins": {name: digest for name, (_, digest) in FILES.items()},
               "elapsed_s": round(time.monotonic() - started, 1)}
    atomic_json(base / "verification-summary.json", summary)
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
