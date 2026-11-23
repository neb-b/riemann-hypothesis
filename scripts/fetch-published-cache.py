#!/usr/bin/env python3
"""Fetch and verify Jack McCarthy's pinned Lean 4.33.1 olean/ilean archive.

This imports no Lean code and creates no Lake traces. It preserves the published
file bytes for the subsequent cache bootstrap. Run it before normalization;
extracting it again deliberately restores the original published bytes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile
import tempfile
import time

REVISION = "9036e64326acf4acfae159b96664e9708445c1d1"
BASE_URL = f"https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/resolve/{REVISION}"
FILES = {
    "oleans.tar.zst": (28638044751, "953bab5386a7849527a11960f80a2fab427c49c637d6e94cc75788dd8f40196b"),
    "olean-manifest.sha256": (64388496, "fb3609ad73a17102e6e3e2346c5358a9c0957bcf5945442a7e5ffaa00c441ff5"),
}
PREFIX = ".lake/build/lib/lean/"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(8 * 1024 * 1024):
            h.update(chunk)
    return h.hexdigest()


def verify_download(path: Path, name: str) -> None:
    size, digest = FILES[name]
    if path.stat().st_size != size or sha256(path) != digest:
        raise ValueError(f"Published {name} size or SHA256 mismatch: {path}")


def fetch(directory: Path, name: str) -> Path:
    path = directory / name
    if path.exists():
        verify_download(path, name)
        return path
    directory.mkdir(parents=True, exist_ok=True)
    partial = directory / f"{name}.part"
    if partial.exists() and partial.stat().st_size == FILES[name][0]:
        verify_download(partial, name)
        partial.replace(path)
        return path
    subprocess.run(
        ["curl", "--fail", "--location", "--retry", "5", "--continue-at", "-",
         "--output", str(partial), f"{BASE_URL}/{name}"],
        check=True,
    )
    verify_download(partial, name)
    partial.replace(path)
    return path


def clean_path(name: str) -> str:
    while name.startswith("./"):
        name = name[2:]
    parts = PurePosixPath(name).parts
    if name.startswith("/") or ".." in parts or not parts:
        raise ValueError(f"Unsafe archive path: {name!r}")
    return str(PurePosixPath(name))


def read_manifest(path: Path) -> dict[str, str]:
    expected: dict[str, str] = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        match = re.fullmatch(r"([0-9a-f]{64}) [ *](.+)", line)
        if not match:
            raise ValueError(f"Malformed manifest line {number}")
        digest, name = match.groups()
        name = clean_path(name)
        if not name.startswith(PREFIX) or not name.endswith((".olean", ".ilean")):
            raise ValueError(f"Unexpected manifest entry: {name!r}")
        if name in expected:
            raise ValueError(f"Duplicate manifest path: {name!r}")
        expected[name] = digest
    if not expected:
        raise ValueError("The published manifest is empty")
    return expected


def extract_verified(archive_path: Path, expected: dict[str, str], project: Path) -> dict:
    """Extract only manifest-listed regular files, validating bytes before rename."""
    project = project.resolve(strict=True)
    directories = {project}
    seen: set[str] = set()
    total = 0
    started = time.monotonic()

    def ensure_directory(path: Path) -> None:
        if path in directories:
            return
        ensure_directory(path.parent)
        if path.is_symlink():
            raise ValueError(f"Symlink destination directory: {path}")
        path.mkdir(exist_ok=True)
        if not path.is_dir():
            raise ValueError(f"Non-directory destination: {path}")
        directories.add(path)

    proc = subprocess.Popen(["zstd", "-dc", str(archive_path)], stdout=subprocess.PIPE)
    assert proc.stdout is not None
    try:
        with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
            for member in archive:
                if member.isdir() and member.name in (".", "./"):
                    continue
                name = clean_path(member.name)
                if member.isdir():
                    if name in (".lake", ".lake/build", ".lake/build/lib", ".lake/build/lib/lean") or name.startswith(PREFIX):
                        continue
                    raise ValueError(f"Unexpected archive directory: {name!r}")
                if not member.isfile() or name not in expected or name in seen:
                    raise ValueError(f"Unexpected or duplicate archive member: {name!r} (type {member.type!r})")
                destination = project / name
                ensure_directory(destination.parent)
                if destination.is_symlink():
                    raise ValueError(f"Symlink destination file: {destination}")
                fd, temporary = tempfile.mkstemp(prefix=".published-cache-", dir=destination.parent)
                try:
                    digest = hashlib.sha256()
                    with archive.extractfile(member) as source, os.fdopen(fd, "wb") as output:
                        while chunk := source.read(1024 * 1024):
                            digest.update(chunk)
                            output.write(chunk)
                    if digest.hexdigest() != expected[name]:
                        raise ValueError(f"File SHA256 mismatch: {name!r}")
                    os.chmod(temporary, 0o644)
                    os.replace(temporary, destination)
                finally:
                    if os.path.exists(temporary):
                        os.unlink(temporary)
                seen.add(name)
                total += member.size
                if len(seen) % 5000 == 0:
                    print(json.dumps({"files": len(seen), "expected": len(expected), "bytes": total,
                                      "elapsed_s": round(time.monotonic() - started)}), flush=True)
        # Tar iteration stops at its end marker; drain padding before waiting.
        while proc.stdout.read(1024 * 1024):
            pass
        if proc.wait() != 0:
            raise RuntimeError("zstd decompression failed")
        if seen != expected.keys():
            raise ValueError(f"Archive is missing {len(expected.keys() - seen)} manifest files")
        return {"files": len(seen), "bytes": total, "elapsed_s": round(time.monotonic() - started)}
    finally:
        proc.stdout.close()
        if proc.poll() is None:
            proc.terminate()
            proc.wait()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd(), help="project checkout receiving .lake/build/lib/lean")
    parser.add_argument("--download-dir", type=Path, help="archive and manifest directory (default: PROJECT/.lake/published-cache)")
    parser.add_argument("--download-only", action="store_true", help="verify downloads without extracting")
    args = parser.parse_args()
    project = args.project.resolve(strict=True)
    downloads = (args.download_dir or project / ".lake/published-cache").resolve()
    archive = fetch(downloads, "oleans.tar.zst")
    manifest = fetch(downloads, "olean-manifest.sha256")
    if args.download_only:
        print(json.dumps({"verified_downloads": True, "directory": str(downloads)}))
        return
    report = extract_verified(archive, read_manifest(manifest), project)
    report.update({"revision": REVISION, "archive_sha256": FILES["oleans.tar.zst"][1],
                   "manifest_sha256": FILES["olean-manifest.sha256"][1]})
    (downloads / "extraction-verified.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"verified": True, **report}), flush=True)


if __name__ == "__main__":
    main()
