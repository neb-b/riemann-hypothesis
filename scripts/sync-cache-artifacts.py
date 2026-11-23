#!/usr/bin/env python3
"""Preupload completed LTARs as they arrive; never publish revision mappings.

The producer must install immutable {content-hash}.ltar files by atomic rename
(normal rsync behavior). Partial rsync files and outputs.jsonl are ignored.
Publication of a complete revision is a separate publish-lake-cache.py step.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import stat
import tempfile
import time


def publisher():
    path = Path(__file__).with_name("publish-lake-cache.py")
    spec = importlib.util.spec_from_file_location("riemann_cache_publisher", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def alias_completed(directory: Path, aliases: Path, pattern: re.Pattern) -> dict:
    count, total = 0, 0
    with os.scandir(directory) as entries:
        for entry in entries:
            if entry.name == "outputs.jsonl" or entry.name.startswith("."):
                continue
            if not pattern.fullmatch(entry.name):
                raise ValueError(f"Unexpected artifact filename: {entry.name}")
            metadata = entry.stat(follow_symlinks=False)
            if not stat.S_ISREG(metadata.st_mode) or metadata.st_size == 0:
                raise ValueError(f"Artifact is not a nonempty regular file: {entry.name}")
            target = aliases / (entry.name[:16] + ".art")
            if target.exists() or target.is_symlink():
                existing = target.stat(follow_symlinks=False)
                if not stat.S_ISREG(existing.st_mode) or existing.st_size != metadata.st_size:
                    raise ValueError(f"Previously seen immutable artifact changed: {entry.name}")
            else:
                # aliases is a sibling of directory, so this stays on the same filesystem.
                os.link(entry.path, target, follow_symlinks=False)
                if not stat.S_ISREG(target.stat(follow_symlinks=False).st_mode):
                    raise ValueError(f"Artifact changed during alias creation: {entry.name}")
            count += 1
            total += metadata.st_size
    return {"completed_artifacts": count, "completed_bytes": total}


def main() -> None:
    pub = publisher()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path, help="flat directory progressively receiving completed .ltar files")
    parser.add_argument("--repo", default=pub.REPOSITORY)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--once", action="store_true", help="one upload pass (default)")
    group.add_argument("--watch", action="store_true", help="repeat while completed files arrive")
    parser.add_argument("--interval", type=float, default=30, help="seconds between completed upload passes")
    parser.add_argument("--concurrency", type=int, default=50)
    credentials = parser.add_mutually_exclusive_group()
    credentials.add_argument("--token-file", type=Path)
    credentials.add_argument("--credentials-file", type=Path)
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*/[A-Za-z0-9][A-Za-z0-9_.-]*", args.repo):
        parser.error("--repo must be a GitHub owner/repository scope")
    if args.interval < 1 or not 1 <= args.concurrency <= 100:
        parser.error("--interval must be at least 1 second; --concurrency must be between 1 and 100")
    directory = args.directory.absolute()
    if directory.is_symlink() or not directory.is_dir():
        parser.error("directory must be a real existing directory")
    aws = shutil.which("aws")
    if aws is None:
        parser.error("the AWS CLI is required")
    access, secret, token = pub.credentials(args.token_file, args.credentials_file)
    redactions = (f"{access}:{secret}", secret, token)
    with tempfile.TemporaryDirectory(prefix=".r2-artifact-sync-", dir=directory.parent) as name:
        temporary = Path(name)
        aliases = temporary / "artifacts"
        aliases.mkdir()
        env = pub.aws_environment(temporary, access, secret, args.concurrency)
        while True:
            report = alias_completed(directory, aliases, pub.ARTIFACT)
            print(json.dumps({"phase": "preupload", "repo": args.repo, **report}), flush=True)
            if report["completed_artifacts"]:
                pub.run([aws, "s3", "sync", str(aliases) + "/",
                         f"s3://{pub.BUCKET}/artifacts/{args.repo}/", "--endpoint-url", pub.S3_ENDPOINT,
                         "--size-only", "--no-follow-symlinks", "--exclude", "*", "--include", "*.art",
                         "--content-type", pub.ARTIFACT_CONTENT_TYPE, "--cache-control", pub.IMMUTABLE_CACHE_CONTROL,
                         "--only-show-errors", "--no-progress"],
                        cwd=temporary, env=env, secrets=redactions)
            print(json.dumps({"phase": "preupload-complete", "repo": args.repo, **report}), flush=True)
            if not args.watch:
                return
            time.sleep(args.interval)


if __name__ == "__main__":
    main()
