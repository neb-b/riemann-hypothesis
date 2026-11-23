#!/usr/bin/env python3
"""Generate only C in independent shards, preserving the verified archived oleans.

Every fresh compilation is checked against the frozen archive's constants and
runtime ABI/IR before its C is accepted. Completed C and validation records form
a flat delivery spool which can be copied to the collecting machine.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import runpy
import subprocess
import time


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            h.update(chunk)
    return h.hexdigest()


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix + ".writing")
    temporary.write_text(json.dumps(value, sort_keys=True) + "\n")
    temporary.replace(path)


def ordered_modules(jobs):
    """Match the collector's sorted roots and depth-first import traversal."""
    result, seen = [], set()
    for name in sorted(jobs):
        stack = [(name, False)]
        while stack:
            current, exiting = stack.pop()
            if exiting:
                result.append(current)
                continue
            if current in seen:
                continue
            seen.add(current)
            stack.append((current, True))
            for imp in reversed(jobs[current]["imports"]):
                if imp["module"] in jobs and imp["module"] not in seen:
                    stack.append((imp["module"], False))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    parser.add_argument("--workers", type=int, default=24)
    parser.add_argument("--shard-count", type=int, default=1)
    parser.add_argument("--shards", default="0", help="comma-separated shard indices")
    parser.add_argument("--limit", type=int, help="process only the first N jobs (for a timed preflight)")
    parser.add_argument("--reverse", action="store_true", help="steal work from the far end of another shard")
    parser.add_argument("--only-names", type=Path, help="restrict work to newline-separated module names")
    parser.add_argument("--install", type=Path, help="install a transferred flat delivery spool instead of compiling")
    args = parser.parse_args()
    indices = {int(s) for s in args.shards.split(",")}
    if args.workers < 1 or args.shard_count < 1 or not indices or min(indices) < 0 or max(indices) >= args.shard_count:
        parser.error("invalid worker count or shard indices")
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    resource.setrlimit(resource.RLIMIT_NOFILE, (min(65536, hard), hard))
    root = args.project.resolve()
    helper = Path(__file__).with_name("bootstrap-cache.py")
    common = runpy.run_path(str(helper))
    provenance = common["PUBLISHED_PROVENANCE"]
    if (root / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.1":
        raise SystemExit("the published archive requires stock Lean 4.33.1")
    actual_tree = subprocess.check_output(["git", "rev-parse", "HEAD:src"], cwd=root, text=True).strip()
    if actual_tree != provenance["source_tree"] or digest(root / "lakefile.toml") not in provenance["lakefile_sha256"]:
        raise SystemExit("source/configuration do not match the published archive")
    if digest(root / "lake-manifest.json") != provenance["manifest_sha256"]:
        raise SystemExit("dependency manifest differs from the published archive")
    subprocess.run(["git", "diff", "HEAD", "--exit-code", "--", "src", "lean-toolchain", "lake-manifest.json"], cwd=root, check=True)
    if subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "--", "src"], cwd=root).strip():
        raise SystemExit("untracked source files are unsupported")
    work = root / ".lake/bootstrap"
    if not json.loads((work / "state.json").read_text()).get("normalized"):
        raise SystemExit("first complete bootstrap-cache.py --stop-after normalize")
    jobs = {j["name"]: j for j in common["read_jsonl"](work / "jobs.jsonl")}
    runtime = {r["name"] for report in sorted(work.glob("report-*.jsonl"))
               for r in common["read_jsonl"](report) if r["needsCompile"]}
    records, delivery, temporary, logs = [work / name for name in ("codegen-records", "c-delivery", "codegen-tmp", "codegen-logs")]
    for directory in (records, delivery, temporary, logs):
        directory.mkdir(exist_ok=True)
    tools = root / "scripts/cache-bootstrap"
    check = tools / ".lake/build/bin/check-runtime"
    checker_hash = digest(tools / "CheckRuntime.lean")

    def fingerprint(job):
        value = {"source": digest(job["source"]), "olean": digest(job["olean"]),
                 "setup": job["setup"], "args": job["leanArgs"], "checker": checker_hash,
                 "manifest": provenance["manifest_sha256"], "toolchain": "leanprover/lean4:v4.33.1"}
        return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()

    def install(record, c_file):
        name = record["name"]
        expected_id = hashlib.sha256(name.encode()).hexdigest()[:24]
        if record.get("id") != expected_id or not re.fullmatch(r"[0-9a-f]{24}", expected_id):
            raise ValueError("delivery has an invalid module identifier")
        if name not in runtime or record["fingerprint"] != fingerprint(jobs[name]):
            raise ValueError(f"delivery does not match frozen inputs: {name}")
        if digest(c_file) != record["cSha256"]:
            raise ValueError(f"delivery C checksum mismatch: {name}")
        destination = Path(jobs[name]["c"])
        prior_path = records / (expected_id + ".json")
        if prior_path.exists():
            prior = json.loads(prior_path.read_text())
            if prior.get("fingerprint") == record["fingerprint"]:
                if destination.exists() and digest(destination) == prior.get("cSha256"):
                    # Never replace validated C after the indexer may have hashed it.
                    return
                if prior.get("cSha256") != record["cSha256"]:
                    raise ValueError(f"cannot replace missing validated C with another variant: {name}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        linked = destination.with_suffix(".c.installing")
        linked.unlink(missing_ok=True)
        os.link(c_file, linked)
        linked.replace(destination)
        atomic_json(records / (record["id"] + ".json"), record)

    if args.install:
        count = 0
        for record_file in args.install.glob("*.json"):
            record = json.loads(record_file.read_text())
            existing = records / record_file.name
            if existing.exists():
                prior = json.loads(existing.read_text())
                destination = Path(jobs[record["name"]]["c"])
                if prior.get("fingerprint") == record.get("fingerprint") and destination.exists() and digest(destination) == prior.get("cSha256"):
                    continue
            c_file = args.install / (record["id"] + ".c")
            if not c_file.exists():
                continue
            install(record, c_file)
            count += 1
        print(f"installed {count} validated C files", flush=True)
        return

    subprocess.run(["lake", "-d", str(tools), "build", "check-runtime"], cwd=root, check=True)
    lean = Path(subprocess.check_output(["elan", "which", "lean"], cwd=root, text=True).strip())
    if subprocess.check_output([str(lean), "--githash"], cwd=root, text=True).strip() != "819816b2e0a3bf405af45ae5c7af2491d8f5bee6":
        raise SystemExit("the compiler does not match the stock Lean 4.33.1 release")
    toolchain = lean.parent.parent
    original_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=root, text=True).strip()
    # Most dependency lookups are Mathlib. Put it immediately after the project.
    paths = original_path.split(os.pathsep)
    paths.sort(key=lambda p: (0 if p == str(root / ".lake/build/lib/lean") else 1 if "/mathlib/" in p else 2))
    lean_path = os.pathsep.join(paths)
    env = {"PATH": os.environ["PATH"], "HOME": "/tmp", "LEAN_PATH": lean_path,
           "LEAN_NUM_THREADS": "1", "LEAN_ABORT_ON_PANIC": "1"}
    prefix = ["bwrap", "--die-with-parent", "--unshare-all", "--ro-bind", "/", "/",
              "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/tmp", "--tmpfs", "/opt",
              "--dev", "/dev", "--proc", "/proc", "--ro-bind", str(root), str(root),
              "--ro-bind", str(toolchain), "/opt/lean",
              "--chdir", str(root), "--setenv", "PATH", "/opt/lean/bin:/usr/bin:/bin",
              "--setenv", "LEAN_SYSROOT", "/opt/lean", "--setenv", "LD_LIBRARY_PATH", "/opt/lean/lib/lean:/opt/lean/lib"]
    ordered = [name for name in ordered_modules(jobs) if name in runtime]
    todo = [name for i, name in enumerate(ordered) if i % args.shard_count in indices]
    if args.only_names:
        selected = set(args.only_names.read_text().splitlines())
        if not selected <= runtime:
            raise SystemExit("--only-names includes a module outside the runtime set")
        todo = [name for name in todo if name in selected]
    if args.reverse:
        todo.reverse()
    if args.limit is not None:
        todo = todo[:args.limit]
    started = time.monotonic()
    print(f"shards {sorted(indices)}/{args.shard_count}: {len(todo)} of {len(runtime)} modules, {args.workers} workers", flush=True)

    def compile_one(name):
        job = jobs[name]
        identifier = hashlib.sha256(name.encode()).hexdigest()[:24]
        record_path = records / (identifier + ".json")
        key = fingerprint(job)
        if record_path.exists():
            record = json.loads(record_path.read_text())
            if record.get("fingerprint") == key and Path(job["c"]).exists() and digest(job["c"]) == record.get("cSha256"):
                return "reused"
        scratch = temporary / identifier
        scratch.mkdir(exist_ok=True)
        setup = scratch / "setup.json"
        fresh = scratch / "module.olean"
        ilean = scratch / "module.ilean"
        c_file = scratch / "module.c"
        report = scratch / "check.json"
        sandbox = [*prefix, "--bind", str(scratch), str(scratch)]
        setup.write_text(json.dumps(job["setup"]))
        before = time.monotonic()
        with (logs / (identifier + ".log")).open("wb") as log:
            # The shell defaults to hardware_concurrency even when LEAN_NUM_THREADS
            # is set. Bound it explicitly to avoid nested pools in every worker.
            subprocess.run([*sandbox, "/opt/lean/bin/lean", "-j1", *job["leanArgs"], job["source"],
                            "-o", str(fresh), "-i", str(ilean), "-c", str(c_file),
                            "--setup", str(setup), "--json"], cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
            subprocess.run([*sandbox, str(check), job["olean"], str(fresh), str(report)],
                           cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        # Both comparisons must succeed before making C visible to the collector.
        if fingerprint(job) != key:
            raise ValueError(f"frozen input changed during compilation: {name}")
        record = {"name": name, "id": identifier, "fingerprint": key,
                  "cSha256": digest(c_file), "seconds": time.monotonic() - before,
                  "validation": json.loads(report.read_text())}
        final_delivery = delivery / (identifier + ".c")
        c_file.replace(final_delivery)
        atomic_json(delivery / (identifier + ".json"), record)
        install(record, final_delivery)
        for path in (fresh, ilean, report, setup):
            path.unlink(missing_ok=True)
        try:
            scratch.rmdir()
        except OSError:
            pass
        return "generated"

    errors = []
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(compile_one, name): name for name in todo}
        for number, future in enumerate(as_completed(futures), 1):
            if future.cancelled():
                continue
            try:
                future.result()
            except Exception as error:
                errors.append((futures[future], str(error)))
                print(f"FAILED {futures[future]}: {error}", flush=True)
                if len(errors) >= 5:
                    for queued in futures:
                        queued.cancel()
            if number % 50 == 0 or number == len(todo):
                elapsed = time.monotonic() - started
                print(f"completed {number}/{len(todo)}; {len(errors)} failures; elapsed {elapsed:.1f}s", flush=True)
    if errors:
        atomic_json(work / "codegen-errors.json", errors)
        raise SystemExit(f"{len(errors)} modules failed; see codegen-errors.json and codegen-logs")


if __name__ == "__main__":
    main()
