#!/usr/bin/env python3
"""Turn verified published legacy oleans into a complete, stock Lake cache.

First run fetch-published-cache.py. This program contains no Cloudflare credential
handling. Native-code modules compile in an offline bubblewrap sandbox; theorem-only
modules reuse the archive's proofs. All stages are resumable for a fixed source/tool
state, and the final staging tree contains compressed Lake archives only.
"""
from __future__ import annotations

import argparse
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys

PUBLISHED_PROVENANCE = {
    "source_path": "src",
    "source_tree": "24df20b62d9976ccd20da819bc20b16f808f0fdd",
    "lakefile_sha256": [
        "a1b98b41c96ad1e78906a210f5c6806218bda1701356215983033b2f77d44c99",
        "32af981ad33964a949f3e4d1e188e4afd0f85fecf6bf86e8ed133f00f16727ca",
        "e4686772edd6823c948d7cd6b0dbcf6168e1bfcce9d1e6713f884f646ce4bd0b",
    ],
    "manifest_sha256": "fee57ee9ed399d0a638ca955e5ad40a37a36eeb9b6dfd9f5964114fa7bbe4774",
}


def run(command, *, cwd, env=None, log=None):
    print("+", " ".join(map(str, command)), flush=True)
    if log:
        with open(log, "wb") as stream:
            subprocess.run(command, cwd=cwd, env=env, stdout=stream,
                           stderr=subprocess.STDOUT, check=True)
    else:
        subprocess.run(command, cwd=cwd, env=env, check=True)


def read_jsonl(path):
    with open(path) as stream:
        return [json.loads(line) for line in stream if line.strip()]


def prepare_pack_stack():
    # Stock leantar recursively compresses olean objects. Some published proofs
    # exceed an 8 MiB stack; raise only this producer's soft limit, inherited by
    # its children, without changing the hard limit or any system settings.
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    if soft != hard:
        resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    parser.add_argument("--tools", type=Path, default=Path(__file__).parent / "cache-bootstrap")
    parser.add_argument("--workers", type=int, default=min(os.cpu_count() or 1, 16))
    parser.add_argument("--stop-after", choices=["plan", "normalize", "compile", "index", "pack"])
    parser.add_argument("--provenance", type=Path,
                        help="explicit source attestation for a separately validated archive (used by fixture tests)")
    parser.add_argument("--rebuild-c", action="store_true", help="rebuild runtime C rather than use pinned published extras")
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    root, tools = args.project.resolve(), args.tools.resolve()
    work = root / ".lake/bootstrap"
    work.mkdir(parents=True, exist_ok=True)
    cache = root / ".lake/cache"
    env = os.environ.copy()
    # Do not allow a build to inherit an upload credential.
    for key in list(env):
        if key.startswith(("AWS_", "CLOUDFLARE_")) or key == "LAKE_CACHE_KEY":
            env.pop(key)
    env.update(LAKE_CACHE_DIR=str(cache), LAKE_ARTIFACT_CACHE="false",
               LEAN_ABORT_ON_PANIC="1", LEAN_NUM_THREADS="1")
    lean = Path(subprocess.check_output(["elan", "which", "lean"], cwd=root,
                                        env=env, text=True).strip())
    toolchain = lean.parent.parent
    if (root / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.1":
        raise SystemExit("this bootstrap supports the published Lean 4.33.1 archive only")
    env.update(LEAN_SYSROOT=str(toolchain), LAKE_HOME=str(toolchain))
    if not shutil.which("bwrap"):
        raise SystemExit("bubblewrap is required for computational-module compilation")
    provenance = json.loads(args.provenance.read_text()) if args.provenance else PUBLISHED_PROVENANCE
    source_path = provenance["source_path"]
    source_ref = "HEAD^{tree}" if source_path == "." else f"HEAD:{source_path}"
    actual_tree = subprocess.check_output(["git", "rev-parse", source_ref], cwd=root, text=True).strip()
    if actual_tree != provenance["source_tree"]:
        raise SystemExit("source tree differs from the published archive; build changed proofs from source")
    if hashlib.sha256((root / "lakefile.toml").read_bytes()).hexdigest() not in provenance["lakefile_sha256"]:
        raise SystemExit("Lake configuration differs from the published compilation options")
    if hashlib.sha256((root / "lake-manifest.json").read_bytes()).hexdigest() != provenance["manifest_sha256"]:
        raise SystemExit("dependency manifest differs from the published archive")
    run(["git", "diff", "HEAD", "--exit-code", "--", source_path, "lean-toolchain", "lake-manifest.json"], cwd=root)
    untracked = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "--", source_path], cwd=root)
    if untracked.strip():
        raise SystemExit("untracked source files must be committed before cache bootstrap")
    fingerprint = hashlib.sha256()
    fingerprint.update(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root))
    fingerprint.update((root / "lakefile.toml").read_bytes())
    fingerprint.update(str(args.workers).encode())
    fingerprint.update(json.dumps(provenance, sort_keys=True).encode())
    for path in [Path(__file__), *sorted(tools.glob("*.lean")), tools / "lakefile.toml"]:
        fingerprint.update(path.read_bytes())
    identity = fingerprint.hexdigest()
    state_path = work / "state.json"
    state = json.loads(state_path.read_text()) if state_path.exists() else {}
    if state.get("identity") != identity:
        state = {"identity": identity}

    def completed(phase):
        state[phase] = True
        temporary = state_path.with_suffix(".tmp")
        temporary.write_text(json.dumps(state, indent=2) + "\n")
        temporary.replace(state_path)

    run(["lake", "-d", str(tools), "build", "trace-cache", "normalize-cache", "check-runtime", "hash-outputs", "attest-extras"], cwd=root, env=env)
    trace = tools / ".lake/build/bin/trace-cache"
    normalizer = tools / ".lake/build/bin/normalize-cache"
    jobs_file = work / "jobs.jsonl"
    if not state.get("planned"):
        run([str(trace), "plan", str(root), str(jobs_file)], cwd=root, env=env)
        completed("planned")
    if args.stop_after == "plan":
        return
    jobs = read_jsonl(jobs_file)
    by_name = {job["name"]: job for job in jobs}
    if len(by_name) != len(jobs):
        raise SystemExit("duplicate module in plan")
    missing = [j["name"] for j in jobs if not Path(j["olean"]).is_file()
               or not Path(j["ilean"]).is_file()]
    if missing:
        raise SystemExit(f"published archive has not been fully restored: {missing[:5]}")
    shards = [[] for _ in range(args.workers)]
    for i, job in enumerate(jobs):
        shards[i % args.workers].append(job)
    shard_files = []
    for i, shard in enumerate(shards):
        path = work / f"jobs-{i:03}.jsonl"
        path.write_text("".join(json.dumps(j, separators=(",", ":")) + "\n" for j in shard))
        shard_files.append(path)
    if not state.get("normalized"):
        def normalize(item):
            i, path = item
            run([str(normalizer), "--jobs", str(path), "--report", str(work / f"report-{i:03}.jsonl")],
                cwd=root, env=env, log=work / f"normalize-{i:03}.log")
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            list(pool.map(normalize, enumerate(shard_files)))
        completed("normalized")
    if args.stop_after == "normalize":
        return
    reports = [item for i in range(args.workers)
               for item in read_jsonl(work / f"report-{i:03}.jsonl")]
    computational = {item["name"] for item in reports if item["needsCompile"]}
    if len(reports) != len(jobs):
        raise SystemExit("normalizer report is incomplete")
    print(f"{len(jobs)} modules; only {len(computational)} contain compiled code", flush=True)
    if not state.get("compiled") and not args.rebuild_c and args.provenance is None:
        # Newer published C belongs to another build of the same source. Certify
        # exact bytes, or a difference confined to diagnostic filenames, first.
        run([sys.executable, str(Path(__file__).with_name("fetch-published-extras.py")),
             "--project", str(root)], cwd=root, env=env)
        extras = root / ".lake/published-extras"
        attestation = extras / "runtime-attestation.jsonl"
        result = subprocess.run([str(tools / ".lake/build/bin/attest-extras"),
                                 str(extras / "runtime-attest-jobs.jsonl"), str(attestation)], cwd=root, env=env)
        rows = read_jsonl(attestation)
        if result.returncode not in (0, 1) or {r["name"] for r in rows} != computational:
            raise SystemExit("published extras attestation did not complete")
        run([sys.executable, str(Path(__file__).with_name("accept-published-c.py")),
             "--project", str(root)], cwd=root, env=env)
        remaining = [r["name"] for r in rows if not r.get("compatible")]
        if remaining:
            fallback = work / "extras-source-fallback.txt"
            fallback.write_text("".join(name + "\n" for name in remaining))
            run([sys.executable, str(Path(__file__).with_name("codegen-cache.py")),
                 "--project", str(root), "--workers", str(min(args.workers, 8)),
                 "--only-names", str(fallback)], cwd=root, env=env)
        if any(not Path(jobs_by_name["c"]).is_file() for jobs_by_name in jobs if jobs_by_name["name"] in computational):
            raise SystemExit("some runtime C is still missing")
        completed("compiled")
    if not state.get("compiled"):
        lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                           cwd=root, env=env, text=True).strip()
        setups = work / "setups"
        logs = work / "compile-logs"
        setups.mkdir(exist_ok=True)
        logs.mkdir(exist_ok=True)
        sandbox_env = {"HOME": "/tmp", "PATH": "/opt/lean/bin:/usr/bin:/bin",
                       "LEAN_PATH": lean_path, "LEAN_NUM_THREADS": "1",
                       "LEAN_ABORT_ON_PANIC": "1"}

        def compile_module(name):
            job = by_name[name]
            setup = setups / (name + ".json")
            setup.write_text(json.dumps(job["setup"]))
            outputs = {key: Path(job[key] + ".compiling") for key in ("olean", "ilean", "c")}
            for path in outputs.values():
                path.parent.mkdir(parents=True, exist_ok=True)
            command = ["bwrap", "--die-with-parent", "--unshare-all", "--ro-bind", "/", "/",
                       "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/tmp", "--tmpfs", "/opt",
                       "--dev", "/dev", "--proc", "/proc",
                       "--ro-bind", str(root), str(root),
                       "--bind", str(root / ".lake/build"), str(root / ".lake/build"),
                       "--bind", str(work), str(work),
                       "--ro-bind", str(toolchain), "/opt/lean",
                       "--chdir", str(root), "/opt/lean/bin/lean", "-j1", *job["leanArgs"], job["source"],
                       "-o", str(outputs["olean"]), "-i", str(outputs["ilean"]),
                       "-c", str(outputs["c"]), "--setup", str(setup), "--json"]
            # Keep the host PATH for bwrap; only the child receives the clean sandbox env.
            host_env = {"PATH": env.get("PATH", "/usr/bin:/bin"), **sandbox_env}
            host_env["PATH"] = env.get("PATH", "/usr/bin:/bin")
            command[command.index("/opt/lean/bin/lean"):command.index("/opt/lean/bin/lean")] = [
                "--setenv", "PATH", sandbox_env["PATH"]]
            try:
                with (logs / (name + ".log")).open("wb") as log:
                    subprocess.run(command, cwd=root, env=host_env, stdout=log,
                                   stderr=subprocess.STDOUT, check=True)
                for key, path in outputs.items():
                    path.replace(job[key])
            except subprocess.CalledProcessError as error:
                raise RuntimeError(f"{name} failed; see {logs / (name + '.log')}") from error

        dependencies = {name: {i["module"] for i in job["imports"] if i["module"] in by_name}
                        for name, job in by_name.items()}
        remaining = {name: len(deps) for name, deps in dependencies.items()}
        children = {name: [] for name in by_name}
        for name, deps in dependencies.items():
            for dep in deps:
                children[dep].append(name)
        ready = deque(name for name, n in remaining.items() if n == 0)
        done = 0
        compiled = 0

        def finish(name):
            nonlocal done
            done += 1
            for child in children[name]:
                remaining[child] -= 1
                if remaining[child] == 0:
                    ready.append(child)

        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            pending = {}
            while ready or pending:
                while ready and len(pending) < args.workers:
                    name = ready.popleft()
                    if name in computational:
                        pending[pool.submit(compile_module, name)] = name
                    else:
                        finish(name)
                if pending:
                    finished, _ = wait(pending, return_when=FIRST_COMPLETED)
                    for future in finished:
                        name = pending.pop(future)
                        future.result()
                        finish(name)
                        compiled += 1
                        if compiled % 100 == 0 or compiled == len(computational):
                            print(f"compiled {compiled}/{len(computational)} computational modules", flush=True)
        if done != len(jobs):
            raise SystemExit("cyclic or incomplete import graph")
        run(["git", "diff", "HEAD", "--exit-code", "--", source_path, "lean-toolchain", "lake-manifest.json"], cwd=root)
        completed("compiled")
    if args.stop_after == "compile":
        return
    if not state.get("indexed"):
        run([str(trace), "index", str(root), str(work / "raw-outputs.jsonl")],
            cwd=root, env=env, log=work / "index.log")
        completed("indexed")
    if args.stop_after == "index":
        return
    if not state.get("packed"):
        prepare_pack_stack()
        def pack(item):
            i, path = item
            run([str(trace), "pack", str(root), str(path), str(work / f"outputs-{i:03}.jsonl")],
                cwd=root, env=env, log=work / f"pack-{i:03}.log")
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            list(pool.map(pack, enumerate(shard_files)))
        completed("packed")
    if args.stop_after == "pack":
        return
    staging = root / ".lake/cache-staging"
    staging.mkdir(exist_ok=True)
    mappings = {}
    header = None
    for i in range(args.workers):
        entries = read_jsonl(work / f"outputs-{i:03}.jsonl")
        if header is not None and entries[0] != header:
            raise SystemExit("inconsistent mapping schema")
        header = entries[0]
        for input_hash, artifact in entries[1:]:
            if input_hash in mappings and mappings[input_hash] != artifact:
                raise SystemExit("conflicting output mappings")
            mappings[input_hash] = artifact
    if len(mappings) != len(jobs):
        raise SystemExit("incomplete packed output map")
    for artifact in set(mappings.values()):
        if not isinstance(artifact, str) or "/" in artifact or not artifact.endswith(".ltar"):
            raise SystemExit("expected flat Lake archive names")
        destination = staging / artifact
        if not destination.exists():
            os.link(cache / "artifacts" / artifact, destination)
    with (staging / "outputs.jsonl").open("w") as stream:
        stream.write(json.dumps(header) + "\n")
        for pair in sorted(mappings.items()):
            stream.write(json.dumps(pair, separators=(",", ":")) + "\n")
    completed("staged")
    print(f"Ready: {len(mappings)} compressed artifacts in {staging}", flush=True)


if __name__ == "__main__":
    main()
