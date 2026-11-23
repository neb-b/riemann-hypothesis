#!/usr/bin/env python3
"""Exercise bootstrap against stock Lake, including dependency invalidation.

Build trace-cache, normalize-cache, check-runtime, hash-outputs, and attest-extras
with `lake -d scripts/cache-bootstrap build <targets>` before running this file.
No network, large repository build, or published artifact download is required.
"""

import argparse
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import runpy
import resource
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch


def run(command, *, cwd, env, succeeds=True):
    result = subprocess.run(
        [str(arg) for arg in command], cwd=cwd, env=env,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if (result.returncode == 0) != succeeds:
        raise AssertionError(
            f"unexpected exit {result.returncode}: {' '.join(map(str, command))}\n"
            f"{result.stdout}"
        )
    return result.stdout


def write(path, contents):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents)


def topological(jobs):
    by_name = {job["name"]: job for job in jobs}
    seen, ordered = set(), []

    def visit(name):
        if name in seen:
            return
        seen.add(name)
        job = by_name[name]
        for imp in job["imports"]:
            if imp["module"] in by_name:
                visit(imp["module"])
        ordered.append(job)

    for name in by_name:
        visit(name)
    return ordered


def integration(trace, normalize, temporary, platform_independent=None):
    temporary.mkdir(parents=True, exist_ok=True)
    root = temporary / "project"
    dependency = temporary / "dependency"
    root.mkdir()
    dependency.mkdir()
    toolchain = (Path(__file__).parent / "lean-toolchain").read_text()
    for directory in (root, dependency):
        write(directory / "lean-toolchain", toolchain)
    write(dependency / "lakefile.toml", '''name = "external"
defaultTargets = ["External"]
[[lean_lib]]
name = "External"
''')
    write(dependency / "External.lean", "theorem externalFact : True := True.intro\n")
    config = '''name = "bootstrapTest"
defaultTargets = ["Probe"]
moreLeanArgs = ["--tstack=400000"]
[leanOptions]
autoImplicit = false
maxHeartbeats = 100000
pp.unicode.fun = true
[[require]]
name = "external"
path = "../dependency"
[[lean_lib]]
name = "Probe"
globs = ["Probe.*"]
'''
    if platform_independent is not None:
        config = config.replace(
            'name = "bootstrapTest"\n',
            'name = "bootstrapTest"\n'
            f'platformIndependent = {str(platform_independent).lower()}\n',
            1,
        )
    write(root / "lakefile.toml", config)
    sources = {
        "Probe/Base.lean": "import External\nnamespace Probe\ntheorem base : True := externalFact\nend Probe\n",
        "Probe/Bridge.lean": "import Probe.Base\nnamespace Probe\ntheorem bridge : True := base\nend Probe\n",
        "Probe.lean": "import Probe.Bridge\ntheorem finalFact : True := Probe.bridge\n",
    }
    for relative, content in sources.items():
        write(root / relative, content)
    env = dict(os.environ, LAKE_CACHE_DIR=str(temporary / "cache"), LAKE_ARTIFACT_CACHE="false")
    # Avoid inherited project-specific service settings affecting this isolated test.
    for key in tuple(env):
        if key.startswith("LAKE_CACHE_") and key != "LAKE_CACHE_DIR":
            del env[key]
    run(["lake", "build"], cwd=root, env=env)
    jobs_file = temporary / "jobs.jsonl"
    run(["lake", "env", trace, "plan", root, jobs_file], cwd=root, env=env)
    jobs = [json.loads(line) for line in jobs_file.read_text().splitlines()]
    assert {j["name"] for j in jobs} == {"Probe", "Probe.Base", "Probe.Bridge"}
    base = next(j for j in jobs if j["name"] == "Probe.Base")
    assert next(i for i in base["imports"] if i["module"] == "External")["package"] == "external"
    expected = {
        job["name"]: {
            "trace": json.loads(Path(job["trace"]).read_text()),
            "olean": Path(job["olean"]).read_bytes(),
            "ilean": Path(job["ilean"]).read_bytes(),
            "c": Path(job["c"]).read_bytes(),
        }
        for job in jobs
    }

    # Reproduce the published archive's omission of package metadata and C/traces.
    # These tiny proofs are elaborated only to manufacture a self-contained test fixture.
    for job in topological(jobs):
        setup = dict(job["setup"])
        setup.pop("package", None)
        setup_path = temporary / f'{job["name"]}.setup.json'
        setup_path.write_text(json.dumps(setup))
        run([
            "lake", "env", "lean", *job["leanArgs"], job["source"],
            "-o", job["olean"], "-i", job["ilean"], "--setup", setup_path,
        ], cwd=root, env=env)
        for key in ("trace", "c"):
            Path(job[key]).unlink()
        for key in ("olean", "ilean", "c"):
            Path(job[key] + ".hash").unlink(missing_ok=True)

    report_path = temporary / "report.jsonl"
    run([normalize, "--jobs", jobs_file, "--report", report_path], cwd=root, env=env)
    report = [json.loads(line) for line in report_path.read_text().splitlines()]
    assert len(report) == len(jobs)
    assert all(row["normalized"] and not row["needsCompile"] for row in report)
    for job in jobs:
        for key in ("olean", "ilean", "c"):
            assert Path(job[key]).read_bytes() == expected[job["name"]][key], (job["name"], key)

    env["LAKE_ARTIFACT_CACHE"] = "true"
    mappings = temporary / "outputs.jsonl"
    run(["lake", "env", trace, "index", root, mappings], cwd=root, env=env)
    assert len(mappings.read_text().splitlines()) == len(jobs) + 1
    for job in jobs:
        actual = json.loads(Path(job["trace"]).read_text())
        original = expected[job["name"]]["trace"]
        assert actual["synthetic"] is True
        assert actual["depHash"] == original["depHash"], (job["name"], actual, original)
        assert actual["outputs"] == original["outputs"], job["name"]
    run(["lake", "--no-build", "--rehash", "build"], cwd=root, env=env)

    # A consumer can restore everything from the local artifact cache, without Lean builds.
    shutil.rmtree(root / ".lake/build")
    run(["lake", "--no-build", "--rehash", "build"], cwd=root, env=env)

    imported = root / "Probe/Base.lean"
    imported.write_text(imported.read_text() + "\n-- changed imported source\n")
    run(["lake", "--no-build", "--rehash", "build"], cwd=root, env=env, succeeds=False)
    imported.write_text(sources["Probe/Base.lean"])
    run(["lake", "--no-build", "--rehash", "build"], cwd=root, env=env)
    (root / "lakefile.toml").write_text(config.replace("maxHeartbeats = 100000", "maxHeartbeats = 200000"))
    run(["lake", "--no-build", "--rehash", "build"], cwd=root, env=env, succeeds=False)
    print(f"PASS (platformIndependent={platform_independent}): normalized outputs match stock Lake; regenerated traces match; cache restores; source and option changes invalidate")


def orchestration(tools, temporary):
    """Exercise the actual scheduler, offline compiler, packer, and archive consumer."""
    temporary.mkdir(parents=True, exist_ok=True)
    root = temporary / "project"
    root.mkdir()
    toolchain = (Path(__file__).parent / "lean-toolchain").read_text()
    write(root / "lean-toolchain", toolchain)
    write(root / ".gitignore", ".lake/\n")
    write(root / "lakefile.toml", '''name = "pipelineTest"
srcDir = "src"
defaultTargets = ["Probe"]
platformIndependent = true
[leanOptions]
autoImplicit = false
maxHeartbeats = 100000
[[lean_lib]]
name = "Probe"
globs = ["Probe.*"]
''')
    sources = {
        "Probe/Base.lean": "namespace Probe\ntheorem base : True := True.intro\nend Probe\n",
        "Probe/Computer.lean": "import Probe.Base\nnamespace Probe\ndef value : Nat := 7\nend Probe\n",
        "Probe/MoreComputer.lean": "import Probe.Computer\nnamespace Probe\ndef next : Nat := value + 1\nend Probe\n",
        "Probe.lean": "import Probe.MoreComputer\ntheorem result : Probe.next = 8 := rfl\n",
    }
    for relative, content in sources.items():
        write(root / "src" / relative, content)
    env = dict(os.environ, LAKE_ARTIFACT_CACHE="false")
    for key in tuple(env):
        if key.startswith("LAKE_CACHE_"):
            del env[key]
    run(["lake", "build"], cwd=root, env=env)
    # The producer requires immutable, tracked inputs and fingerprints HEAD.
    run(["git", "init", "-q"], cwd=root, env=env)
    run(["git", "add", "src", "lean-toolchain", "lakefile.toml", "lake-manifest.json", ".gitignore"], cwd=root, env=env)
    run(["git", "-c", "user.name=Cache test", "-c", "user.email=cache-test@example.invalid",
         "commit", "-qm", "test fixture"], cwd=root, env=env)
    provenance = temporary / "provenance.json"
    provenance.write_text(json.dumps({
        "source_path": "src",
        "source_tree": run(["git", "rev-parse", "HEAD:src"], cwd=root, env=env).strip(),
        "lakefile_sha256": [hashlib.sha256((root / "lakefile.toml").read_bytes()).hexdigest()],
        "manifest_sha256": hashlib.sha256((root / "lake-manifest.json").read_bytes()).hexdigest(),
    }))
    jobs_file = temporary / "original-jobs.jsonl"
    run(["lake", "env", tools / ".lake/build/bin/trace-cache", "plan", root, jobs_file], cwd=root, env=env)
    jobs = [json.loads(line) for line in jobs_file.read_text().splitlines()]
    assert len(jobs) == 4
    original = {job["name"]: {
        key: Path(job[key]).read_bytes() for key in ("olean", "ilean", "c")
    } for job in jobs}
    original_hashes = {job["name"]: json.loads(Path(job["trace"]).read_text())["depHash"] for job in jobs}
    for job in topological(jobs):
        setup = dict(job["setup"])
        setup.pop("package", None)
        setup_file = temporary / f'{job["name"]}.json'
        setup_file.write_text(json.dumps(setup))
        run(["lake", "env", "lean", *job["leanArgs"], job["source"],
             "-o", job["olean"], "-i", job["ilean"], "--setup", setup_file], cwd=root, env=env)
        for key in ("trace", "c"):
            Path(job[key]).unlink()
        for key in ("olean", "ilean", "c"):
            Path(job[key] + ".hash").unlink(missing_ok=True)

    producer = Path(__file__).resolve().parents[1] / "bootstrap-cache.py"
    command = ["python3", producer, "--project", root, "--tools", tools,
               "--provenance", provenance, "--workers", "2"]
    run(command, cwd=root, env=env)
    report = [item for file in (root / ".lake/bootstrap").glob("report-*.jsonl")
              for item in map(json.loads, file.read_text().splitlines())]
    assert {row["name"] for row in report if row["needsCompile"]} == {
        "Probe.Computer", "Probe.MoreComputer",
    }
    for job in jobs:
        for key in ("olean", "ilean", "c"):
            assert Path(job[key]).read_bytes() == original[job["name"]][key], (job["name"], key)
        actual_hash = json.loads(Path(job["trace"]).read_text())["depHash"]
        assert actual_hash == original_hashes[job["name"]], job["name"]
    staging = root / ".lake/cache-staging"
    staging_names = {file.name for file in staging.iterdir()}
    assert "outputs.jsonl" in staging_names
    assert all(name == "outputs.jsonl" or name.endswith(".ltar") for name in staging_names)
    assert len(staging_names) == len(jobs) + 1

    # A second run resumes to the identical staging map without compiling again.
    mapping = (staging / "outputs.jsonl").read_bytes()
    compile_logs = {file.name: file.stat().st_mtime_ns
                    for file in (root / ".lake/bootstrap/compile-logs").glob("*.log")}
    run(command, cwd=root, env=env)
    assert mapping == (staging / "outputs.jsonl").read_bytes()
    assert compile_logs == {file.name: file.stat().st_mtime_ns
                            for file in (root / ".lake/bootstrap/compile-logs").glob("*.log")}
    # Changing parallelism changes the shard layout. A clean identity reset must
    # replace prior read-only/hard-linked outputs without corrupting the cache.
    run([*command[:-1], "3"], cwd=root, env=env)
    assert mapping == (staging / "outputs.jsonl").read_bytes()

    # Eliminate the producer's uncompressed cache and build outputs. Restore from
    # only the exact flat archive staging tree that will be published to R2.
    shutil.rmtree(root / ".lake/cache")
    shutil.rmtree(root / ".lake/build")
    env.update(LAKE_CACHE_DIR=str(root / ".lake/cache"), LAKE_ARTIFACT_CACHE="true")
    run(["lake", "cache", "unstage", staging], cwd=root, env=env)
    assert all(file.name.endswith(".ltar") for file in (root / ".lake/cache/artifacts").iterdir())
    run(["lake", "--no-build", "--rehash", "build"], cwd=root, env=env)
    for job in jobs:
        for key in ("olean", "ilean", "c"):
            assert Path(job[key]).read_bytes() == original[job["name"]][key], (job["name"], key)
    changed = root / "src/Probe/Base.lean"
    changed.write_text(changed.read_text() + "\n-- different committed source\n")
    run(["git", "add", "src"], cwd=root, env=env)
    run(["git", "-c", "user.name=Cache test", "-c", "user.email=cache-test@example.invalid",
         "commit", "-qm", "change submitted source"], cwd=root, env=env)
    rejection = run(command, cwd=root, env=env, succeeds=False)
    assert "source tree differs" in rejection
    print("PASS pipeline: computational dependencies compile offline in order; resume skips work; .ltar-only cache restores with stock Lake")


def guard_fixtures(tools, temporary):
    """Check native compatibility, lint-only attestation, and acceptance invariants."""
    temporary.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LAKE_ARTIFACT_CACHE="false")
    config = 'name = "guardFixture"\nsrcDir = "src"\ndefaultTargets = ["Subject"]\n[[lean_lib]]\nname = "Subject"\n'
    source = '''import Lean
namespace Subject
variable {α : Type} [Inhabited α]
theorem warning (x : α) : x = x := rfl
def bump (n : Nat) : Nat := n + 1
initialize counter : IO.Ref Nat ← IO.mkRef 3
end Subject
'''
    roots = [temporary / name for name in ("original", "rebuilt")]
    for root in roots:
        write(root / "lakefile.toml", config)
        write(root / "lean-toolchain", (tools / "lean-toolchain").read_text())
        write(root / "src/Subject.lean", source)
        write(root / ".gitignore", ".lake/\n")
        run(["lake", "build"], cwd=root, env=env)
    root, rebuilt = roots
    old = root / ".lake/build/lib/lean/Subject.olean"
    remote = temporary / "external.olean"
    shutil.copyfile(rebuilt / ".lake/build/lib/lean/Subject.olean", remote)
    frozen_sha = hashlib.sha256(old.read_bytes()).hexdigest()
    check = tools / ".lake/build/bin/check-runtime"
    attest = tools / ".lake/build/bin/attest-extras"
    hasher = tools / ".lake/build/bin/hash-outputs"
    run([check, old, remote], cwd=root, env=env)

    hash_jobs = temporary / "hash-jobs.jsonl"
    hash_jobs.write_text("".join(json.dumps({"name": name, "file": str(file), "expected": "0" * 16}) + "\n"
                                 for name, file in (("old", old), ("remote", remote))))
    hash_report = temporary / "hash-report.jsonl"
    run([hasher, hash_jobs, hash_report], cwd=root, env=env)
    hashes = {row["name"]: row["actual"] for row in map(json.loads, hash_report.read_text().splitlines())}
    assert hashes["old"] != hashes["remote"], "fixture must contain location-dependent lint metadata"
    attest_jobs, attest_report = temporary / "attest-jobs.jsonl", temporary / "attest-report.jsonl"
    base = {"name": "Subject", "olean": str(old)}
    attest_jobs.write_text(json.dumps({**base, "expected": hashes["old"]}) + "\n")
    run([attest, attest_jobs, attest_report, temporary], cwd=root, env=env)
    assert json.loads(attest_report.read_text())["mode"] == "exact"
    lint_job = {**base, "expected": hashes["remote"], "source": str(rebuilt / "src/Subject.lean")}
    attest_jobs.write_text(json.dumps(lint_job) + "\n")
    run([attest, attest_jobs, attest_report, temporary], cwd=root, env=env)
    lint_certificate = json.loads(attest_report.read_text())
    assert lint_certificate["mode"] == "lint-only" and lint_certificate["compatible"]
    assert hashlib.sha256(old.read_bytes()).hexdigest() == frozen_sha
    attest_jobs.write_text(json.dumps({**lint_job, "expected": "0" * 16}) + "\n")
    run([attest, attest_jobs, attest_report, temporary], cwd=root, env=env, succeeds=False)
    assert json.loads(attest_report.read_text())["mode"] == "mismatch"
    write(rebuilt / "src/Subject.lean", source.replace("n + 1", "n + 2"))
    run(["lake", "build"], cwd=rebuilt, env=env)
    run([check, old, rebuilt / ".lake/build/lib/lean/Subject.olean"], cwd=root, env=env, succeeds=False)

    # Use small explicitly trusted fixture manifests instead of downloading the
    # public archives; execute the real acceptance logic and native rehash tool.
    run(["git", "init", "-q"], cwd=root, env=env)
    run(["git", "add", "src", "lakefile.toml", "lean-toolchain", "lake-manifest.json", ".gitignore"], cwd=root, env=env)
    run(["git", "-c", "user.name=Cache test", "-c", "user.email=cache-test@example.invalid", "commit", "-qm", "fixture"], cwd=root, env=env)
    provenance = {"source_tree": run(["git", "rev-parse", "HEAD:src"], cwd=root, env=env).strip(),
                  "lakefile_sha256": [hashlib.sha256((root / "lakefile.toml").read_bytes()).hexdigest()],
                  "manifest_sha256": hashlib.sha256((root / "lake-manifest.json").read_bytes()).hexdigest()}
    jobs_file = temporary / "plan.jsonl"
    run(["lake", "env", tools / ".lake/build/bin/trace-cache", "plan", root, jobs_file], cwd=root, env=env)
    work = root / ".lake/bootstrap"
    work.mkdir()
    shutil.copyfile(jobs_file, work / "jobs.jsonl")
    write(work / "report-000.jsonl", json.dumps({"name": "Subject", "needsCompile": True}) + "\n")
    extras = root / ".lake/published-extras"
    extras.mkdir()
    write(extras / "runtime-attestation.jsonl", json.dumps(lint_certificate) + "\n")
    c_path = root / ".lake/build/ir/Subject.c"
    c_bytes = c_path.read_bytes()
    checksum = hashlib.sha256(c_bytes).hexdigest()
    c_path.unlink()
    write(extras / "incoming-c/Subject.c", c_bytes.decode())
    manifest = extras / "project-ir.files.sha256"
    write(manifest, f"{checksum}  .lake/build/ir/Subject.c\n")
    lib_manifest = extras / "project-lib-traces-hashes.files.sha256"
    write(lib_manifest, hashlib.sha256(hashes["remote"].encode()).hexdigest() + "  .lake/build/lib/lean/Subject.olean.hash\n")
    local_tools = root / "scripts/cache-bootstrap"
    write(local_tools / "CheckRuntime.lean", (tools / "CheckRuntime.lean").read_text())
    binary = local_tools / ".lake/build/bin/hash-outputs"
    binary.parent.mkdir(parents=True)
    binary.symlink_to(hasher)
    loaded = runpy.run_path(str(Path(__file__).resolve().parents[1] / "accept-published-c.py"))
    main = loaded["main"]
    main.__globals__["MANIFEST_SHA"] = hashlib.sha256(manifest.read_bytes()).hexdigest()
    main.__globals__["LIB_MANIFEST_SHA"] = hashlib.sha256(lib_manifest.read_bytes()).hexdigest()

    def atomic_json(path, value):
        write(path, json.dumps(value, sort_keys=True) + "\n")

    def fixture_common(path):
        if Path(path).name == "codegen-cache.py":
            return {"atomic_json": atomic_json}
        assert Path(path).name == "bootstrap-cache.py"
        return {"PUBLISHED_PROVENANCE": provenance,
                "read_jsonl": lambda path: [json.loads(line) for line in Path(path).read_text().splitlines() if line]}

    real_run = subprocess.run

    def without_rebuilding(command, **kwargs):
        if command[0] == "lake" and command[-2:] == ["build", "hash-outputs"]:
            return subprocess.CompletedProcess(command, 0)
        return real_run(command, **kwargs)

    def accept(succeeds=True):
        with patch.object(sys, "argv", ["accept-published-c", "--project", str(root)]), \
                patch.object(runpy, "run_path", side_effect=fixture_common), \
                patch.object(subprocess, "run", side_effect=without_rebuilding), redirect_stdout(io.StringIO()):
            try:
                main()
            except SystemExit:
                if succeeds:
                    raise
                return
        assert succeeds, "acceptance should have rejected the fixture"

    incoming = extras / "incoming-c/Subject.c"
    incoming.write_bytes(c_bytes + b"\n/* changed published bytes */\n")
    accept(succeeds=False)
    assert not c_path.exists()
    incoming.write_bytes(c_bytes)
    accept()
    assert c_path.read_bytes() == c_bytes
    inode = c_path.stat().st_ino
    accept()
    assert c_path.stat().st_ino == inode, "validated C must remain immutable during packing"
    bad = {**lint_certificate, "expected": "0" * 16, "candidate": "0" * 16}
    write(extras / "runtime-attestation.jsonl", json.dumps(bad) + "\n")
    accept(succeeds=False)
    write(extras / "runtime-attestation.jsonl", json.dumps(lint_certificate) + "\n")
    with old.open("ab") as stream:
        stream.write(b"changed-after-attestation")
    accept(succeeds=False)
    print("PASS guards: runtime changes reject; lint-only metadata attests without mutation; pinned acceptance preserves C and rejects unbound or stale evidence")


def main():
    here = Path(__file__).resolve().parent
    prepare_stack = runpy.run_path(str(here.parent / "bootstrap-cache.py"))["prepare_pack_stack"]
    for limits in ((8 * 1024 * 1024, resource.RLIM_INFINITY), (8 * 1024 * 1024, 64 * 1024 * 1024)):
        with patch.object(resource, "getrlimit", return_value=limits), patch.object(resource, "setrlimit") as setter:
            prepare_stack()
            setter.assert_called_once_with(resource.RLIMIT_STACK, (limits[1], limits[1]))
    with patch.object(resource, "getrlimit", return_value=(8 * 1024 * 1024,) * 2), patch.object(resource, "setrlimit") as setter:
        prepare_stack()
        setter.assert_not_called()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--trace", type=Path, default=here / ".lake/build/bin/trace-cache")
    parser.add_argument("--normalize", type=Path, default=here / ".lake/build/bin/normalize-cache")
    parser.add_argument("--keep", type=Path, help="retain the test fixture at this directory")
    parser.add_argument("--pipeline-only", action="store_true", help="run only the producer/sandbox/archive integration")
    args = parser.parse_args()
    for binary in (args.trace, args.normalize):
        if not binary.is_file():
            parser.error(f"missing {binary}; build the cache-bootstrap executables first")
    if not args.pipeline_only:
        for name in ("check-runtime", "hash-outputs", "attest-extras"):
            binary = args.trace.parent / name
            if not binary.is_file():
                parser.error(f"missing {binary}; build all five cache-bootstrap executables first")
    def suite(temporary):
        if not args.pipeline_only:
            for mode, flag in (("unspecified", None), ("independent", True), ("dependent", False)):
                integration(args.trace.resolve(), args.normalize.resolve(), temporary / mode, flag)
            guard_fixtures(args.trace.resolve().parents[3], temporary / "guards")
        orchestration(args.trace.resolve().parents[3], temporary / "pipeline")

    if args.keep:
        suite(args.keep.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="rh-cache-bootstrap-") as temporary:
            suite(Path(temporary))


if __name__ == "__main__":
    main()
