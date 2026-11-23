#!/usr/bin/env python3
"""Run the stock default-target producer once and bind its completed outputs."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import tomllib

SPEC = importlib.util.spec_from_file_location("complete_build_ci", Path(__file__).with_name("ci-build.py"))
ci = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ci)
COMMAND = ["lake", "--rehash", "build", "-o", "<outputs>"]
INPUT_ATTESTATION = "git-blobs-and-locked-dependencies-v1"


def identity(project, selected):
    ci.TOOLCHAIN = selected.TOOLCHAIN
    ci.validate_inputs(project, selected.DEPENDENCIES)
    head = ci.git(project, "rev-parse", "HEAD")
    subprocess.run(["git", "-C", str(project), "diff", "--no-ext-diff", "--no-textconv", "--quiet", "HEAD",
                    "--", "src", "lakefile.toml", "lake-manifest.json", "lean-toolchain"], check=True)
    if ci.git(project, "ls-files", "--others", "--", "src"):
        raise ValueError("complete builds require committed source inputs")
    inventory = subprocess.check_output(["git", "-C", str(project), "ls-tree", "-r", "-z", "HEAD", "--", "src"], env=ci.trusted_env())
    if any(entry.split(b" ", 1)[0] not in (b"100644", b"100755") for entry in inventory.split(b"\0") if entry):
        raise ValueError("complete builds reject source symlinks and submodules")
    ci.verify_snapshot(project, head, project)
    # A manifest pin does not establish that the actual package sources still
    # match their locked commits. Resolve the shared parent once; do not hash
    # generated .lake caches or copy the author's dependency build outputs.
    packages = (project / ".lake/packages").resolve()
    ci.validate_packages(project, packages)
    ci.verify_private_packages(project, packages, packages)
    for package in json.loads((project / "lake-manifest.json").read_text()).get("packages", []):
        if ci.git(packages / package["name"], "ls-files", "--others", "--exclude=.lake/", "--exclude=node_modules/",
                  "--", "*.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            raise ValueError("complete builds reject untracked dependency Lean/config inputs")
    return {"candidate_head": head,
            "candidate_tree": ci.git(project, "rev-parse", head + "^{tree}"),
            "source_tree": ci.git(project, "rev-parse", head + ":src"), "build_roots": {},
            "lakefile_sha256": ci.sha256(project / "lakefile.toml"),
            "manifest_sha256": ci.sha256(project / "lake-manifest.json"), "toolchain": selected.TOOLCHAIN,
            "default_targets": tomllib.loads((project / "lakefile.toml").read_text())["defaultTargets"]}


def validate_receipt(receipt, current, selected, log, mapping):
    if (receipt.get("schema") != 1 or receipt.get("kind") != "stock-default-target-build" or
            receipt.get("input_attestation") != INPUT_ATTESTATION or
            receipt.get("scope") != "default-targets" or receipt.get("command") != COMMAND or
            receipt.get("build_exit_code") != 0 or receipt.get("toolchain_commit") != selected.COMMIT or
            any(receipt.get(key) != value for key, value in current.items()) or
            receipt.get("build_log_sha256") != ci.sha256(log) or
            receipt.get("map_sha256") != ci.sha256(mapping)):
        raise ValueError("completed build receipt does not bind current inputs, default scope, log and map")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("project", "build-map", "build-log", "receipt"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--release", default=ci.TOOLCHAIN)
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    selected = ci.settings.for_toolchain(args.release)
    project, mapping, log, receipt = (path.resolve() for path in (args.project, args.build_map, args.build_log, args.receipt))
    if len({mapping, log, receipt}) != 3:
        raise ValueError("producer map, log and receipt must be distinct files")
    if any(path.exists() for path in (mapping, log, receipt)):
        raise ValueError("use fresh producer map/log/receipt paths, so stale results cannot be reused")
    before = identity(project, selected)
    toolchain = args.toolchain
    env = {**ci.trusted_env(), "ELAN_TOOLCHAIN": selected.TOOLCHAIN, "LEAN_NUM_THREADS": str(args.jobs),
           "LEAN_ABORT_ON_PANIC": "1", "RUST_MIN_STACK": "8388608"}
    if toolchain is None:
        toolchain = Path(subprocess.check_output(["elan", "which", "lean"], env=env, text=True).strip()).parent.parent
    version = subprocess.check_output([str(toolchain / "bin/lean"), "--version"], env=env, text=True)
    if not version.startswith(f"Lean (version {selected.VERSION},") or selected.COMMIT not in version:
        raise ValueError("the producer requires the exact registered stock toolchain")
    for path in (mapping, log, receipt):
        path.parent.mkdir(parents=True, exist_ok=True)
    # Deep proof objects require more than the usual 8 MiB packer stack.
    for kind, target in ((resource.RLIMIT_STACK, None), (resource.RLIMIT_NOFILE, 65536)):
        _, hard = resource.getrlimit(kind)
        soft = hard if target is None else (target if hard == resource.RLIM_INFINITY else min(target, hard))
        resource.setrlimit(kind, (soft, hard))
    with log.open("wb") as stream:
        code = subprocess.run([str(toolchain / "bin/lake"), "--rehash", "build", "-o", str(mapping)],
                              cwd=project, env=env, stdout=stream, stderr=subprocess.STDOUT).returncode
    if code:
        return ci.normalized_exit_code(code)
    if identity(project, selected) != before:
        raise ValueError("build inputs changed while the default-target build ran")
    if not ci.load_map(mapping):
        raise ValueError("the completed default-target build emitted an empty map")
    value = {"schema": 1, "kind": "stock-default-target-build", "scope": "default-targets", "command": COMMAND,
             "input_attestation": INPUT_ATTESTATION,
             **before, "default_targets": tomllib.loads((project / "lakefile.toml").read_text())["defaultTargets"],
             "toolchain_commit": selected.COMMIT, "build_exit_code": 0,
             "build_log_sha256": ci.sha256(log), "map_sha256": ci.sha256(mapping)}
    receipt.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"completed_default_build": True, "candidate_head": before["candidate_head"],
                      "receipt_sha256": ci.sha256(receipt)}), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
