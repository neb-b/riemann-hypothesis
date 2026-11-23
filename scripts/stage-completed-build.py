#!/usr/bin/env python3
"""Stage an already successful stock build; never elaborate proofs or upload.

The native staging directory and metadata sidecar are transferred to the operator
credential host. This command consumes the completed build's stock -o map and
checks actual LTAR content hashes with the selected stock release.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

SPEC = importlib.util.spec_from_file_location("completed_ci_build", Path(__file__).with_name("ci-build.py"))
ci = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ci)
RUN_SPEC = importlib.util.spec_from_file_location("stock_complete_build", Path(__file__).with_name("run-complete-build.py"))
complete = importlib.util.module_from_spec(RUN_SPEC)
RUN_SPEC.loader.exec_module(complete)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--build-map", type=Path, required=True)
    parser.add_argument("--build-log", type=Path, required=True)
    parser.add_argument("--build-receipt", type=Path, required=True,
                        help="fresh run-complete-build.py receipt for the full default-target build")
    parser.add_argument("--cache-dir", type=Path, help="completed native LTAR cache for modules without a local IR alias")
    parser.add_argument("--output", type=Path, required=True, help="flat native Lake staging")
    parser.add_argument("--metadata", type=Path, required=True, help="separate module manifest/provenance directory")
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--release", default=ci.TOOLCHAIN,
                        help="registered stock release to stage before activating its public baseline")
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 32:
        parser.error("--jobs must be 1..32")
    selected = ci.settings.for_toolchain(args.release)
    ci.TOOLCHAIN, ci.settings = selected.TOOLCHAIN, selected
    if ci.settings.DEPENDENCIES is None:
        raise ValueError("the trusted descriptor must first pin this build's dependency manifest")
    project = args.project.resolve()
    ci.validate_inputs(project, ci.settings.DEPENDENCIES)
    subprocess.run(["git", "-C", str(project), "diff", "--no-ext-diff", "--no-textconv", "--quiet", "HEAD",
                    "--", "src", "lakefile.toml", "lake-manifest.json", "lean-toolchain"], check=True)
    if ci.git(project, "ls-files", "--others", "--exclude-standard", "--", "src"):
        raise ValueError("completed build has uncommitted source inputs")
    log = ci.safe_file(args.build_log.parent.resolve(), args.build_log.name)
    if not re.search(rb"Build completed successfully \([0-9]+ jobs\)\.", log.read_bytes()):
        raise ValueError("the supplied stock build log does not record successful completion")
    mapping_file = ci.safe_file(args.build_map.parent.resolve(), args.build_map.name)
    receipt_file = ci.safe_file(args.build_receipt.parent.resolve(), args.build_receipt.name)
    receipt = json.loads(receipt_file.read_text())
    current = complete.identity(project, selected)
    complete.validate_receipt(receipt, current, selected, log, mapping_file)
    mapping = ci.load_map(mapping_file)
    if not mapping:
        raise ValueError("the successful build's stock -o map is empty")
    output, metadata = args.output.resolve(), args.metadata.resolve()
    if output == metadata:
        raise ValueError("native staging and module metadata must be separate directories")
    for directory in (output, metadata):
        directory.mkdir(parents=True, exist_ok=True)
        if any(directory.iterdir()):
            raise ValueError("staging destinations must be empty")
    toolchain = args.toolchain
    if toolchain is None:
        env = {**ci.trusted_env(), "ELAN_TOOLCHAIN": ci.TOOLCHAIN}
        toolchain = Path(subprocess.check_output(["elan", "which", "lean"], env=env, text=True).strip()).parent.parent
    version = subprocess.check_output([str(toolchain / "bin/lean"), "--version"], env=ci.trusted_env(), text=True)
    if not version.startswith(f"Lean (version {ci.settings.VERSION},") or ci.settings.COMMIT not in version:
        raise ValueError("LTAR hashing requires the exact descriptor-pinned stock release")
    modules, seen = [], set()
    for name, module, dep_hash in ci.module_traces(project):
        if dep_hash not in mapping:
            continue
        if dep_hash in seen:
            raise ValueError("multiple modules claim one build input hash")
        seen.add(dep_hash)
        try:
            archive = ci.safe_file(project / ".lake/build/ir", str(module.parent / (module.name + ".ltar")))
        except FileNotFoundError:
            if args.cache_dir is None:
                raise ValueError("module LTAR alias absent; supply its completed native --cache-dir") from None
            archive = ci.safe_file(args.cache_dir.resolve(), "artifacts/" + mapping[dep_hash])
        alias = output / mapping[dep_hash]
        if not alias.exists():
            try:
                os.link(archive, alias)
            except OSError:
                shutil.copyfile(archive, alias)
        modules.append((name, dep_hash, mapping[dep_hash]))
    if seen != set(mapping):
        raise ValueError("current module traces do not cover the complete stock output map")
    paths = sorted(output.iterdir())
    with tempfile.TemporaryDirectory(prefix="hash-completed-", dir=metadata) as work:
        actual = ci.native_hashes(toolchain, paths, Path(work))
    if any(actual.get(path.name) != path.stem for path in paths):
        raise ValueError("a staged LTAR differs from the completed map's stock content hash")
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        hashes = dict(zip((path.name for path in paths), pool.map(ci.sha256, paths)))
    contents = mapping_file.read_bytes()
    if complete.identity(project, selected) != current:
        raise ValueError("build inputs changed during completed-artifact staging")
    complete.validate_receipt(receipt, current, selected, log, mapping_file)
    (output / "outputs.jsonl").write_bytes(contents)
    inputs = {"source_tree": ci.git(project, "rev-parse", "HEAD:src"), "build_roots": {},
              "lakefile_sha256": ci.sha256(project / "lakefile.toml"),
              "manifest_sha256": ci.sha256(project / "lake-manifest.json"), "toolchain": ci.TOOLCHAIN}
    fingerprint = hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    map_sha = hashlib.sha256(contents).hexdigest()
    header = {"schema": 1, **inputs, "map_sha256": map_sha, "input_fingerprint": fingerprint, "modules": len(modules)}
    manifest = metadata / "modules.jsonl.gz"
    with manifest.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as zipped:
        zipped.write((json.dumps(header, sort_keys=True, separators=(",", ":")) + "\n").encode())
        for name, dep_hash, filename in sorted(modules):
            zipped.write((json.dumps([name, dep_hash, filename, hashes[filename]], separators=(",", ":")) + "\n").encode())
    revision = ci.git(project, "rev-parse", "HEAD")
    summary = {"schema": 1, "validation": "completed stock build; actual compressed bytes checked with stock Lake hash and SHA256",
               "candidate_head": revision, "candidate_tree": ci.git(project, "rev-parse", "HEAD^{tree}"), **inputs,
               "input_fingerprint": fingerprint, "build_log_sha256": ci.sha256(log),
               "build_receipt_sha256": ci.sha256(receipt_file),
               "modules": len(modules), "artifacts": len(paths), "artifact_bytes": sum(path.stat().st_size for path in paths),
               "baseline": {"revision": revision, "map_sha256": map_sha, "manifest_sha256": ci.sha256(manifest)}}
    (metadata / "completed-build.json").write_text(json.dumps(summary, sort_keys=True, indent=2) + "\n")
    shutil.copyfile(receipt_file, metadata / "build-receipt.json")
    print(json.dumps(summary, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
