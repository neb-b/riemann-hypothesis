#!/usr/bin/env python3
"""Small local fixture for pinned bulk restore, integrity, and path rejection."""
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from unittest.mock import patch


def run(command, root):
    return subprocess.check_output(command, cwd=root, text=True, stderr=subprocess.STDOUT)


def main():
    here = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location("restore_cache", here.parent / "restore-cache.py")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    with tempfile.TemporaryDirectory(prefix="rh-bulk-restore-") as temporary:
        root = Path(temporary)
        (root / "src").mkdir()
        (root / "src/Subject.lean").write_text("def answer : Nat := 42\ntheorem yes : True := True.intro\n")
        (root / "lean-toolchain").write_text(helper.HEADER["toolchain"] + "\n")
        (root / "lakefile.toml").write_text('name = "bulkFixture"\nsrcDir = "src"\n[[lean_lib]]\nname = "Subject"\n')
        run(["lake", "build", "Subject"], root)
        run(["git", "init", "-q"], root)
        run(["git", "add", "src", "lean-toolchain", "lakefile.toml", "lake-manifest.json"], root)
        run(["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture"], root)
        helper.HEADER = {**helper.HEADER, "source_tree": run(["git", "rev-parse", "HEAD:src"], root).strip(), "modules": 1}
        helper.CONFIG_HASHES = {helper.sha256(root / "lakefile.toml")}
        helper.DEPENDENCIES_SHA256 = helper.sha256(root / "lake-manifest.json")
        helper.check_project(root)
        lib, ir = root / ".lake/build/lib/lean", root / ".lake/build/ir"
        originals = {suffix: (ir if suffix == "c" else lib).joinpath("Subject." + suffix).read_bytes()
                     for suffix in ("olean", "ilean", "c")}
        dep_hash = json.loads((lib / "Subject.trace").read_text())["depHash"]
        artifacts = root / ".lake/cache/artifacts"
        artifacts.mkdir(parents=True)
        artifact = "1" * 16 + ".ltar"
        archive = artifacts / artifact
        leantar = Path(run(["elan", "which", "lean"], root).strip()).with_name("leantar")
        run([str(leantar), "-s", "-C", str(lib), "-C", str(ir), str(archive),
             "Subject.trace", "-i", "0", "Subject.olean", "-i", "0", "Subject.ilean", "-i", "1", "Subject.c"], root)
        row = ["Subject", dep_hash, artifact, helper.sha256(archive)]
        data = gzip.compress((json.dumps(helper.HEADER) + "\n" + json.dumps(row) + "\n").encode(), mtime=0)
        helper.MANIFEST_SHA256 = hashlib.sha256(data).hexdigest()
        manifest = root / "modules.jsonl.gz"
        manifest.write_bytes(data)
        assert helper.manifest_rows(data) == [row]
        shutil.rmtree(root / ".lake/build")
        with patch.object(sys, "argv", ["restore-cache", "--project", str(root), "--manifest", str(manifest), "--jobs", "2"]):
            helper.main()
        for suffix, contents in originals.items():
            assert (ir if suffix == "c" else lib).joinpath("Subject." + suffix).read_bytes() == contents
        assert json.loads((lib / "Subject.trace").read_text())["depHash"] == dep_hash
        (lib / "Subject.olean").unlink()
        with patch.object(sys, "argv", ["restore-cache", "--project", str(root), "--manifest", str(manifest), "--jobs", "2"]):
            helper.main()
        assert (lib / "Subject.olean").read_bytes() == originals["olean"]
        (lib / "Subject.olean").write_bytes(b"corrupt existing output")
        with patch.object(sys, "argv", ["restore-cache", "--project", str(root), "--manifest", str(manifest), "--jobs", "2"]):
            helper.main()
        assert (lib / "Subject.olean").read_bytes() == originals["olean"]

        def rejects(function):
            try:
                function()
            except (ValueError, subprocess.CalledProcessError):
                return
            raise AssertionError("unsafe fixture was accepted")

        rejects(lambda: helper.manifest_rows(data + b"changed"))
        (lib / "Subject.olean").unlink()
        (lib / "Subject.olean").symlink_to(root / "outside.olean")
        rejects(lambda: helper.restore_jobs(root, root / ".lake/cache", [row]))
        (lib / "Subject.olean").unlink()
        shutil.rmtree(ir)
        ir.symlink_to(root / "src", target_is_directory=True)
        rejects(lambda: helper.restore_jobs(root, root / ".lake/cache", [row]))
        ir.unlink()
        for bad_name in ("../Subject", "Subject/Other", "/Subject"):
            bad_data = gzip.compress((json.dumps(helper.HEADER) + "\n" + json.dumps([bad_name, *row[1:]]) + "\n").encode(), mtime=0)
            helper.MANIFEST_SHA256 = hashlib.sha256(bad_data).hexdigest()
            rejects(lambda: helper.manifest_rows(bad_data))
        archive.write_bytes(archive.read_bytes()[:-1])
        rejects(lambda: helper.restore_jobs(root, root / ".lake/cache", [row]))
        (root / "src/Subject.lean").write_text("changed source\n")
        rejects(lambda: helper.check_project(root))
        # The script itself still holds the real pins, so it stops on this fixture and says what to run instead.
        stopped = subprocess.run([sys.executable, str(here.parent / "restore-cache.py"), "--project", str(root)],
                                 capture_output=True, text=True)
        assert stopped.returncode == 1 and "source scripts/cache-env.sh && lake build" in stopped.stderr, stopped.stderr
    print("PASS bulk restore: stock output bytes match; partial artifacts, changed source, traversal, and output symlinks reject")


if __name__ == "__main__":
    main()
