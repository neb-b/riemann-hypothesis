#!/usr/bin/env python3
"""Offline regression tests for restore paths, tar completion, and helper preflight."""
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def reference_local_path(root, relative, checked):
    path = root
    for part in relative.parts:
        if part in ("", ".", "..") or "/" in part or "\\" in part:
            raise ValueError("unsafe module path")
        path = path / part
        if path not in checked:
            if path.is_symlink():
                raise ValueError(f"symlink in source/output path: {path}")
            checked.add(path)
    return path


def supervised(kind, *args):
    command = [sys.executable, str(Path(__file__).resolve()), "--worker", kind, *map(str, args)]
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        raise AssertionError(f"fixture exceeded completion budget: {kind}\n{stdout}\n{stderr}")
    return process.returncode, stdout, stderr


def raw_tar(name, contents, padding=0):
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode="w") as archive:
        member = tarfile.TarInfo(name)
        member.size = len(contents)
        archive.addfile(member, io.BytesIO(contents))
    return stream.getvalue() + b"\0" * padding


def worker(kind, *args):
    if kind == "fifo":
        helper = load("runner_fixture", SCRIPTS / "ci-runner.py")
        try:
            helper.private_file(Path(args[0]))
        except ValueError:
            print("rejected")
            return
        raise AssertionError("FIFO credential was accepted")
    helper = load("fetch_fixture", SCRIPTS / "fetch-published-cache.py")
    archive, project = map(Path, args[:2])
    expected = {".lake/build/lib/lean/A.olean": hashlib.sha256(b"ok").hexdigest()}
    if kind == "bad-exit":
        original = subprocess.Popen

        def failing_producer(*unused, **kwargs):
            return original([sys.executable, "-c",
                             "import sys; sys.stdout.buffer.write(open(sys.argv[1], 'rb').read()); sys.exit(7)",
                             args[2]], **kwargs)

        with patch.object(helper.subprocess, "Popen", failing_producer):
            helper.extract_verified(archive, expected, project)
        raise AssertionError("nonzero decompressor exit was accepted")
    print(json.dumps(helper.extract_verified(archive, expected, project)))


class RestorePathTests(unittest.TestCase):
    def setUp(self):
        self.helper = load("restore_fixture", SCRIPTS / "restore-cache.py")

    def test_valid_paths_preserve_results_and_ancestor_closed_memo(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            original, optimized = set(), set()
            relatives = [Path(), Path("src/Unicode/Θ'.lean")]
            for index in range(120):
                module = Path("Nested") / f"Group{index // 10}" / f"Subject{index}"
                relatives.append(Path("src") / module.with_suffix(".lean"))
                for suffix in (".trace", ".olean", ".ilean"):
                    relatives.append(Path(".lake/build/lib/lean") / module.with_suffix(suffix))
                relatives.append(Path(".lake/build/ir") / module.with_suffix(".c"))
            relatives += relatives[20:40]
            for relative in relatives:
                self.assertEqual(reference_local_path(root, relative, original),
                                 self.helper.local_path(root, relative, optimized))
                self.assertEqual(original, optimized)

    def test_unsafe_paths_reject(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for relative in ("../Subject", "src/../Subject", "/Subject", "Subject\\Other"):
                for function in (reference_local_path, self.helper.local_path):
                    with self.assertRaises(ValueError):
                        function(root, Path(relative), set())

    def test_leaf_and_ancestor_symlinks_reject(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            outside = root / "outside"
            outside.mkdir()
            (outside / "Subject.lean").write_text("theorem fixture : True := True.intro\n")
            (root / "linked").symlink_to(outside, target_is_directory=True)
            (root / "leaf.lean").symlink_to(outside / "Subject.lean")
            for relative in (Path("linked/Subject.lean"), Path("leaf.lean")):
                for function in (reference_local_path, self.helper.local_path):
                    with self.assertRaises(ValueError):
                        function(root, relative, set())


@unittest.skipUnless(shutil.which("zstd"), "zstd is required for the extraction fixture")
class TarCompletionTests(unittest.TestCase):
    def fixture(self, root, name=".lake/build/lib/lean/A.olean", contents=b"ok", padding=0):
        raw = raw_tar(name, contents, padding)
        archive, plain = root / "fixture.tar.zst", root / "fixture.tar"
        plain.write_bytes(raw)
        with archive.open("wb") as output:
            subprocess.run(["zstd", "-q", "-c"], input=raw, stdout=output, check=True)
        project = root / "project"
        project.mkdir()
        return archive, plain, project

    def test_padded_valid_tar_finishes(self):
        with tempfile.TemporaryDirectory() as temporary:
            archive, _, project = self.fixture(Path(temporary), padding=2 * 1024 * 1024)
            code, stdout, stderr = supervised("extract", archive, project)
            self.assertEqual(code, 0, stderr)
            self.assertEqual(json.loads(stdout)["files"], 1)
            self.assertEqual((project / ".lake/build/lib/lean/A.olean").read_bytes(), b"ok")

    def test_nonzero_producer_exit_still_rejects(self):
        with tempfile.TemporaryDirectory() as temporary:
            archive, plain, project = self.fixture(Path(temporary))
            code, _, stderr = supervised("bad-exit", archive, project, plain)
            self.assertNotEqual(code, 0)
            self.assertIn("zstd decompression failed", stderr)

    def test_hash_mismatch_does_not_install(self):
        with tempfile.TemporaryDirectory() as temporary:
            archive, _, project = self.fixture(Path(temporary), contents=b"bad")
            code, _, stderr = supervised("extract", archive, project)
            self.assertNotEqual(code, 0)
            self.assertIn("File SHA256 mismatch", stderr)
            self.assertFalse((project / ".lake/build/lib/lean/A.olean").exists())

    def test_unsafe_archive_path_rejects(self):
        with tempfile.TemporaryDirectory() as temporary:
            archive, _, project = self.fixture(Path(temporary), name="../A.olean")
            code, _, stderr = supervised("extract", archive, project)
            self.assertNotEqual(code, 0)
            self.assertIn("Unsafe archive path", stderr)
            self.assertFalse((project.parent / "A.olean").exists())


class HelperPreflightTests(unittest.TestCase):
    def test_resource_only_skips_recovery(self):
        helper = load("build_tests_fixture", SCRIPTS / "cache-bootstrap/test_ci_build.py")
        with patch.object(sys, "argv", ["test_ci_build.py", "--resource-tests-only"]), \
                patch.object(helper, "resource_tests") as resources, \
                patch.object(helper, "recovery_tests", side_effect=AssertionError("recovery ran")):
            helper.main()
        resources.assert_called_once()

    def test_normal_mode_still_enters_recovery(self):
        helper = load("normal_build_tests_fixture", SCRIPTS / "cache-bootstrap/test_ci_build.py")
        with patch.object(sys, "argv", ["test_ci_build.py"]), \
                patch.object(helper, "resource_tests"), \
                patch.object(helper, "recovery_tests", side_effect=RuntimeError("recovery reached")):
            with self.assertRaisesRegex(RuntimeError, "recovery reached"):
                helper.main()

    @unittest.skipUnless(hasattr(os, "mkfifo"), "FIFO fixture requires POSIX")
    def test_fifo_credential_rejects_without_waiting_for_writer(self):
        with tempfile.TemporaryDirectory() as temporary:
            fifo = Path(temporary) / "credential"
            os.mkfifo(fifo, 0o600)
            code, stdout, stderr = supervised("fifo", fifo)
            self.assertEqual(code, 0, stderr)
            self.assertEqual(stdout.strip(), "rejected")

    def test_regular_private_credential_and_public_bits(self):
        helper = load("regular_runner_fixture", SCRIPTS / "ci-runner.py")
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "credential"
            path.write_text("fixture-token\n")
            path.chmod(0o600)
            self.assertEqual(helper.private_file(path), "fixture-token")
            path.chmod(0o644)
            with self.assertRaises(ValueError):
                helper.private_file(path)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--worker":
        worker(*sys.argv[2:])
    else:
        unittest.main()
