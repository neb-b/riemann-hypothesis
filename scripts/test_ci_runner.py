#!/usr/bin/env python3
"""Credential and process-boundary checks; no GitHub/AWS calls or registration."""
import importlib.util
import base64
import os
import json
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

SCRIPT = Path(__file__).with_name("ci-runner.py")
spec = importlib.util.spec_from_file_location("ci_runner", SCRIPT)
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class RunnerChecks(unittest.TestCase):
    def test_missing_elan_is_a_failed_required_command(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            tools = root / "bin"
            tools.mkdir()
            for command in ("git", "cc", "python3", "bwrap"):
                path = tools / command
                path.touch()
                path.chmod(0o700)
            with patch.object(runner.Path, "home", return_value=root), patch.dict(os.environ, {"PATH": str(tools)}):
                missing = runner.required_commands()
                self.assertIsNone(missing["elan"])
                self.assertFalse(all(missing.values()))
                elan = tools / "elan"
                elan.touch()
                elan.chmod(0o700)
                self.assertEqual(runner.required_commands()["elan"], str(elan))
                self.assertTrue(all(runner.required_commands().values()))

    def test_elan_home_precedes_path_as_in_the_build_workflow(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            home_bin, other_bin = root / ".elan/bin", root / "bin"
            home_bin.mkdir(parents=True)
            other_bin.mkdir()
            for directory in (home_bin, other_bin):
                elan = directory / "elan"
                elan.touch()
                elan.chmod(0o700)
            with patch.object(runner.Path, "home", return_value=root), patch.dict(os.environ, {"PATH": str(other_bin)}):
                self.assertEqual(runner.required_commands()["elan"], str(home_bin / "elan"))
                (home_bin / "elan").chmod(0o600)
                self.assertEqual(runner.required_commands()["elan"], str(other_bin / "elan"))

    def identity_fixture(self, root):
        installed, source = root / "installed", root / "identity"
        installed.mkdir(mode=0o700); source.mkdir(mode=0o700)
        for name in ("config.sh", "run.sh", "bin/Runner.Listener"):
            path = installed / name; path.parent.mkdir(exist_ok=True)
            path.write_text("must never execute")
        policy = root / "policy.json"
        policy.write_text(json.dumps({"id": 5, "name": runner.GROUP, "visibility": "selected",
                                     "allows_public_repositories": True, "restricted_to_workflows": True,
                                     "selected_workflows": [f"{runner.WORKFLOW}@{runner.MAIN_REF}"]}))
        policy.chmod(0o600)
        settings = dict(agentId=123456, agentName="volunteer-host", poolId=5, poolName=runner.GROUP,
                        serverUrl="https://pipelines.actions.githubusercontent.com/example/", gitHubUrl=runner.ORGANIZATION,
                        workFolder="_work", useV2Flow=True,
                        serverUrlV2="https://broker.actions.githubusercontent.com/")
        credential = {"scheme": "OAuth", "data": {"clientId": "11111111-2222-4333-8444-555555555555",
                      "authorizationUrl": "https://tokenghub.actions.githubusercontent.com/example/one/two/three", "requireFipsCryptography": "True"}}
        rsa = {key: base64.b64encode(b"x" * (256 if key in ("d", "modulus") else 3 if key == "exponent" else 128)).decode()
               for key in ("d", "dp", "dq", "exponent", "inverseQ", "modulus", "p", "q")}
        for name, value in zip(runner.IDENTITY_FILES, (settings, credential, rsa)):
            # Official runner 2.338.2 on the live AWS host writes UTF-8 BOM JSON.
            path = source / name; path.write_text(json.dumps(value), encoding="utf-8-sig"); path.chmod(0o600)
        return SimpleNamespace(directory=installed, identity_directory=source, policy_file=policy,
                               name="volunteer-host", runner_id=123456)

    @unittest.skipIf(os.getuid() == 0, "adoption correctly refuses root")
    def test_adopt_copies_only_one_identity_without_process_or_enrollment_token(self):
        with tempfile.TemporaryDirectory() as name:
            args = self.identity_fixture(Path(name))
            with patch.object(runner.subprocess, "run", side_effect=AssertionError("adoption must not execute bundle data")):
                runner.adopt_identity(args)
            for filename in runner.IDENTITY_FILES:
                actual = args.directory / filename
                self.assertEqual(actual.stat().st_mode & 0o777, 0o600)
                self.assertEqual(json.loads(actual.read_text()), json.loads((args.identity_directory / filename).read_text(encoding="utf-8-sig")))
            with self.assertRaisesRegex(ValueError, "already has identity"):
                runner.adopt_identity(args)

    @unittest.skipIf(os.getuid() == 0, "adoption correctly refuses root")
    def test_adopt_rejects_other_group_endpoints_paths_and_unexpected_files(self):
        mutations = [(".runner", "poolId", 1), (".runner", "agentId", 999),
                     (".runner", "workFolder", "/outside"), (".runner", "gitHubUrl", "https://github.com/other-org"),
                     (".runner", "serverUrl", "https://evil.example/"), (".credentials", "scheme", "OAuthAccessToken")]
        for filename, key, value in mutations:
            with self.subTest(key=key), tempfile.TemporaryDirectory() as name:
                args = self.identity_fixture(Path(name)); path = args.identity_directory / filename
                obj = json.loads(path.read_text(encoding="utf-8-sig")); obj[key] = value; path.write_text(json.dumps(obj))
                with self.assertRaises(ValueError):
                    runner.adopt_identity(args)
                self.assertFalse((args.directory / ".runner").exists())
        with tempfile.TemporaryDirectory() as name:
            args = self.identity_fixture(Path(name)); path = args.identity_directory / ".credentials"
            obj = json.loads(path.read_text(encoding="utf-8-sig")); obj["data"]["authorizationUrl"] = "https://evil.example/"
            path.write_text(json.dumps(obj))
            with self.assertRaisesRegex(ValueError, "OAuth endpoint"):
                runner.adopt_identity(args)
        with tempfile.TemporaryDirectory() as name:
            args = self.identity_fixture(Path(name)); (args.identity_directory / "registration-token").write_text("not allowed")
            with self.assertRaisesRegex(ValueError, "exactly the three"):
                runner.adopt_identity(args)

    @unittest.skipIf(os.getuid() == 0, "adoption correctly refuses root")
    def test_adopt_rejects_public_files_and_symlinks(self):
        for symlink in (False, True):
            with self.subTest(symlink=symlink), tempfile.TemporaryDirectory() as name:
                args = self.identity_fixture(Path(name)); path = args.identity_directory / ".credentials"
                if symlink:
                    path.rename(args.identity_directory.parent / "outside")
                    path.symlink_to(args.identity_directory.parent / "outside")
                else:
                    path.chmod(0o644)
                with self.assertRaises((ValueError, OSError)):
                    runner.adopt_identity(args)

    def test_private_credentials_reject_public_files_and_symlinks(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "credential"
            path.write_text("testcredential")
            path.chmod(0o600)
            self.assertEqual(runner.private_file(path), "testcredential")
            path.chmod(0o644)
            with self.assertRaises(ValueError):
                runner.private_file(path)
            path.chmod(0o600)
            link = path.with_name("link")
            link.symlink_to(path)
            with self.assertRaises(OSError):
                runner.private_file(link)

    @unittest.skipIf(os.getuid() == 0, "registration correctly refuses root")
    def test_failed_official_config_does_not_echo_token_in_error(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            root.chmod(0o700)
            config = root / "config.sh"
            config.write_text("#!/bin/sh\nexit 7\n")
            config.chmod(0o700)
            token = root / "registration-token"
            secret = "not-a-real-registration-token-1234"
            token.write_text(secret)
            token.chmod(0o600)
            policy = root / "policy.json"
            policy.write_text(json.dumps({
                "name": runner.GROUP, "visibility": "selected", "allows_public_repositories": True,
                "restricted_to_workflows": True,
                "selected_workflows": [f"{runner.WORKFLOW}@{runner.MAIN_REF}"]}))
            policy.chmod(0o600)
            result = subprocess.run(
                [sys.executable, str(SCRIPT), "register", "--directory", str(root),
                 "--token-file", str(token), "--policy-file", str(policy)], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertNotIn(secret, result.stdout + result.stderr)
            self.assertIn("credentials omitted", result.stderr)

    def test_max_map_count_reads_value_and_tolerates_missing_or_malformed_file(self):
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "max_map_count"
            self.assertIsNone(runner.max_map_count(path))
            path.write_text("65530\n")
            self.assertEqual(runner.max_map_count(path), 65530)
            self.assertLess(runner.max_map_count(path), runner.MINIMUM_MAX_MAP_COUNT)
            path.write_text("not a number\n")
            self.assertIsNone(runner.max_map_count(path))

    def test_failed_checks_name_each_unmet_prerequisite_with_its_required_value(self):
        minimum = runner.MINIMUM_MAX_MAP_COUNT
        commands = dict.fromkeys(("git", "cc", "python3", "bwrap", "elan"), "/usr/bin/tool")

        def check(**changes):
            report = {"uid": 1000, "commands": commands, "offline_bwrap": True,
                      "free_disk_gib": 300.0, "max_map_count": minimum} | changes
            return runner.failed_checks(report, 250, minimum)

        self.assertEqual(check(), [])
        self.assertEqual(check(max_map_count=65530),
                         [f"max_map_count is 65530, need at least {minimum} (sysctl vm.max_map_count, set on the host)"])
        self.assertEqual(check(max_map_count=None),
                         [f"max_map_count is unreadable, need at least {minimum} (sysctl vm.max_map_count, set on the host)"])
        self.assertEqual(check(free_disk_gib=120.5), ["free_disk_gib is 120.5, need at least 250"])
        self.assertEqual(check(uid=0), ["uid is 0: use a dedicated unprivileged account"])
        self.assertEqual(check(offline_bwrap=False), ["offline_bwrap probe failed: see bwrap_error"])
        # A missing bwrap also leaves offline_bwrap false; it is named once, as the missing command.
        self.assertEqual(check(commands=commands | {"bwrap": None, "elan": None}, offline_bwrap=False),
                         ["command not found: bwrap", "command not found: elan"])
        self.assertEqual(len(check(uid=0, free_disk_gib=1, max_map_count=65530)), 3)
        # Zero minimums switch the threshold checks off, even when the value cannot be read.
        self.assertEqual(runner.failed_checks(
            {"uid": 1000, "commands": commands, "offline_bwrap": True, "free_disk_gib": 0.0, "max_map_count": None}, 0, 0), [])

    def test_policy_rejects_branch_or_repository_expansion(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "policy.json"
            data = {"name": runner.GROUP, "visibility": "selected", "allows_public_repositories": True,
                    "restricted_to_workflows": True,
                    "selected_workflows": [f"{runner.WORKFLOW}@{runner.MAIN_REF}"]}
            path.write_text(json.dumps(data)); path.chmod(0o600)
            runner.check_policy(path)
            data["selected_workflows"].append(f"{runner.WORKFLOW}@refs/pull/123/head")
            path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):
                runner.check_policy(path, maintenance=True)
            data["selected_workflows"] = [f"{runner.WORKFLOW}@{runner.MAINTENANCE_REF}"]
            path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):
                runner.check_policy(path)
            runner.check_policy(path, maintenance=True)

    def test_unit_rejects_newline_and_escapes_systemd_specifiers(self):
        with self.assertRaises(ValueError):
            runner.systemd_quote("/runner\nExecStart=malicious")
        self.assertEqual(runner.systemd_quote('/runner/%h/"quoted"'),
                         '"/runner/%%h/\\"quoted\\""')


    @unittest.skipUnless(shutil.which("systemd-analyze"), "systemd-analyze is not installed")
    def test_generated_unit_passes_real_systemd_parser(self):
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name) / 'runner with spaces'
            directory.mkdir(mode=0o700)
            executable = directory / "run.sh"
            executable.write_text("#!/bin/sh\nexit 0\n")
            executable.chmod(0o700)
            contents = subprocess.check_output(
                [sys.executable, str(SCRIPT), "systemd-unit", "--directory", str(directory),
                 "--jobs", "64", "--memory-gib", "384"], text=True)
            self.assertIn("Environment=RH_CI_JOBS=64\n", contents)
            self.assertIn("Environment=RH_CI_MEMORY_GIB=384\n", contents)
            service = Path(name) / "rh-runner-test.service"
            service.write_text(contents)
            result = subprocess.run(["systemd-analyze", "--user", "verify", str(service)],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_service_resource_options_reject_invalid_limits_without_emitting_a_unit(self):
        with tempfile.TemporaryDirectory() as name:
            for flag, value in (("--jobs", "0"), ("--memory-gib", "-1"), ("--jobs", "64\nExecStart=bad")):
                with self.subTest(flag=flag, value=value):
                    result = subprocess.run([sys.executable, str(SCRIPT), "systemd-unit", "--directory", name,
                                             flag, value], capture_output=True, text=True)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")

    def test_service_defaults_leave_build_resource_selection_to_the_workflow(self):
        with tempfile.TemporaryDirectory() as name:
            output = subprocess.check_output([sys.executable, str(SCRIPT), "systemd-unit", "--directory", name], text=True)
            self.assertNotIn("RH_CI_JOBS", output)
            self.assertNotIn("RH_CI_MEMORY_GIB", output)


if __name__ == "__main__":
    unittest.main()
