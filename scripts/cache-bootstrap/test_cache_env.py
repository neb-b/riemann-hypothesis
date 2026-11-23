#!/usr/bin/env python3
"""Offline tests that cache-env.sh finds the project root from the shell that sources it."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SETTINGS = Path(__file__).resolve().parent.parent / "cache-env.sh"


def exported_paths(shell):
    """Source a copy of cache-env.sh from a temporary project root and return that root and the two paths it exports."""
    with tempfile.TemporaryDirectory(prefix="rh-cache-env-") as temporary:
        project = Path(temporary).resolve() / "project"
        (project / "scripts").mkdir(parents=True)
        shutil.copy(SETTINGS, project / "scripts")
        script = 'source scripts/cache-env.sh && printf "%s\\n" "$LAKE_CONFIG" "$LAKE_CACHE_DIR"'
        result = subprocess.run([*shell, "-c", script], cwd=project, env={"PATH": os.environ["PATH"]},
                                capture_output=True, text=True, check=True)
        return project, result.stdout.splitlines()


class ProjectRoot(unittest.TestCase):
    def check(self, shell):
        project, paths = exported_paths(shell)
        self.assertEqual(paths, [str(project / "lakefile.toml"), str(project / ".lake/cache")])

    def test_sourced_from_bash(self):
        self.check(["bash"])

    @unittest.skipUnless(shutil.which("zsh"), "zsh is not installed")
    def test_sourced_from_zsh(self):
        self.check(["zsh", "-f"])  # -f: skip the user's startup files


if __name__ == "__main__":
    unittest.main()
