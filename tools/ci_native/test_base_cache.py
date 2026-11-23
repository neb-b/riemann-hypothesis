import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import launch
import proof_baseline
import rpc

class SealedBaseTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def seal(self):
        base = self.root / 'expanded'
        for part in ('lib/lean', 'ir'):
            (base / '.lake/build' / part).mkdir(parents=True)
        rpc.atomic(base / 'complete.json', proof_baseline.seal_fields())
        return base

    def test_sealed_warm_base_never_invokes_unpack_or_reads_compressed_cache(self):
        base = self.seal()
        worker = {'expanded_base_root': str(base), 'baseline_cache_root': '/missing',
                  'toolchain_root': '/missing'}
        with patch.object(proof_baseline.subprocess, 'run', side_effect=AssertionError('cold expansion repeated')):
            self.assertEqual(proof_baseline.ensure(worker, self.root, self.root, []), base)

    def test_foreign_seal_or_symlink_is_not_reused(self):
        base = self.seal()
        seal = rpc.read(base / 'complete.json')
        seal['worklist_sha256'] = '0' * 64
        rpc.atomic(base / 'complete.json', seal)
        self.assertFalse(proof_baseline.prepared(base))
        worker = {'expanded_base_root': str(base)}
        with self.assertRaises(ValueError):
            proof_baseline.ensure(worker, self.root, self.root, [])
        alias = self.root / 'alias'
        alias.symlink_to(base, target_is_directory=True)
        self.assertFalse(proof_baseline.prepared(alias))

    def test_private_copy_fallback_cannot_modify_original_dependency_inode(self):
        deps = self.root / 'deps'
        package = deps / 'fixture'
        package.mkdir(parents=True)
        (package / '.git').mkdir()
        (package / '.git/config').write_text('original metadata')
        (package / 'source.lean').write_text('original source')
        output = self.root / 'output'
        args = launch.dependency_mounts(self.root / 'candidate', deps, output,
                                        [{'name': 'fixture'}], False)
        copied = output / 'dependency-overlays/fixture/copy'
        self.assertNotEqual((copied / 'source.lean').stat().st_ino,
                            (package / 'source.lean').stat().st_ino)
        (copied / 'source.lean').write_text('private change')
        self.assertEqual((package / 'source.lean').read_text(), 'original source')
        self.assertFalse((copied / '.git/config').exists())
        self.assertIn('--ro-bind', args)
        self.assertIn(str(package / '.git'), args)

if __name__ == '__main__':
    unittest.main()
