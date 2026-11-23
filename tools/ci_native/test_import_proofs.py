import hashlib
import zipfile
from pathlib import Path
import unittest
from unittest.mock import patch
import rpc
import import_proof_lease
import test_proofs

class CoordinatorReturnTests(unittest.TestCase):
    setUp = test_proofs.ProofProtocolTests.setUp
    plan = test_proofs.ProofProtocolTests.plan

    def fixture(self, modules=None):
        modules = modules or self.names[:1]
        control = self.plan(modules)
        lease = rpc.read(control / 'lease.json')
        request = rpc.read(control / 'request-0.json')
        returned = self.root / 'returned'
        returned.mkdir()
        files = []
        with zipfile.ZipFile(returned / 'runtime-parts.zip', 'w') as archive:
          for module in modules:
            for suffix in rpc.PROOF_PARTS:
                part = 'ir' if suffix == '.c' else 'lib/lean'
                path = f'.lake/build/{part}/{module.replace(".", "/")}{suffix}'
                data = (module + suffix).encode()
                archive.writestr(path, data)
                files.append({'module': module, 'path': path, 'bytes': len(data),
                              'sha256': hashlib.sha256(data).hexdigest()})
        manifest = {'schema': 1, 'snapshot': self.snapshot['fingerprint'],
                    'modules': modules, 'files': files}
        rpc.atomic(returned / 'artifacts-0.json', manifest)
        rpc.atomic(returned / 'response-0.json', {
            'snapshot': self.snapshot['fingerprint'], 'operation': rpc.PROOF_OPERATION,
            'batch': 0, 'elapsed_ms': 1234, 'lease_id': lease['lease_id'],
            'request_sha256': lease['request_sha256'], 'run_id': '123', 'run_attempt': 1,
            'runner_name': 'registered-james',
            'result': {'ok': True, 'modules': [{'module': module, 'ok': True} for module in modules]},
            'artifacts': {'manifest': 'artifacts-0.json',
                          'sha256': rpc.digest(returned / 'artifacts-0.json')}})
        provenance = {'run_id': '123', 'run_attempt': 1, 'runner_name': 'registered-james',
                      'workflow_sha': 'b' * 40,
                      'artifact_name': f'native-123-1-{lease["lease_id"]}'}
        proxy = self.root / 'proxy'
        round = self.root / 'round'
        round.mkdir()
        rpc.atomic(round / 'request-7.json', request)
        durable = self.root / 'leases.json'
        rpc.atomic(durable, {'snapshot': self.snapshot,
                             'workers': {'james': {'batch': 7, 'modules': modules}}})
        return control, returned, provenance, proxy, round, durable

    def test_real_accept_imports_eight_parts_and_completes_correct_batch(self):
        control, returned, provenance, proxy, round, durable = self.fixture()
        import_proof_lease.accept(control, returned, provenance, proxy, round, durable, 'james', 7)
        response = rpc.read(round / 'response-7.json')
        self.assertEqual(response['batch'], 7)
        self.assertEqual(response['artifacts']['files'], 8)
        self.assertEqual(response['elapsed_ms'], 1234)
        self.assertEqual(len([p for p in proxy.rglob('*') if p.is_file()]), 8)

    def test_stale_lease_or_tampered_zip_cannot_write_completion(self):
        control, returned, provenance, proxy, round, durable = self.fixture()
        state = rpc.read(durable)
        state['workers']['james']['batch'] = 8
        rpc.atomic(durable, state)
        with self.assertRaises(ValueError):
            import_proof_lease.accept(control, returned, provenance, proxy, round, durable, 'james', 7)
        self.assertFalse((round / 'response-7.json').exists())
        state['workers']['james']['batch'] = 7
        rpc.atomic(durable, state)
        with zipfile.ZipFile(returned / 'runtime-parts.zip', 'a') as archive:
            archive.writestr('../escape', b'foreign')
        with self.assertRaises(ValueError):
            import_proof_lease.accept(control, returned, provenance, proxy, round, durable, 'james', 7)
        self.assertFalse((round / 'response-7.json').exists())

    def test_actions_scope_can_have_different_order_without_changing_original(self):
        control, returned, provenance, proxy, round, durable = self.fixture(self.names[:2])
        original = (returned / 'response-0.json').read_bytes()
        expected = rpc.read(round / 'request-7.json')
        expected['modules'].reverse()
        rpc.atomic(round / 'request-7.json', expected)
        state = rpc.read(durable)
        state['workers']['james']['modules'] = expected['modules']
        rpc.atomic(durable, state)
        import_proof_lease.accept(control, returned, provenance, proxy, round, durable, 'james', 7)
        response = rpc.read(round / 'response-7.json')
        self.assertEqual([row['module'] for row in response['result']['modules']], expected['modules'])
        self.assertEqual((returned / 'response-0.json').read_bytes(), original)
        self.assertEqual(response['artifacts']['files'], 16)

    def test_different_scope_cannot_write_completion(self):
        control, returned, provenance, proxy, round, durable = self.fixture(self.names[:2])
        expected = rpc.read(round / 'request-7.json')
        expected['modules'][0] = self.names[2]
        rpc.atomic(round / 'request-7.json', expected)
        state = rpc.read(durable)
        state['workers']['james']['modules'] = expected['modules']
        rpc.atomic(durable, state)
        with self.assertRaisesRegex(ValueError, 'work scope mismatch'):
            import_proof_lease.accept(control, returned, provenance, proxy, round, durable, 'james', 7)
        self.assertFalse((round / 'response-7.json').exists())

if __name__ == '__main__':
    unittest.main()
