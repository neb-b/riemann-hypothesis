from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import launch
import rpc

class FreshLeaseTests(unittest.TestCase):
    def test_reused_output_fails_before_any_old_artifact_can_be_staged(self):
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            candidate, control, output = base / 'candidate', base / 'control', base / 'output'
            (candidate / '.lake/build').mkdir(parents=True)
            control.mkdir()
            output.mkdir()
            old = output / 'returned'
            old.mkdir()
            prior = b'{"run_id":"old-run","lease_id":"old-lease"}\n'
            (old / 'response-0.json').write_bytes(prior)
            producer = base / 'producer.py'
            producer.write_text('fixture')
            rpc.atomic(control / 'lease.json', {'operation': rpc.PROOF_OPERATION,
                                              'producer_sha256': rpc.digest(producer), 'worker': {}})
            rpc.atomic(control / 'request-0.json', {})
            with patch.object(rpc, 'check_lease'), patch.object(rpc, 'resource_limits'), \
                 patch.object(rpc, 'stage_zip', side_effect=AssertionError('stale seed staging reached')):
                with self.assertRaisesRegex(ValueError, 'lease output must be fresh'):
                    launch.command(candidate, control, output, producer, '1', 1, 'fixture')
            self.assertEqual((old / 'response-0.json').read_bytes(), prior)

    def test_two_workflow_leases_select_distinct_inputs_and_upload_paths(self):
        import yaml
        workflow = yaml.safe_load((Path(__file__).parents[2] / '.github/workflows/build-pr.yml').read_text())
        job = workflow['jobs']['proof_worker']
        with tempfile.TemporaryDirectory() as temp:
            workspace = Path(temp)
            def resolved(template, run, attempt, lease):
                return Path(template.replace('${{ github.workspace }}', str(workspace))
                            .replace('${{ github.run_id }}', run)
                            .replace('${{ github.run_attempt }}', attempt)
                            .replace('${{ matrix.lease_id }}', lease))
            first = resolved(job['env']['PROOF_OUTPUT_ROOT'], '1', '1', 'old')
            second = resolved(job['env']['PROOF_OUTPUT_ROOT'], '2', '1', 'new')
            (first / 'returned').mkdir(parents=True)
            (first / 'seed').mkdir()
            (first / 'returned/response-0.json').write_text('old response')
            (first / 'seed/conflicting.trace').write_text('old trace')
            second.mkdir(parents=True)
            self.assertFalse(any(second.iterdir()))
            upload = next(step['with']['path'] for step in job['steps']
                          if step.get('uses', '').startswith('actions/upload-artifact@'))
            self.assertEqual(upload, '${{ env.PROOF_OUTPUT_ROOT }}/returned')
            self.assertFalse((second / 'returned/response-0.json').exists())
            self.assertEqual((first / 'returned/response-0.json').read_text(), 'old response')
            self.assertNotEqual(resolved(job['env']['PROOF_CONTROL_ROOT'], '1', '1', 'old'),
                                resolved(job['env']['PROOF_CONTROL_ROOT'], '2', '1', 'new'))
            self.assertNotEqual(resolved(job['env']['PROOF_OUTPUT_ROOT'], '1', '1', 'same'),
                                resolved(job['env']['PROOF_OUTPUT_ROOT'], '1', '2', 'same'))

if __name__ == '__main__':
    unittest.main()
