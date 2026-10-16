import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from audits import sha, write
from bind import FILES, admitted_sources, verify_admission


class Binding(unittest.TestCase):
    def fixture(self, root):
        after = root / 'after'
        after.mkdir()
        for name in FILES:
            (after / name).write_text('fixture:' + name)
        core, sdc = root / 'core.json', root / 'core.sdc'
        core.write_text('{}')
        sdc.write_text('create_clock -period 20 [get_ports clk]\n')
        receipt = root / 'report.json'
        write(receipt, {'status': 'passed', 'inputs_unchanged': True,
            'container_termination': {'status': 'absent'}, 'within_absolute_and_job_deadlines': True,
            'artifact_sha256': {str(p.relative_to(root)): sha(p) for p in after.iterdir()}})
        gate = root / 'adjudication.json'
        write(gate, {'stage_execution_and_scope_gate_passed': True})
        return after, receipt, gate, core, sdc

    def test_completed_source_and_proof_binding(self):
        with tempfile.TemporaryDirectory() as d:
            paths = self.fixture(Path(d))
            binding = admitted_sources(*paths)
            self.assertTrue(verify_admission(binding)['producer_and_scope_admitted'])
            self.assertEqual(len(binding['source_sha256']), 9)
            self.assertFalse(binding['route_admission']['physical_acceptance_claim'])

    def test_failed_scope_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            paths = self.fixture(Path(d))
            write(paths[2], {'stage_execution_and_scope_gate_passed': False})
            with self.assertRaises(AssertionError):
                admitted_sources(*paths)

    def test_changed_after_checkpoint_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            paths = self.fixture(Path(d))
            binding = admitted_sources(*paths)
            (paths[0] / 'checkpoint.odb').write_text('different')
            with self.assertRaises(AssertionError):
                verify_admission(binding)

    def test_changed_adjudication_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            paths = self.fixture(Path(d))
            binding = admitted_sources(*paths)
            write(paths[2], {'stage_execution_and_scope_gate_passed': True, 'changed': True})
            with self.assertRaises(AssertionError):
                verify_admission(binding)

    def test_unsettled_or_invalidated_producer_rejected(self):
        for change in [{'status': 'running'}, {'inputs_unchanged': False},
                       {'container_termination': {'status': 'unconfirmed'}},
                       {'within_absolute_and_job_deadlines': False}]:
            with tempfile.TemporaryDirectory() as d:
                paths = self.fixture(Path(d))
                receipt = json.loads(paths[1].read_text())
                receipt.update(change)
                write(paths[1], receipt)
                with self.assertRaises(AssertionError):
                    admitted_sources(*paths)


if __name__ == '__main__':
    unittest.main()
