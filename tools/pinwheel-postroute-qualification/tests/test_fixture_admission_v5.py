import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from audits import sha
from run import fixture_admission

CASES = ['positive', 'removed-terminal', 'bridged-nets', 'macro-detached-signal', 'macro-bridged-signals', 'macro-detached-VSS']

class Admission(unittest.TestCase):
    def fixture(self, base):
        root = base / 'lvs-native-fixture-07'
        artifacts = {}
        sources = {}
        for case in CASES:
            for name in ['lvs.json', 'lvs.rpt', 'native.log', 'reference.v', 'run.lvs']:
                path = root / 'controls' / case / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('bound explicit host admission test evidence\n')
                artifacts[str(path.relative_to(root))] = sha(path)
                sources[str(path)] = sha(path)
        receipt = root / 'report.json'
        receipt.write_text(json.dumps({'status': 'passed', 'inputs_unchanged': True,
            'container_termination': {'status': 'absent'}, 'within_absolute_and_job_deadlines': True,
            'image_id': 'pinned-image', 'artifact_sha256': artifacts}))
        sources[str(receipt)] = sha(receipt)
        gate = base / 'semantic-gate.json'
        gate.write_text(json.dumps({'macro_connectivity_qualified': True, 'standardcell_sensitivity_qualified': True, 'source_sha256': sources}))
        return root, gate
    def test_bound_explicit_review_admission(self):
        with tempfile.TemporaryDirectory() as d:
            root, gate = self.fixture(Path(d))
            self.assertIn(str(gate.resolve()), fixture_admission(gate, sha(gate), 'pinned-image'))
    def test_macro_false_or_missing_gate_rejected(self):
        with self.assertRaises(AssertionError): fixture_admission(None, None, 'image')
        with tempfile.TemporaryDirectory() as d:
            root, gate = self.fixture(Path(d))
            data = json.loads(gate.read_text())
            data['macro_connectivity_qualified'] = False
            gate.write_text(json.dumps(data))
            with self.assertRaises(AssertionError): fixture_admission(gate, sha(gate), 'pinned-image')
    def test_changed_native_evidence_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root, gate = self.fixture(Path(d))
            (root / 'controls/macro-detached-VSS/lvs.json').write_text('changed')
            with self.assertRaisesRegex(AssertionError, 'Changed fixture'): fixture_admission(gate, sha(gate), 'pinned-image')
    def test_missing_case_or_changed_gate_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root, gate = self.fixture(Path(d))
            data = json.loads(gate.read_text())
            del data['source_sha256'][str(root / 'controls/macro-bridged-signals/native.log')]
            gate.write_text(json.dumps(data))
            with self.assertRaises(AssertionError): fixture_admission(gate, sha(gate), 'pinned-image')
            with self.assertRaisesRegex(AssertionError, 'Changed fixture semantic gate'): fixture_admission(gate, '0' * 64, 'pinned-image')

if __name__ == '__main__': unittest.main()
