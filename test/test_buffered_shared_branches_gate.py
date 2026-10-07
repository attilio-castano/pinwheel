"""Independent fixture translation and structural census checks."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
SPEC = importlib.util.spec_from_file_location('shared_branch_gate',
    ROOT / 'scripts/check-buffered-shared-branches.py')
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


class SharedBranchGateTests(unittest.TestCase):
    def fixture(self):
        return dict(cases=[dict(name='two-distinct-raw-descriptors', vectors=[
            dict(command=dict(initialize=1), raw_inputs=3),
            dict(command=dict(command=1, address=0, word=6, branch=1 << 55), raw_inputs=2),
            dict(command=dict(command=1, address=1, word=3), raw_inputs=1),
            dict(command=dict(command=2, count=2, virtual_span=2), raw_inputs=0)],
            checks=[dict(edge=3, state=dict(valid=1))])])

    def test_insertion_preserves_raw_descriptors_and_independent_expectation(self):
        source = self.fixture()
        saved = deepcopy(source)
        result = gate.convert_request(source)
        self.assertEqual(source, saved)
        case = result['cases'][0]
        self.assertEqual(len(case['vectors']), 20)
        self.assertEqual([v['command']['branch'] for v in case['vectors'][1:17]],
                         [1 << 55] + [0] * 15)
        self.assertEqual([v['raw_inputs'] for v in case['vectors'][1:17]], [2] * 16)
        self.assertEqual(case['vectors'][17]['command']['branch'], 0)
        self.assertEqual(case['vectors'][18]['command']['branch'], 1)
        self.assertEqual(case['checks'][-1], dict(edge=19, state=dict(valid=1)))

    def test_excess_unique_raw_descriptors_are_rejected(self):
        source = self.fixture()
        source['cases'][0]['vectors'] = [dict(command=dict(command=1, branch=k), raw_inputs=0)
                                         for k in range(17)]
        with self.assertRaisesRegex(RuntimeError, 'capacity'):
            gate.convert_request(source)

    def test_injected_upload_fixtures_require_complete_both_bank_coverage(self):
        cases = gate.upload_cases()
        self.assertEqual(len(cases), 5)
        for case in cases[:2]:
            failed = [c for c in case['checks'] if c['state'].get('rejected') == 1 and
                      c['state'].get('pending') == 1]
            self.assertEqual(len(failed), 2)
            self.assertEqual([c['state']['generation'] for c in failed], [0, 1])
        full = cases[-1]
        writes = [v['command']['branch'] for v in full['vectors'] if v['command'].get('command') == 6]
        self.assertEqual(len(set(writes)), 16)
        self.assertEqual(full['vectors'][-5]['command']['branch'], 15)

    def test_saved_cell_depth_counts_next_data_and_excludes_clock_fanout(self):
        module = dict(ports=dict(clk=dict(direction='input', bits=[2]),
                                x=dict(direction='input', bits=[3]),
                                y=dict(direction='output', bits=[6])), cells={
            'ff': dict(type='$_DFF_P_', connections=dict(C=[2], D=[5], Q=[4]),
                       port_directions=dict(C='input', D='input', Q='output')),
            'and': dict(type='$_AND_', connections=dict(A=[3], B=[4], Y=[5]),
                        port_directions=dict(A='input', B='input', Y='output')),
            'not': dict(type='$_NOT_', connections=dict(A=[5], Y=[6]),
                        port_directions=dict(A='input', Y='output'))})
        result = gate.structural_depth(dict(modules=dict(dut=module)), 'dut')
        self.assertEqual(result['next_state_depth'], 1)
        self.assertEqual(result['public_output_depth'], dict(y=2))
        self.assertEqual(result['maximum_data_signal_fanout'], 2)
        module['cells']['and']['connections']['A'] = [6]
        with self.assertRaisesRegex(RuntimeError, 'cycle'):
            gate.structural_depth(dict(modules=dict(dut=module)), 'dut')


if __name__ == '__main__':
    unittest.main()
