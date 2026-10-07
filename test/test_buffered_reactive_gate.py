"""Reject corrupted execution evidence at the Lean/Python comparison boundary."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('buffered_reactive_gate',
                                            ROOT / 'scripts/check-buffered-reactive.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def fixture():
    # Entry consumes/appends once. Two timed edges precede CHECKED, whose
    # terminal edge captures input1 and enters HALT without an extra wire edge.
    emit = lambda **fields: dict(kind='emit', instruction=fields)
    code = dict(kind='seq', first=emit(kind='shift', duration=2, shift_pin=0, append_input=0),
        rest=dict(kind='seq', first=emit(kind='checked', terminal_capture=[1, 0]),
                  rest=emit(kind='halt')))
    initial = dict(control='active', stop_reason=None, pc=0, remaining=1, wait_left=None,
        samples=[False] * 16, levels=1, enabled=7, sampler_first=3, sampler_second=3,
        phase='running', tx_consumed_bits=1, rx_bits=[True], outcome=None)
    first = dict(deepcopy(initial), remaining=0, sampler_first=0)
    second = dict(deepcopy(first), control='checked', pc=1, levels=0, sampler_second=0)
    third = dict(deepcopy(second), control='stopped', stop_reason='complete', pc=None,
                 remaining=None, phase='completed', outcome='complete')
    return dict(schema='pinwheel-buffered-reactive-vectors-v1', cases=[dict(
        name='entry-hold-terminal', program=dict(schedule=code, idle_levels=0,
        idle_enabled=7, virtual_span=3, stored_words=3, stored_nodes=5, loop_count=0, nesting=0),
        tx_capacity_bits=1, rx_capacity_bits=1, tx_bits=[True], rx_limit=1,
        tx_demand=1, rx_demand=1, initial_state=initial, incoming=[0, 0, 0],
        states=[first, second, third])])


class BufferedReactiveDifferentialTests(unittest.TestCase):
    def test_entry_hold_and_terminal_observations_match(self):
        report = gate.differential(fixture())
        self.assertEqual((report['cases'], report['initial_states'], report['edges'],
                          report['completed']), (1, 1, 3, 1))

    def test_each_changed_execution_observation_is_rejected(self):
        for field, value in (('control', 'waiting'), ('pc', 0), ('remaining', 1),
                             ('samples', [True] * 16), ('levels', 1), ('enabled', 0),
                             ('sampler_first', 3), ('sampler_second', 3),
                             ('phase', 'completed'), ('tx_consumed_bits', 0),
                             ('rx_bits', [False]), ('outcome', 'fault')):
            vectors = fixture()
            vectors['cases'][0]['states'][1][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(RuntimeError, 'execution mismatch'):
                gate.differential(vectors)

    def test_initial_entry_corruption_is_rejected(self):
        vectors = fixture()
        vectors['cases'][0]['initial_state']['tx_consumed_bits'] = 0
        with self.assertRaisesRegex(RuntimeError, 'initial-state mismatch'):
            gate.differential(vectors)

    def test_unbound_i2c_frontend_is_rejected(self):
        vectors = fixture()
        vectors['cases'][0]['name'] = 'i2c-four-byte-complete'
        with self.assertRaisesRegex(RuntimeError, 'factory geometry or admission mismatch'):
            gate.differential(vectors)

    def test_compact_geometry_corruption_is_rejected(self):
        for field in ('virtual_span', 'stored_words', 'stored_nodes', 'loop_count', 'nesting'):
            vectors = fixture()
            vectors['cases'][0]['program'][field] += 1
            with self.subTest(field=field), self.assertRaisesRegex(RuntimeError, 'geometry mismatch'):
                gate.differential(vectors)

    def test_terminal_outcome_or_raw_input_corruption_is_rejected(self):
        vectors = fixture()
        vectors['cases'][0]['states'][-1]['stop_reason'] = 'fault'
        with self.assertRaisesRegex(RuntimeError, 'execution mismatch'):
            gate.differential(vectors)
        vectors = fixture()
        vectors['cases'][0]['incoming'][0] = 3
        with self.assertRaisesRegex(RuntimeError, 'execution mismatch'):
            gate.differential(vectors)

    def test_unknown_schema_schedule_or_truncated_history_is_rejected(self):
        malformed = [dict(fixture(), schema='unknown'),
                     dict(schema='pinwheel-buffered-reactive-vectors-v1', cases=[])]
        vectors = fixture()
        vectors['cases'][0]['incoming'].pop()
        malformed.append(vectors)
        vectors = fixture()
        vectors['cases'][0]['program']['schedule']['kind'] = 'unknown'
        malformed.append(vectors)
        for vectors in malformed:
            with self.assertRaises(ValueError):
                gate.differential(vectors)


if __name__ == '__main__':
    unittest.main()
