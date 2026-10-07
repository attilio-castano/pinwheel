"""Ensure the differential gate rejects corrupt evidence, not just bad programs."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('buffered_gate', ROOT / 'scripts/check-buffered-transfers.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def fixture():
    preparing = dict(phase='preparing', epoch=0, next_sequence=2, identity=[0, 1],
        program_generation=17, tx_bits=[True], tx_consumed_bits=0, rx_limit=1,
        rx_bits=[], outcome=None, reply=dict(accepted=True, reason=None, tx_bit=None))
    running = deepcopy(preparing)
    running['phase'] = 'running'
    consumed = deepcopy(running)
    consumed['tx_consumed_bits'] = 1
    consumed['reply']['tx_bit'] = True
    stale = deepcopy(consumed)
    stale['reply'] = dict(accepted=False, reason='wrong_identity', tx_bit=None)
    return dict(schema='pinwheel-transfer-vectors-v1', cases=[dict(
        tx_capacity_bits=1, rx_capacity_bits=1,
        commands=[dict(kind='prepare', program_generation=17, tx_bits=[True], rx_limit=1),
                  dict(kind='start', epoch=0, sequence=1, program_generation=17),
                  dict(kind='consume', epoch=0, sequence=1),
                  dict(kind='release', epoch=0, sequence=2)],
        states=[preparing, running, consumed, stale])])


class BufferedDifferentialGateTests(unittest.TestCase):
    def test_known_state_and_reply_observations_match(self):
        report = gate.differential(fixture())
        self.assertEqual((report['cases'], report['edges'], report['rejected_edges']), (1, 4, 1))

    def test_each_changed_ownership_observation_is_rejected(self):
        for field, value in (('phase', 'completed'), ('identity', [0, 2]),
                             ('tx_consumed_bits', 0), ('rx_bits', [True]),
                             ('program_generation', 18), ('tx_bits', [False])):
            vectors = fixture()
            vectors['cases'][0]['states'][2][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(RuntimeError, 'ownership mismatch'):
                gate.differential(vectors)

    def test_reply_and_rejection_reason_corruption_is_rejected(self):
        for reply in (dict(accepted=True, reason=None, tx_bit=None),
                      dict(accepted=False, reason='wrong_phase', tx_bit=None)):
            vectors = fixture()
            vectors['cases'][0]['states'][3]['reply'] = reply
            with self.assertRaisesRegex(RuntimeError, 'ownership mismatch'):
                gate.differential(vectors)

    def test_bad_schema_or_empty_or_truncated_history_is_rejected(self):
        malformed = [dict(fixture(), schema='unknown'),
                     dict(schema='pinwheel-transfer-vectors-v1', cases=[])]
        vectors = fixture()
        vectors['cases'][0]['states'].pop()
        malformed.append(vectors)
        for vectors in malformed:
            with self.assertRaises(ValueError):
                gate.differential(vectors)

    def test_unknown_command_is_rejected(self):
        vectors = fixture()
        vectors['cases'][0]['commands'][0]['kind'] = 'unknown'
        with self.assertRaisesRegex(ValueError, 'Unknown exported'):
            gate.differential(vectors)


if __name__ == '__main__':
    unittest.main()
