import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_timing_acceptance import assess_timing


class TimingAcceptanceTest(unittest.TestCase):
    def setUp(self):
        self.corners = ['nom_typ_1p20V_25C', 'nom_slow_1p08V_125C', 'nom_fast_1p32V_m40C']
        self.metrics = {}
        for corner in self.corners:
            for name, value in {
                'timing__setup__ws': 1.0, 'timing__hold__ws': .02,
                'timing__setup_vio__count': 0, 'timing__hold_vio__count': 0,
                'design__max_cap_violation__count': 0,
                'design__max_slew_violation__count': 0,
                'design__max_fanout_violation__count': 0,
            }.items():
                self.metrics[name + '__corner:' + corner] = value

    def test_complete_positive_control(self):
        self.assertEqual(assess_timing(self.metrics, self.corners)['status'], 'passed')

    def test_each_corner_cannot_hide_behind_passing_aggregate(self):
        for corner in self.corners:
            for metric, value in [
                ('timing__setup__ws', -.1), ('timing__hold__ws', -.01),
                ('timing__setup_vio__count', 1), ('timing__hold_vio__count', 1),
                ('design__max_cap_violation__count', 1),
                ('design__max_slew_violation__count', 1),
                ('design__max_fanout_violation__count', 14),
            ]:
                with self.subTest(corner=corner, metric=metric):
                    changed = dict(self.metrics, **{metric: 0})
                    changed[metric + '__corner:' + corner] = value
                    result = assess_timing(changed, self.corners)
                    self.assertEqual(result['status'], 'rejected')
                    self.assertEqual(len(result['failures']), 1)

    def test_missing_corner_is_not_a_pass(self):
        changed = {k:v for k,v in self.metrics.items() if not k.endswith(self.corners[2])}
        with self.assertRaisesRegex(ValueError, 'required corner metric'):
            assess_timing(changed, self.corners)

    def test_invalid_numbers_are_not_a_pass(self):
        for value in [None, True, '0', float('nan'), float('inf'), -.1, .5]:
            with self.subTest(value=value):
                changed = copy.deepcopy(self.metrics)
                changed['design__max_cap_violation__count__corner:' + self.corners[0]] = value
                with self.assertRaises(ValueError):
                    assess_timing(changed, self.corners)

    def test_explicit_corner_contract(self):
        for corners in [[], ['a', 'a'], [''], 'nom_typ_1p20V_25C', [None]]:
            with self.subTest(corners=corners), self.assertRaises(ValueError):
                assess_timing(self.metrics, corners)


if __name__ == '__main__':
    unittest.main()
