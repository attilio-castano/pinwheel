"""Fail-closed checks for the experimental core's exact state intake."""
from copy import deepcopy
from pathlib import Path
import runpy
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
core_cut = runpy.run_path(str(ROOT / 'scripts/check-paired-validation.py'))['core_cut']


def fixture():
    registers = [dict(name='r_boot_b0', reference='r_boot_b0', width=32),
                 dict(name='r_cursor', reference='r_cursor', width=9)]
    module = dict(attributes={}, ports={'clk': dict(direction='input', bits=[2]),
        'value': dict(direction='output', bits=[10])}, netnames={}, cells={})
    for name, bits in [('clk', [2]), ('value', [10]), ('r_boot_b0', list(range(10, 40))),
                       ('r_cursor', list(range(40, 49)))]:
        module['netnames'][name] = dict(hide_name=0, bits=bits, attributes={})
    for q in range(10, 49):
        module['cells'][f'ff{q}'] = dict(type='$_DFF_P_', hide_name=0, parameters={}, attributes={},
            connections={'C': [2], 'D': ['0'], 'Q': [q]},
            port_directions={'C': 'input', 'D': 'input', 'Q': 'output'})
    return module, dict(inputs=[], outputs=[dict(name='value', width=1)], registers=registers)


class CoreIntakeTests(unittest.TestCase):
    def test_only_dead_reserved_coordinates_are_added(self):
        module, description = fixture()
        original = deepcopy(module)
        cut, projection = core_cut(module, description)
        self.assertEqual(module, original)
        self.assertEqual(projection['logical_state_bits'], 41)
        self.assertEqual(projection['physical_flip_flops'], 39)
        self.assertEqual(projection['pruned_state_positions'], [30, 31])
        self.assertEqual(cut['ports']['next_state']['bits'][30:32], ['0', '0'])

    def test_missing_live_state_is_rejected(self):
        module, description = fixture()
        module['netnames']['r_cursor']['bits'].pop()
        with self.assertRaisesRegex(ValueError, 'Unexpected trimmed core state'):
            core_cut(module, description)

    def test_reserved_unknown_with_a_live_use_is_rejected(self):
        module, description = fixture()
        module['netnames']['r_boot_b0']['bits'] += ['x', 'x']
        module['cells']['ff10']['connections']['D'] = ['x']
        with self.assertRaisesRegex(ValueError, 'Unknown value in live core logic'):
            core_cut(module, description)

    def test_hidden_flip_flop_is_rejected(self):
        module, description = fixture()
        module['cells']['hidden'] = deepcopy(module['cells']['ff10'])
        module['cells']['hidden']['connections']['Q'] = [100]
        with self.assertRaisesRegex(ValueError, 'exact physical FF bijection'):
            core_cut(module, description)


if __name__ == '__main__':
    unittest.main()
