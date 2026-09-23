"""Cheap negative controls for the paired chip's macro and state boundary."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from paired_mapping import MACRO, binding, cut


def fixture():
    inputs = {'x': [3], 'mem_q0': list(range(100, 164))}
    outputs = {'y': [4], 'mem_addr0': ['0'] * 9, 'mem_data': ['0'] * 64,
               'mem_write': ['0'], 'mem_read': ['1']}
    module = {
        'ports': {'clk': {'direction': 'input', 'bits': [2]},
                  'x': {'direction': 'input', 'bits': [3]},
                  'y': {'direction': 'output', 'bits': [4]}},
        'netnames': {'controller.' + n: {'bits': list(bs)}
                     for n, bs in (inputs | outputs).items()},
        'cells': {'ff': {'type': '$_DFF_P_',
                         'connections': {'C': [2], 'D': [3], 'Q': [4]},
                         'port_directions': {'C': 'input', 'D': 'input', 'Q': 'output'}}},
    }
    description = {'inputs': [{'name': n, 'width': len(bs)} for n, bs in inputs.items()],
                   'outputs': [{'name': n, 'width': len(bs)} for n, bs in outputs.items()],
                   'registers': []}
    for name in ['r_boot_b0', 'r_boot_b1', 'r_current']:
        description['registers'].append({'name': name, 'reference': name, 'width': 32})
        bits = ['0'] * 30 + ['x', 'x']
        if name == 'r_current':
            bits[0] = 4
        module['netnames']['controller.' + name] = {'bits': bits}
    pins = dict(A_CLK=[2], A_MEN=['1'], A_DLY=['1'],
                A_ADDR=outputs['mem_addr0'], A_DIN=outputs['mem_data'], A_DOUT=inputs['mem_q0'],
                A_WEN=outputs['mem_write'], A_REN=outputs['mem_read'], A_BM=['1'] * 64,
                A_BIST_CLK=['0'], A_BIST_EN=['0'], A_BIST_MEN=['0'], A_BIST_WEN=['0'],
                A_BIST_REN=['0'], A_BIST_ADDR=['0'] * 9, A_BIST_DIN=['0'] * 64,
                A_BIST_BM=['0'] * 64)
    module['cells']['memory.storage'] = {
        'type': MACRO, 'connections': deepcopy(pins),
        'port_directions': {p: 'output' if p == 'A_DOUT' else 'input' for p in pins},
    }
    return module, description


class PairedIntakeChecks(unittest.TestCase):
    def test_unused_reserved_bits_are_explicit_and_inputs_are_unchanged(self):
        module, desc = fixture()
        saved = deepcopy((module, desc))
        result, projection = cut(module, desc)
        self.assertEqual((module, desc), saved)
        self.assertNotIn('memory.storage', result['cells'])
        self.assertEqual(projection['physical_flip_flops'], 1)
        self.assertEqual(projection['logical_state_bits'], 96)
        self.assertEqual(projection['pruned_state_positions'], [30, 31, 62, 63, 94, 95])
        self.assertEqual(len(projection['unused_reserved_x_coordinates']), 6)
        self.assertEqual(result['ports']['mem_q0']['bits'], list(range(100, 164)))

    def test_every_macro_terminal_is_bound(self):
        original, desc = fixture()
        for pin in original['cells']['memory.storage']['connections']:
            with self.subTest(pin=pin):
                module = deepcopy(original)
                module['cells']['memory.storage']['connections'][pin][0] = 900
                with self.assertRaisesRegex(ValueError, 'changed paired macro terminal'):
                    binding(module, desc)

    def test_macro_count_kind_and_terminal_width(self):
        for mutation in ['extra', 'missing', 'kind', 'width', 'direction']:
            with self.subTest(mutation=mutation):
                module, desc = fixture()
                cell = module['cells']['memory.storage']
                if mutation == 'extra':
                    module['cells']['other.storage'] = deepcopy(cell)
                elif mutation == 'missing':
                    del module['cells']['memory.storage']
                elif mutation == 'kind':
                    cell['type'] = MACRO.replace('512x64', '64x64')
                elif mutation == 'width':
                    cell['connections']['A_ADDR'].pop()
                else:
                    cell['port_directions']['A_DOUT'] = 'input'
                with self.assertRaises(ValueError):
                    cut(module, desc)

    def test_package_alias_cannot_hide_changed_pin(self):
        module, desc = fixture()
        module['ports']['y']['bits'] = [900]
        with self.assertRaisesRegex(ValueError, 'paired package boundary mismatch'):
            cut(module, desc)

    def test_unknown_live_cell_inputs_are_never_pruned(self):
        for value in ['x', 'z']:
            module, desc = fixture()
            module['cells']['ff']['connections']['D'] = [value]
            with self.assertRaisesRegex(ValueError, 'unknown value in live paired logic'):
                cut(module, desc)

    def test_unknown_live_output_is_never_pruned(self):
        module, desc = fixture()
        module['ports']['y']['bits'] = ['x']
        module['netnames']['controller.y']['bits'] = ['x']
        with self.assertRaisesRegex(ValueError, 'unknown value in live paired logic'):
            cut(module, desc)

    def test_unknown_nonreserved_state_coordinate_is_rejected(self):
        module, desc = fixture()
        module['netnames']['controller.r_current']['bits'][29] = 'x'
        with self.assertRaisesRegex(ValueError, 'unexpected unknown paired state coordinate'):
            cut(module, desc)

    def test_disappearing_or_aliased_physical_state_is_rejected(self):
        for value in ['0', 4]:
            module, desc = fixture()
            bits = module['netnames']['controller.r_current']['bits']
            bits[0 if value == '0' else 1] = value
            with self.assertRaisesRegex(ValueError, 'exact physical FF bijection'):
                cut(module, desc)


if __name__ == '__main__':
    unittest.main()
