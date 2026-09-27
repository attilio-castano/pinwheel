"""Reject incomplete state/binding evidence in the complete-chip comparison."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from tiled_chip import FF, MACRO, controller_wrapper, state_cut, project_pruned_state, macro_binding


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('check_tiled_chip', ROOT / 'scripts/check-tiled-chip.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class FanoutBudgetChecks(unittest.TestCase):
    def test_library_must_support_sink_count_as_electrical_budget(self):
        valid = 'default_max_fanout : 8.0; default_fanout_load : 1;'
        checker.require_unit_fanout_budget(valid, 8)
        for text in ('', valid.replace('8.0', '10'), valid.replace('load : 1', 'load : 2'),
                     valid + ' max_fanout : 6;', valid + ' fanout_load : 0.5;', valid + valid):
            with self.subTest(text=text), self.assertRaises(ValueError):
                checker.require_unit_fanout_budget(text, 8)

    def test_library_budget_rejects_incomplete_organization_before_running(self):
        result = subprocess.run([sys.executable, '-B', str(ROOT / 'scripts/check-tiled-chip.py'),
                                 '--tag', 'invalid-budget', '--fanout-limit', '8'],
                                cwd=ROOT, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 2)
        self.assertIn('requires the combined boundary', result.stderr)

    def test_flat_comparison_requires_aggregate_organization(self):
        result = subprocess.run([sys.executable, '-B', str(ROOT / 'scripts/check-tiled-chip.py'),
                                 '--tag', 'invalid-flat-comparison', '--compare-flat'],
                                cwd=ROOT, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 2)
        self.assertIn('requires the combined organization', result.stderr)


def cell(kind, pins, outputs):
    return {'type': kind, 'connections': deepcopy(pins),
            'port_directions': {p: 'output' if p in outputs else 'input' for p in pins}}


def fixture():
    module = {'ports': {'clk': {'direction': 'input', 'bits': [2]},
                        'x': {'direction': 'input', 'bits': [3]},
                        'y': {'direction': 'output', 'bits': [7]}},
              'netnames': {n: {'bits': [b]} for n, b in [('x', 3), ('y', 7), ('ra', 5), ('rb', 6), ('derived', 7), ('unused', 8)]},
              'cells': {'a': cell('$_DFF_P_', {'C': [2], 'D': [3], 'Q': [5]}, {'Q'}),
                        'b': cell('$_DFF_P_', {'C': [2], 'D': [5], 'Q': [6]}, {'Q'}),
                        'inv': cell('$_NOT_', {'A': [5], 'Y': [7]}, {'Y'})}}
    description = {'inputs': [{'name': 'x', 'width': 1}], 'outputs': [{'name': 'y', 'width': 1}],
                   'registers': [{'name': n, 'reference': n, 'width': 1} for n in ('ra', 'rb', 'derived', 'unused')]}
    return module, description


class TiledChipChecks(unittest.TestCase):
    def test_exact_state_projection_derived_bit_and_dead_bit(self):
        module, description = fixture()
        saved = deepcopy(module)
        cut, receipt = state_cut(module, description, False)
        self.assertEqual(module, saved)
        self.assertEqual(receipt, {'logical_state_bits': 4, 'physical_flip_flops': 2,
                                   'derived_or_constant_state_bits': 1, 'pruned_state_positions': [3]})
        self.assertEqual(cut['ports']['next_state']['bits'][:2], [3, 5])
        self.assertEqual(cut['ports']['next_state']['bits'][3], '0')
        cloned = cut['cells']['state_projection_inv']
        self.assertEqual(cloned['connections']['A'], [3])
        self.assertEqual(cloned['connections']['Y'], [cut['ports']['next_state']['bits'][2]])

    def test_missing_alias_and_extra_physical_state(self):
        for mutate in (lambda m: m['netnames'].pop('ra'),
                       lambda m: m['netnames'].__setitem__('rb', {'bits': [5]}),
                       lambda m: m['cells'].__setitem__('extra', cell('$_DFF_P_', {'C': [2], 'D': [3], 'Q': [99]}, {'Q'}))):
            module, description = fixture()
            mutate(module)
            with self.assertRaises(ValueError):
                state_cut(module, description, False)

    def test_pruned_projection_keeps_current_reference_inputs_arbitrary(self):
        module, description = fixture()
        candidate, projection = state_cut(module, description, True)
        reference = deepcopy(candidate)
        reference['ports']['next_state']['bits'][3] = 3
        saved = deepcopy(reference)
        projected = project_pruned_state(reference, candidate, projection, [3])
        self.assertEqual(reference, saved)
        self.assertEqual(projected['ports']['state'], reference['ports']['state'])
        self.assertEqual(projected['cells'], reference['cells'])
        self.assertEqual(projected['ports']['next_state']['bits'][:3], reference['ports']['next_state']['bits'][:3])
        self.assertEqual(projected['ports']['next_state']['bits'][3], '0')
        self.assertEqual(projected['netnames']['next_state']['bits'], projected['ports']['next_state']['bits'])

    def test_pruned_projection_rejects_changed_slots_and_live_uses(self):
        module, description = fixture()
        candidate, projection = state_cut(module, description, True)
        reference = deepcopy(candidate)
        with self.assertRaisesRegex(ValueError, 'mapped reference'):
            project_pruned_state(reference, candidate, projection, [])
        for output in (False, True):
            altered = deepcopy(candidate)
            if output:
                altered['ports']['y']['bits'] = [altered['ports']['state']['bits'][3]]
            else:
                altered['cells']['inv']['connections']['A'] = [altered['ports']['state']['bits'][3]]
            with self.assertRaisesRegex(ValueError, 'still has a use'):
                project_pruned_state(reference, altered, projection, [3])

    def test_pruned_bit_must_have_no_pin_use_or_external_port(self):
        for expose in (False, True):
            module, description = fixture()
            if expose:
                module['ports']['escape'] = {'direction': 'output', 'bits': [8]}
            else:
                module['cells']['inv']['connections']['A'] = [8]
            with self.assertRaises(ValueError):
                state_cut(module, description, False)

    def test_named_controller_ports_must_match_actual_ports(self):
        module, description = fixture()
        module['ports']['x']['bits'] = [99]
        with self.assertRaisesRegex(ValueError, 'actual external ports'):
            state_cut(module, description, False)

    def test_derived_state_cannot_depend_on_current_input_or_cycle(self):
        for bad in (3, 7, 'x'):
            module, description = fixture()
            module['cells']['inv']['connections']['A'] = [bad]
            with self.assertRaisesRegex(ValueError, 'Derived state depends'):
                state_cut(module, description, False)

    def test_clock_reset_and_unsupported_flop(self):
        for kind, pins in [(FF, {'CLK': [2], 'D': [3], 'Q': [5], 'RESET_B': ['0']}),
                           ('$_DFF_P_', {'C': [3], 'D': [3], 'Q': [5]}),
                           ('$_DFF_N_', {'C': [2], 'D': [3], 'Q': [5]})]:
            module, description = fixture()
            module['cells']['a'] = cell(kind, pins, {'Q'})
            with self.assertRaises(ValueError):
                state_cut(module, description, False)

    def test_typed_wrapper_connects_both_indices(self):
        _, description = fixture()
        mapping = {'inputs': [{'name': 'pc0', 'width': 8}, {'name': 'pc1', 'width': 8}],
                   'outputs': [{'name': 'index0', 'width': 5}, {'name': 'index1', 'width': 5}]}
        text = controller_wrapper('chip', description, mapping)
        self.assertIn('pinwheel_tiled_chip_logic engine (.*);', text)
        self.assertIn('.index0(map_index0)', text)
        self.assertIn('.index1(map_index1)', text)

    def test_macro_binding_checks_all_control_constants(self):
        module = {'ports': {'clk': {'direction': 'input', 'bits': [2]}}, 'cells': {}, 'netnames': {}}
        signals = {'mem_addr0': [3] * 6 + ['0'] * 3, 'mem_addr1': [4] * 6 + ['0'] * 3,
                   'mem_data': [5] * 64, 'mem_write': [6], 'mem_read': [7],
                   'mem_q0': list(range(8, 72)), 'mem_q1': list(range(72, 136))}
        module['netnames'] = {'controller.' + n: {'bits': bs} for n, bs in signals.items()}
        for b in range(2):
            pins = {'A_CLK': [2], 'A_MEN': ['1'], 'A_DLY': ['1'],
                    'A_ADDR': signals[f'mem_addr{b}'][:6], 'A_DIN': signals['mem_data'],
                    'A_DOUT': signals[f'mem_q{b}'], 'A_WEN': [6], 'A_REN': [7], 'A_BM': ['1'] * 64,
                    'A_BIST_CLK': ['0'], 'A_BIST_EN': ['0'], 'A_BIST_MEN': ['0'], 'A_BIST_WEN': ['0'],
                    'A_BIST_REN': ['0'], 'A_BIST_ADDR': ['0'] * 6, 'A_BIST_DIN': ['0'] * 64, 'A_BIST_BM': ['0'] * 64}
            module['cells'][f'memory.storage{b}'] = cell(MACRO, pins, {'A_DOUT'})
        self.assertEqual(len(macro_binding(module)), 2)
        for p in ('A_MEN', 'A_BM', 'A_BIST_EN', 'A_WEN', 'A_ADDR', 'A_DOUT'):
            altered = deepcopy(module)
            bits = altered['cells']['memory.storage1']['connections'][p]
            bits[0] = '1' if bits[0] == '0' else '0'
            with self.assertRaises(ValueError):
                macro_binding(altered)


if __name__ == '__main__':
    unittest.main()
