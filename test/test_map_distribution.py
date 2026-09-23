"""Distribution must count real pins, preserve aliases and retain its evidence."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
from map_distribution import BUFFER, boundary_loads, distribute

spec = importlib.util.spec_from_file_location('distribution_check', SCRIPTS / 'check-map-tile.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def port(direction, bits):
    return {'direction': direction, 'bits': bits}


def instance(kind, connections, outputs):
    return {'type': kind, 'parameters': {}, 'attributes': {}, 'connections': connections,
            'port_directions': {p: 'output' if p in outputs else 'input' for p in connections}}


def fixture(count=4, weight=7, fixed=1):
    library = {'attributes': {'blackbox': '1', 'area': '7.2576'}, 'cells': {},
               'ports': {'A': port('input', [2]), 'X': port('output', [3])}}
    tile = {'ports': {'A': port('input', [2]), 'Y': port('output', list(range(3, 3 + weight)))},
            'cells': {f'load{k}': instance(BUFFER, {'A': [2], 'X': [3 + k]}, {'X'}) for k in range(weight)}}
    glue = {'ports': {'A': port('input', [2]), 'Y': port('output', [2])},
            'cells': {f'fixed{k}': instance(BUFFER, {'A': [2], 'X': [3 + k]}, {'X'}) for k in range(fixed)}}
    cells = {'glue': instance('glue', {'A': [3], 'Y': [4]}, {'Y'})}
    output_bits = []
    banks = {}
    for k in range(count):
        bits = list(range(5 + k * weight, 5 + (k + 1) * weight))
        output_bits.extend(bits)
        name = f'tile{k}'
        cells[name] = instance('tile', {'A': [4], 'Y': bits}, {'Y'})
        banks[name] = (k // (count // 2), k % (count // 2))
    top = {'ports': {'clk': port('input', [2]), 'data': port('input', [3]),
                     'out': port('output', output_bits)}, 'cells': cells, 'netnames': {}}
    return {'modules': {'top': top, 'tile': tile, 'glue': glue, BUFFER: library}}, banks


class DistributionChecks(unittest.TestCase):
    def test_counts_internal_pins_and_pass_through_aliases(self):
        data, banks = fixture()
        nets = boundary_loads(data['modules'], 'top')
        net = next(n for n in nets if n['source'] == 'data[0]')
        self.assertEqual(net['loads'], 29)
        self.assertEqual(net['fixed_loads'], 1)
        self.assertEqual([e['weight'] for e in net['endpoints']], [7] * 4)
        saved = deepcopy(data)
        candidate, receipt = distribute(data, 'top', banks)
        self.assertEqual(data, saved)
        self.assertEqual(receipt['added_buffers'], 4)
        self.assertEqual(receipt['added_area_um2'], 29.0304)
        self.assertEqual(receipt['trees'][0]['root_sink_pins'], 5)
        self.assertLessEqual(max(n['loads'] for n in boundary_loads(candidate['modules'], 'top')), 10)
        for name in ('tile', 'glue', BUFFER):
            self.assertEqual(candidate['modules'][name], data['modules'][name])
        self.assertEqual(candidate['modules']['top']['cells']['glue'], data['modules']['top']['cells']['glue'])
        self.assertEqual(candidate['modules']['top']['ports'], data['modules']['top']['ports'])
        self.assertFalse(set(candidate['modules']['top']['cells']) & set(candidate['modules']['top']['netnames']))

    def test_multiple_levels_and_fixed_root_load(self):
        data, banks = fixture(count=32, fixed=7)
        candidate, receipt = distribute(data, 'top', banks)
        self.assertEqual(receipt['added_buffers'], 38)
        self.assertEqual(receipt['trees'][0]['maximum_added_levels'], 3)
        self.assertEqual(receipt['trees'][0]['root_sink_pins'], 9)
        self.assertTrue(all(n['loads'] <= 10 for n in boundary_loads(candidate['modules'], 'top')))

    def test_leaf_groups_keep_banks_separate(self):
        data, banks = fixture(count=8, weight=2)
        candidate, receipt = distribute(data, 'top', banks)
        self.assertEqual(receipt['added_buffers'], 2)
        self.assertEqual([b['sink_pins'] for b in receipt['trees'][0]['buffers']], [8, 8])
        wires = [candidate['modules']['top']['cells'][f'tile{k}']['connections']['A'][0] for k in range(8)]
        self.assertEqual(len(set(wires[:4])), 1)
        self.assertEqual(len(set(wires[4:])), 1)
        self.assertNotEqual(wires[0], wires[4])

    def test_no_buffer_when_budget_already_met(self):
        data, banks = fixture(count=2, weight=2)
        candidate, receipt = distribute(data, 'top', banks)
        self.assertEqual(candidate, data)
        self.assertEqual(receipt['added_buffers'], 0)

    def test_reject_unrepairable_boundary(self):
        for weight, fixed in ((11, 1), (7, 10)):
            with self.subTest(weight=weight, fixed=fixed):
                data, banks = fixture(weight=weight, fixed=fixed)
                with self.assertRaisesRegex(ValueError, 'Cannot meet budget'):
                    distribute(data, 'top', banks)
        for limit in (0, 1, True, 1.5):
            data, banks = fixture()
            with self.assertRaisesRegex(ValueError, 'at least two'):
                distribute(data, 'top', banks, limit)

    def test_reject_ambiguous_driver_unknown_and_port_mismatch(self):
        for mutate in (
                lambda t: t['ports'].__setitem__('second_driver', port('input', [4])),
                lambda t: t['cells']['tile0']['connections'].__setitem__('A', ['x']),
                lambda t: t['cells']['tile0']['connections'].__setitem__('A', ['z']),
                lambda t: t['cells']['tile0']['connections'].__setitem__('A', [4, 4]),
                lambda t: t['cells']['tile0']['port_directions'].__setitem__('A', 'output')):
            data, banks = fixture()
            mutate(data['modules']['top'])
            with self.assertRaises(ValueError):
                distribute(data, 'top', banks)

    def test_whole_chip_budget_includes_fixed_macro_and_direct_logic_pins(self):
        data, banks = fixture(count=4, weight=2)
        top = data['modules']['top']
        # A producer serves tile inputs, controller gates and two SRAM pins.
        # Macro outputs here are unused; the load/driver accounting is generic.
        fixed = {'memory0', 'memory1'}
        for k, name in enumerate(['memory0', 'memory1', 'engine0', 'engine1']):
            top['cells'][name] = instance(BUFFER, {'A': [3], 'X': [50 + k]}, {'X'})
        saved = deepcopy(data)
        candidate, receipt = distribute(data, 'top', banks, fixed_cells=fixed)
        self.assertEqual(data, saved)
        tree = next(t for t in receipt['trees'] if t['source'] == 'data[0]')
        self.assertEqual(tree['original_sink_pins'], 13)
        self.assertEqual(tree['fixed_sink_pins'], 3)
        for name in fixed:
            self.assertEqual(candidate['modules']['top']['cells'][name], top['cells'][name])
        self.assertLessEqual(max(n['loads'] for n in boundary_loads(candidate['modules'], 'top', fixed)), 10)
        for name in ('tile', 'glue', BUFFER):
            self.assertEqual(candidate['modules'][name], data['modules'][name])
        with self.assertRaisesRegex(ValueError, 'Unknown fixed'):
            distribute(data, 'top', banks, fixed_cells={'missing_macro'})

    def test_constant_tieoffs_and_scope_metadata_are_preserved(self):
        data, banks = fixture()
        top = data['modules']['top']
        top['cells']['tile0']['connections']['A'] = ['0']
        top['cells']['tieoff'] = instance(BUFFER, {'A': ['1'], 'X': [90]}, {'X'})
        top['ports']['fixed_out'] = port('output', ['0', '1'])
        top['cells']['scope'] = {'type': '$scopeinfo', 'connections': {}, 'port_directions': {}}
        candidate, _ = distribute(data, 'top', banks)
        for name in ('tile0', 'tieoff', 'scope'):
            self.assertEqual(candidate['modules']['top']['cells'][name], top['cells'][name])
        self.assertEqual(candidate['modules']['top']['ports'], top['ports'])
        self.assertLessEqual(max(n['loads'] for n in boundary_loads(candidate['modules'], 'top')), 10)

    def test_reject_inconsistent_constant_alias_and_driven_constant(self):
        for target, value in [('glue', '0'), ('glue', '1'), ('tile0', '0')]:
            data, banks = fixture()
            # The glue's Y aliases its live A; the tile's Y is a real driver.
            data['modules']['top']['cells'][target]['connections']['Y'][0] = value
            with self.assertRaisesRegex(ValueError, 'constant'):
                distribute(data, 'top', banks)

    def test_reject_second_distribution_and_invalid_area(self):
        data, banks = fixture()
        candidate, _ = distribute(data, 'top', banks)
        with self.assertRaisesRegex(ValueError, 'already present'):
            distribute(candidate, 'top', banks)
        data['modules'][BUFFER]['attributes']['area'] = 'nan'
        with self.assertRaisesRegex(ValueError, 'Invalid buffer area'):
            distribute(data, 'top', banks)

    def test_separate_probe_prefix_coexists_with_previous_tree(self):
        data, banks = fixture(count=32)
        first, _ = distribute(data, 'top', banks)
        # The stricter probe may coexist with the retained structural tree.
        second, receipt = distribute(first, 'top', banks, 8, prefix='electrical_distribution_')
        self.assertGreater(receipt['added_buffers'], 0)
        self.assertEqual(first['modules']['tile'], second['modules']['tile'])
        self.assertTrue(all(n['loads'] <= 8 for n in boundary_loads(second['modules'], 'top')))
        for prefix in ('', 'bad name', '1prefix', 'bad;prefix'):
            with self.subTest(prefix=prefix), self.assertRaisesRegex(ValueError, 'Invalid distribution'):
                distribute(data, 'top', banks, prefix=prefix)

    def test_reject_stale_sources_artifacts_tools_and_receipts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ('hardware.lean', 'mapped.json', 'tool'):
                (root / name).write_text(name)
            baseline = {'status': 'passed', 'variants': {},
                        'inputs_sha256': {'hardware.lean': check.sha(root / 'hardware.lean')},
                        'artifacts_sha256': {'mapped.json': check.sha(root / 'mapped.json')},
                        'tools_sha256': {'tool': check.sha(root / 'tool')}}
            check.write_json(root / 'report.json', baseline)
            selected = {'report': 'report.json', 'report_sha256': check.sha(root / 'report.json'), 'variants': {}}
            check.write_json(root / 'selected.json', selected)
            with patch.object(check, 'ROOT', root):
                self.assertEqual(check.load_baseline(root / 'selected.json')[1], baseline)
                for name in ('hardware.lean', 'mapped.json', 'tool', 'report.json'):
                    with self.subTest(name=name):
                        path = root / name
                        saved = path.read_text()
                        path.write_text(saved + 'changed')
                        with self.assertRaises(ValueError):
                            check.load_baseline(root / 'selected.json')
                        path.write_text(saved)
                selected['variants'] = {'wrong': True}
                check.write_json(root / 'selected.json', selected)
                with self.assertRaisesRegex(ValueError, 'selected passing'):
                    check.load_baseline(root / 'selected.json')


if __name__ == '__main__':
    unittest.main()
