"""Hierarchy admission and exact pin identity, independent of CAD tools."""
from copy import deepcopy
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from synthesis_hierarchy import HierarchyPolicy, TOP, TILE, tiled_policy, mapped_view, check_hierarchy, check_flattening


def port(direction, *bits):
    return dict(direction=direction, bits=list(bits))


def cell(kind, **pins):
    return dict(type=kind, parameters={}, connections={p: list(v) for p, v in pins.items()},
                port_directions={p: 'output' if p in ('z', 'Q') else 'input' for p in pins})


def fixture():
    ff = dict(attributes={'blackbox': '1'}, ports={
        'CLK': port('input', 2), 'D': port('input', 3), 'RESET_B': port('input', 4), 'Q': port('output', 5)})
    ports = dict(clk=port('input', 2), a=port('input', 3), z=port('output', 9))
    block = dict(ports=dict(clk=port('input', 2), a=port('input', 3), z=port('output', 4)),
                 cells={'reg': cell('ff', CLK=[2], D=[3], RESET_B=['1'], Q=[4])})
    tree = dict(modules={'ff': ff, 'block': block, TOP: dict(ports=ports, cells={
        'left': cell('block', clk=[2], a=[3], z=[4]),
        'right': cell('block', clk=[2], a=[4], z=[9])})})
    flat = dict(modules={'ff': deepcopy(ff), TOP: dict(ports=deepcopy(ports), cells={
        'left.reg': cell('ff', CLK=[2], D=[3], RESET_B=['1'], Q=[4]),
        'right.reg': cell('ff', CLK=[2], D=[4], RESET_B=['1'], Q=[9])})})
    return tree, flat


POLICY = HierarchyPolicy('test-regions', 'Two independently owned state regions.',
                         True, ('block',), (('left', 'block'), ('right', 'block')))


class HierarchyChecks(unittest.TestCase):
    def test_same_pin_graph_with_independent_wire_numbers(self):
        tree, flat = fixture()
        saved = deepcopy(tree)
        for p in flat['modules'][TOP]['ports'].values():
            p['bits'] = [b + 100 for b in p['bits']]
        for c in flat['modules'][TOP]['cells'].values():
            c['connections'] = {p: [b + 100 if type(b) is int else b for b in bs]
                                for p, bs in c['connections'].items()}
        receipt = check_flattening(tree, flat)
        self.assertTrue(receipt['connection_identity'])
        self.assertEqual(receipt['leaf_cells'], 2)
        self.assertEqual(receipt['leaf_owners']['left.reg']['instance_path'], 'left')
        self.assertEqual(tree, saved)
        self.assertEqual(check_hierarchy(tree, POLICY)['retained_instances'], dict(POLICY.retained_instances))

    def test_rejects_missing_extra_and_changed_regions(self):
        for mutation in ('missing', 'extra', 'changed'):
            tree, _ = fixture()
            if mutation == 'missing':
                del tree['modules'][TOP]['cells']['right']
            elif mutation == 'extra':
                tree['modules'][TOP]['cells']['extra'] = deepcopy(tree['modules'][TOP]['cells']['left'])
            else:
                tree['modules']['other'] = deepcopy(tree['modules']['block'])
                tree['modules'][TOP]['cells']['right']['type'] = 'other'
            with self.subTest(mutation=mutation), self.assertRaisesRegex(ValueError, 'differs from policy'):
                check_hierarchy(tree, POLICY)

    def test_private_cell_names_retain_each_instance_scope(self):
        tree, flat = fixture()
        tree['modules']['block']['cells']['$private'] = tree['modules']['block']['cells'].pop('reg')
        for name in ('left', 'right'):
            flat['modules'][TOP]['cells']['$flatten\\' + name + '.$private'] = flat['modules'][TOP]['cells'].pop(name + '.reg')
        receipt = check_flattening(tree, flat)
        self.assertEqual(receipt['leaf_owners']['$flatten\\right.$private']['instance_path'], 'right')

    def test_verilog_readback_requires_exact_export_name_conversion(self):
        tree, flat = fixture()
        tree['modules']['block']['cells']['$private'] = tree['modules']['block']['cells'].pop('reg')
        for name in ('left', 'right'):
            flat['modules'][TOP]['cells']['\\$flatten\\' + name + '.$private'] = flat['modules'][TOP]['cells'].pop(name + '.reg')
        receipt = check_flattening(tree, flat, verilog_readback=True)
        owner = receipt['leaf_owners']['\\$flatten\\right.$private']
        self.assertEqual(owner['instance_path'], 'right')
        self.assertEqual(owner['flattened_cell'], '$flatten\\right.$private')
        self.assertTrue(receipt['verilog_readback'])
        for mutation in ('clock', 'rename', 'unescaped'):
            changed = deepcopy(flat)
            cells = changed['modules'][TOP]['cells']
            name = '\\$flatten\\right.$private'
            if mutation == 'clock':
                cells[name]['connections']['CLK'] = ['0']
            else:
                cells[name[1:] if mutation == 'unescaped' else 'renamed'] = cells.pop(name)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                check_flattening(tree, changed, verilog_readback=True)

    def test_verilog_readback_rejects_name_encoding_collision(self):
        _, flat = fixture()
        cells = flat['modules'][TOP]['cells']
        cells['$private'] = cells.pop('left.reg')
        cells['\\$private'] = cells.pop('right.reg')
        with self.assertRaisesRegex(ValueError, 'Ambiguous Verilog'):
            check_flattening(flat, flat, verilog_readback=True)

    def test_rejects_changed_clock_reset_data_and_cell_identity(self):
        for pin in ('CLK', 'RESET_B', 'D', 'Q', 'name', 'type'):
            tree, flat = fixture()
            cells = flat['modules'][TOP]['cells']
            if pin == 'name':
                cells['renamed'] = cells.pop('left.reg')
            elif pin == 'type':
                flat['modules']['other_ff'] = deepcopy(flat['modules']['ff'])
                cells['left.reg']['type'] = 'other_ff'
            else:
                cells['left.reg']['connections'][pin] = ['0']
            with self.subTest(pin=pin), self.assertRaises(ValueError):
                check_flattening(tree, flat)

    def test_rejects_incomplete_or_changed_interfaces(self):
        for mutation in ('missing', 'width', 'direction', 'parameter'):
            tree, _ = fixture()
            c = tree['modules'][TOP]['cells']['left']
            if mutation == 'missing':
                del c['connections']['clk']
            elif mutation == 'width':
                c['connections']['a'].append(7)
            elif mutation == 'direction':
                c['port_directions']['a'] = 'output'
            else:
                c['parameters']['INIT'] = '1'
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                mapped_view(tree)

    def test_aliases_across_pass_through_module(self):
        tree, flat = fixture()
        tree['modules']['alias'] = dict(ports={'a': port('input', 2), 'z': port('output', 2)}, cells={})
        tree['modules'][TOP]['cells']['wire'] = cell('alias', a=[3], z=[6])
        tree['modules'][TOP]['cells']['left']['connections']['a'] = [6]
        self.assertTrue(check_flattening(tree, flat)['connection_identity'])
        tree['modules'][TOP]['cells']['wire']['connections'] = dict(a=['0'], z=['1'])
        with self.assertRaisesRegex(ValueError, 'Conflicting constant'):
            mapped_view(tree)

    def test_rejects_recursive_and_unresolved_modules(self):
        for kind in ('missing', TOP):
            tree, _ = fixture()
            tree['modules'][TOP]['cells']['left']['type'] = kind
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                mapped_view(tree)

    def test_rejects_unknown_signals_and_hidden_implementation(self):
        for mutation in ('unknown', 'process', 'blackbox'):
            tree, _ = fixture()
            if mutation == 'unknown':
                tree['modules'][TOP]['cells']['left']['connections']['a'] = ['x']
            elif mutation == 'process':
                tree['modules']['block']['processes'] = {'unmapped': {}}
            else:
                tree['modules']['ff']['cells'] = {'hidden': {}}
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                mapped_view(tree)

    def test_flat_view_requires_no_remaining_modules(self):
        tree, _ = fixture()
        with self.assertRaisesRegex(ValueError, 'still contains hierarchy'):
            check_flattening(tree, tree)

    def test_rejects_ambiguous_flat_names(self):
        tree, flat = fixture()
        tree['modules'][TOP]['cells']['left.reg'] = flat['modules'][TOP]['cells']['left.reg']
        with self.assertRaisesRegex(ValueError, 'Ambiguous'):
            mapped_view(tree)

    def test_scope_metadata_cannot_hide_connections(self):
        tree, flat = fixture()
        scope = dict(type='$scopeinfo', connections={})
        tree['modules'][TOP]['cells']['metadata'] = scope
        self.assertTrue(check_flattening(tree, flat)['connection_identity'])
        scope['connections']['hidden'] = [2]
        with self.assertRaisesRegex(ValueError, 'Connected scope'):
            mapped_view(tree)

    def test_checks_remain_active_under_optimized_python(self):
        source = """
from test_synthesis_hierarchy import fixture, check_flattening
tree, flat = fixture()
flat['modules']['tt_um_pinwheel']['cells']['left.reg']['connections']['CLK'] = ['0']
try:
    check_flattening(tree, flat)
except ValueError:
    pass
else:
    raise SystemExit('Accepted corrupted clock')
"""
        result = subprocess.run([sys.executable, '-B', '-O', '-c', source],
                                cwd=Path(__file__).parent, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_tiled_policy_records_exact_storage_owners(self):
        manifest = dict(tiles=[dict(name=f'tile_b{b}_l{k}') for b in range(2) for k in range(16)])
        combined = tiled_policy('tiled', 'combined', manifest)
        self.assertEqual(combined.keep_modules, (TILE,))
        self.assertEqual(len(combined.retained_instances), 32)
        self.assertEqual(dict(combined.retained_instances)['controller.map.tile_b1_l15'], TILE)
        separate = tiled_policy('tiled', 'separate', manifest)
        self.assertEqual(len(separate.retained_instances), 37)
        flat = tiled_policy('tiled-flat', 'combined', manifest)
        self.assertEqual(flat.retained_instances, ())
        self.assertTrue(flat.flatten_before_mapping)
        for variant, org in (('other', 'combined'), ('tiled', 'other')):
            with self.assertRaises(ValueError):
                tiled_policy(variant, org, manifest)


if __name__ == '__main__':
    unittest.main()
