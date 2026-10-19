"""Refuse incomplete state/area bills and unpinned or invalid Liberty areas."""
from decimal import Decimal
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_cost import parse_areas, graph_cost, measure
from streaming_mapped_liberty import FF
from streaming_mapped_liberty import PREFIX, parse_library
from streaming_mapped_netlist import parse_mapped
from streaming_mapped_cost import TT_PORTS
from test_streaming_mapped_liberty import LIBRARY, TYPES


def graph():
    gate = SimpleNamespace(cell='and', output=5, connections={'A': 2, 'B': 3, 'Y': 5})
    flop = SimpleNamespace(cell=FF, q=4, d=5)
    return SimpleNamespace(gates=(gate,), flipflops=(flop,), state_bits={4}, outputs={'out': [5]},
        cell_counts={'and': 1, FF: 1},
        library=SimpleNamespace(cells={'and': SimpleNamespace(directions={'A': 'input', 'B': 'input', 'Y': 'output'})}))


def complete_fixture():
    """Two physical state branches inside the full public pad envelope."""
    ports, next_bit = {}, 2
    for name, (width, direction) in TT_PORTS.items():
        values = list(range(next_bit, next_bit + width))
        next_bit += width
        ports[name] = dict(direction=direction, bits=values)
    for port in ports.values():
        if port['direction'] == 'output': port['bits'] = [1000] * len(port['bits'])
    clock = ports['clk']['bits'][0]
    def cell(kind, directions, values):
        return dict(type=kind, parameters={}, port_directions=directions,
            connections={pin: [value] for pin, value in values.items()})
    cells = {}
    for branch, pairs in (('core', ((1000, 1004), (1001, 1005))),
            ('frontend', ((1002, 1006), (1003, 1007)))):
        for index, (q, d) in enumerate(pairs):
            cells[branch + '_state' + str(index)] = cell(FF,
                dict(CLK='input', D='input', Q='output', RESET_B='input'),
                dict(CLK=clock, D=d, Q=q, RESET_B='1'))
            cells[branch + '_logic' + str(index)] = cell(PREFIX + 'inv_1',
                dict(A='input', Y='output'), dict(A=q, Y=d))
    top = 'tt_um_pinwheel_streaming_ready_d2'
    data = dict(modules={top: dict(ports=ports, cells=cells, netnames={})})
    library = replace(parse_library(LIBRARY, TYPES), pinned=True)
    return data, top, library


class MappedCostTests(unittest.TestCase):
    def test_decimal_area_from_library_and_all_cells_counted(self):
        text = 'library(x) { cell(and) { area: 1.25; } cell(ff) { area: 2.375; } }'
        self.assertEqual(parse_areas(text, {'and', 'ff'}), {'and': Decimal('1.25'), 'ff': Decimal('2.375')})
        result = graph_cost(graph(), {'and': Decimal('1.25'), FF: Decimal('2.375')}, 1)
        self.assertEqual(result['cell_area_um2'], '3.625')
        self.assertEqual((result['total_cells'], result['physical_ff_bits'], result['longest_combinational_gate_path']), (2, 1, 1))

    def test_missing_duplicate_nonfinite_and_nonpositive_area_refused(self):
        for value in ('0', '-1', 'NaN', 'Infinity', 'nonsense'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                parse_areas('library(x) { cell(and) { area: '+value+'; } }', {'and'})
        for text in ('library(x) { cell(and) {} }',
                'library(x) { cell(and) {area:1;} cell(and) {area:2;} }',
                'library(x) { cell(and) {area:1;area:2;} }'):
            with self.subTest(text=text), self.assertRaises(ValueError): parse_areas(text, {'and'})

    def test_every_declared_state_bit_and_cell_area_required(self):
        areas = {'and': Decimal('1'), FF: Decimal('2')}
        for bits in (0, 2, True):
            with self.subTest(bits=bits), self.assertRaises(ValueError): graph_cost(graph(), areas, bits)
        with self.assertRaises(ValueError): graph_cost(graph(), {'and': Decimal('1')}, 1)
        changed = graph(); changed.cell_counts['and'] = 2
        with self.assertRaises(ValueError): graph_cost(changed, areas, 1)

    def test_native_measurement_refuses_unpinned_library_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root/'cells.lib').write_text('library(x){}')
            (root/'mapped.json').write_text('{}')
            with self.assertRaisesRegex(ValueError, 'unpinned'):
                measure(root/'mapped.json', 'top', root/'cells.lib', 1)

    def test_complete_pad_graph_counts_both_state_branches_and_refuses_a_missing_branch(self):
        data, top, library = complete_fixture()
        physical = parse_mapped(data, top, library)
        areas = {name: Decimal('1.25') for name in physical.cell_counts}
        result = graph_cost(physical, areas, 4)
        self.assertEqual((result['physical_ff_bits'], result['total_cells']), (4, 8))
        self.assertEqual(result['cell_area_um2'], '10.00')
        changed = deepcopy(data)
        cells = changed['modules'][top]['cells']
        for name in tuple(cells):
            if name.startswith('frontend'): del cells[name]
        # Even though every pad is still driven and the remaining core is
        # functional, it is not the declared complete source storage.
        missing = parse_mapped(changed, top, library)
        with self.assertRaisesRegex(ValueError, 'declared state'):
            graph_cost(missing, areas, 4)

    def test_partial_physical_state_alias_is_not_a_second_independent_source(self):
        data, top, library = complete_fixture()
        # One bit of the two-bit frontend state is shorted to one core bit;
        # complete vector names alone could otherwise conceal this overlap.
        data['modules'][top]['cells']['frontend_state0']['connections']['Q'] = [1001]
        with self.assertRaisesRegex(ValueError, 'multiple functional output drivers'):
            parse_mapped(data, top, library)


if __name__ == '__main__': unittest.main()
