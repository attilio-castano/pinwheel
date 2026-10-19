"""Single-clock graph and simultaneous FF semantics, with structural refusals."""
from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_liberty import FF, PREFIX, parse_library
from streaming_mapped_netlist import evaluate_graph, load_mapped, parse_mapped
from test_streaming_mapped_liberty import LIBRARY, TYPES


def fixture():
    def cell(name, directions, connections):
        return dict(type=name, parameters={}, port_directions=directions,
            connections={pin: [value] for pin, value in connections.items()})
    return dict(modules=dict(top=dict(ports=dict(a=dict(direction='input', bits=[2]),
        clk=dict(direction='input', bits=[3]), z=dict(direction='output', bits=[5, '0', 5])),
        netnames=dict(metadata_only=dict(bits=['x', 4])), cells=dict(
            state=cell(FF, dict(CLK='input', D='input', Q='output', RESET_B='input'),
                dict(CLK=3, D=6, Q=4, RESET_B='1')),
            invert=cell(PREFIX + 'inv_1', dict(A='input', Y='output'), dict(A=4, Y=5)),
            combine=cell(PREFIX + 'and2_1', dict(A='input', B='input', X='output'), dict(A=2, B=5, X=6)),
            metadata=dict(type='$scopeinfo', parameters=dict(TYPE='module'), connections={}, port_directions={})))))


class MappedTests(unittest.TestCase):
    def setUp(self): self.library = parse_library(LIBRARY, TYPES)

    def test_ff_cut_observes_pre_edge_q_and_updates_all_state_simultaneously(self):
        graph = parse_mapped(fixture(), 'top', self.library)
        self.assertEqual((len(graph.gates), len(graph.flipflops), graph.metadata_cells), (2, 1, 1))
        for a in (False, True):
            for q in (False, True):
                result = evaluate_graph(graph, {2: a}, {4: q})
                self.assertEqual(result['next_state'], {4: a and not q})
                self.assertEqual(result['outputs']['z'], (not q, False, not q))

    def test_metadata_x_and_public_aliases_are_distinct_from_functional_x_z(self):
        parse_mapped(fixture(), 'top', self.library)
        for value in ('x', 'z', True, -1):
            data = fixture(); data['modules']['top']['cells']['combine']['connections']['A'] = [value]
            with self.subTest(value=value), self.assertRaises(ValueError): parse_mapped(data, 'top', self.library)

    def test_direct_positive_clock_and_tied_inactive_reset_are_required(self):
        for pin, value in [('CLK', 5), ('CLK', '1'), ('RESET_B', '0'), ('RESET_B', 2), ('D', 3)]:
            data = fixture(); data['modules']['top']['cells']['state']['connections'][pin] = [value]
            with self.subTest(pin=pin, value=value), self.assertRaises(ValueError): parse_mapped(data, 'top', self.library)
        data = fixture(); data['modules']['top']['cells']['combine']['connections']['A'] = [3]
        with self.assertRaises(ValueError): parse_mapped(data, 'top', self.library)

    def test_unknown_cell_parameters_pins_and_self_reported_directions_refuse(self):
        for kind in ('type', 'parameters', 'pin', 'direction', 'width'):
            data = fixture(); cell = data['modules']['top']['cells']['combine']
            if kind == 'type': cell['type'] = 'unknown_comb'
            elif kind == 'parameters': cell['parameters'] = dict(WIDTH=1)
            elif kind == 'pin': cell['connections']['UNKNOWN'] = [2]
            elif kind == 'direction': cell['port_directions']['X'] = 'input'
            else: cell['connections']['A'] = [2, 2]
            with self.subTest(kind=kind), self.assertRaises(ValueError): parse_mapped(data, 'top', self.library)

    def test_multidrivers_ff_aliases_combinational_cycles_and_unknown_sources_refuse(self):
        for kind in ('driver', 'q-alias', 'cycle', 'undriven', 'ff-data', 'public-output'):
            data = fixture(); module = data['modules']['top']
            if kind == 'driver': module['cells']['duplicate'] = deepcopy(module['cells']['invert'])
            elif kind == 'q-alias': module['cells']['duplicate'] = deepcopy(module['cells']['state'])
            elif kind == 'cycle': module['cells']['invert']['connections']['A'] = [5]
            elif kind == 'undriven': module['cells']['combine']['connections']['A'] = [99]
            elif kind == 'ff-data': module['cells']['state']['connections']['D'] = [99]
            else: module['ports']['z']['bits'] = [99]
            with self.subTest(kind=kind), self.assertRaises(ValueError): parse_mapped(data, 'top', self.library)

    def test_scope_metadata_cannot_hide_wires_and_primary_aliases_or_inout_refuse(self):
        for kind in ('scope', 'alias', 'inout', 'memory'):
            data = fixture(); module = data['modules']['top']
            if kind == 'scope': module['cells']['metadata']['connections']['X'] = [2]
            elif kind == 'alias': module['ports']['a']['bits'] = [3]
            elif kind == 'inout': module['ports']['a']['direction'] = 'inout'
            else: module['memories'] = dict(storage={})
            with self.subTest(kind=kind), self.assertRaises(ValueError): parse_mapped(data, 'top', self.library)

    def test_missing_extra_and_integer_boolean_assignments_refuse(self):
        graph = parse_mapped(fixture(), 'top', self.library)
        for inputs, state in [({}, {4: False}), ({2: False, 3: True}, {4: False}),
                ({2: 0}, {4: False}), ({2: False}, {}), ({2: False}, {4: 0})]:
            with self.subTest(inputs=inputs, state=state), self.assertRaises(ValueError): evaluate_graph(graph, inputs, state)

    def test_duplicate_json_keys_refuse_before_graph_interpretation(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'mapped.json'
            path.write_text('{"modules":{},"modules":{}}')
            with self.assertRaisesRegex(ValueError, 'Duplicate'): load_mapped(path, 'top', self.library)

    def test_hierarchy_reconstructs_real_body_and_preserves_output_input_aliases(self):
        data = fixture(); module = data['modules']['top']
        inv = module['cells'].pop('invert')
        data['modules']['child'] = dict(ports=dict(a=dict(direction='input', bits=[2]),
            y=dict(direction='output', bits=[3]), alias=dict(direction='output', bits=[2])),
            cells=dict(inv={**inv, 'connections': dict(A=[2], Y=[3])}))
        module['cells']['child'] = dict(type='child', parameters={}, port_directions=dict(a='input', y='output', alias='output'),
            connections=dict(a=[4], y=[5], alias=[11]))
        module['ports']['alias'] = dict(direction='output', bits=[11])
        graph = parse_mapped(data, 'top', self.library)
        for q in (False, True):
            value = evaluate_graph(graph, {2: True}, {4: q})
            self.assertEqual(value['outputs']['alias'], (q,))
            self.assertEqual(value['next_state'], {4: not q})
        # The name "child" supplies no semantics: changing its actual body
        # changes the result, rather than retaining the old named operation.
        data['modules']['child']['cells']['inv']['connections']['A'] = ['0']
        self.assertTrue(evaluate_graph(parse_mapped(data, 'top', self.library), {2: False}, {4: True})['outputs']['z'][0])

    def test_hierarchy_unknown_blackbox_recursive_resize_direction_and_internal_x_refuse(self):
        base = fixture(); module = base['modules']['top']; inv = module['cells'].pop('invert')
        base['modules']['child'] = dict(ports=dict(a=dict(direction='input', bits=[2]), y=dict(direction='output', bits=[3])),
            cells=dict(inv={**inv, 'connections': dict(A=[2], Y=[3])}))
        module['cells']['child'] = dict(type='child', parameters={}, port_directions=dict(a='input', y='output'),
            connections=dict(a=[4], y=[5]))
        for kind in ('unknown', 'blackbox', 'whitebox', 'recursive', 'resize', 'direction', 'x', 'parameter'):
            data = deepcopy(base); child = data['modules']['child']; instance = data['modules']['top']['cells']['child']
            if kind == 'unknown': instance['type'] = 'missing'
            elif kind in ('blackbox', 'whitebox'): child['attributes'] = {kind: '1'}
            elif kind == 'recursive': child['cells']['self'] = deepcopy(instance)
            elif kind == 'resize': instance['connections']['a'] = [4, 2]
            elif kind == 'direction': instance['port_directions']['a'] = 'output'
            elif kind == 'x': child['cells']['inv']['connections']['A'] = ['x']
            else: instance['parameters'] = dict(WIDTH=1)
            with self.subTest(kind=kind), self.assertRaises(ValueError): parse_mapped(data, 'top', self.library)

    def test_combinational_leaf_has_no_hidden_clock_or_state(self):
        data = dict(modules=dict(leaf=dict(ports=dict(a=dict(direction='input', bits=[2]),
            y=dict(direction='output', bits=[3])), cells=dict(inv=dict(type=PREFIX+'inv_1', parameters={},
            port_directions=dict(A='input', Y='output'), connections=dict(A=[2], Y=[3]))))))
        graph = parse_mapped(data, 'leaf', self.library, combinational=True)
        self.assertEqual(evaluate_graph(graph, {2: False}, {})['outputs'], {'y': (True,)})
        with self.assertRaises(ValueError): parse_mapped(data, 'leaf', self.library)
        data['modules']['leaf']['ports']['clk'] = dict(direction='input', bits=[4])
        with self.assertRaises(ValueError): parse_mapped(data, 'leaf', self.library, combinational=True)


if __name__ == '__main__': unittest.main()
