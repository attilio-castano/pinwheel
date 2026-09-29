"""Paired import contracts and refusal controls, without CAD or saved artifacts."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import paired_readback as pr


def fixture(rb):
    next_bit = 2
    def bits(width):
        nonlocal next_bit
        wires = list(range(next_bit, next_bit + width))
        next_bit += width
        return wires
    ports = {'clk': {'direction': 'input', 'bits': bits(1)}}
    for name, (width, _) in rb.INPUTS.items():
        ports[name] = {'direction': 'input', 'bits': bits(width)}
    cells, nets = {}, {}
    for name, (width, _) in rb.REGISTERS.items():
        wires = bits(width)
        nets[name] = {'bits': wires, 'attributes': {}}
        cells[name] = {'type': '$dff', 'parameters': {'WIDTH': f'{width:b}', 'CLK_POLARITY': '1'},
            'connections': {'CLK': ports['clk']['bits'], 'D': wires[:], 'Q': wires[:]},
            'port_directions': {'CLK': 'input', 'D': 'input', 'Q': 'output'}}
    for name, (width, _) in rb.OUTPUTS.items():
        ports[name] = {'direction': 'output', 'bits': ['0'] * width}
    return {'ports': ports, 'cells': cells, 'netnames': nets, 'attributes': {}}


class PairedReadback(unittest.TestCase):
    def read(self, rb, module):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'import.json'
            path.write_text(json.dumps({'modules': {rb.TOP: module}}))
            return rb.read_rtl(path)

    def test_both_complete_interfaces_and_independent_importers(self):
        core, chip = pr.backend('core'), pr.backend('chip')
        for rb, count, outputs in [(core, 81, 37), (chip, 110, 7), (core, 81, 37)]:
            graph = self.read(rb, fixture(rb))
            self.assertEqual(len(graph.next), count)
            self.assertEqual(len(graph.outputs), outputs)
        with self.assertRaises(ValueError):
            pr.backend('unmodeled')

    def test_every_state_and_output_is_required(self):
        for kind in ['core', 'chip']:
            rb = pr.backend(kind)
            for name in rb.REGISTERS:
                with self.subTest(kind=kind, register=name):
                    module = fixture(rb)
                    del module['cells'][name]
                    with self.assertRaises(ValueError):
                        self.read(rb, module)
            for name in rb.OUTPUTS:
                with self.subTest(kind=kind, output=name):
                    module = fixture(rb)
                    del module['ports'][name]
                    with self.assertRaises(ValueError):
                        self.read(rb, module)

    def test_reject_non_digital_or_unmodeled_semantics(self):
        def wrong_clock(m): m['cells']['r_active']['parameters']['CLK_POLARITY'] = '0'
        def other_clock(m): m['cells']['r_active']['connections']['CLK'] = [999999]
        def asynchronous(m): m['cells']['r_active']['type'] = '$adff'
        def initialized(m): m['netnames']['r_active']['attributes']['init'] = '0'
        def unknown(m): m['cells']['r_active']['connections']['D'] = ['x']
        def high_z(m): m['ports']['mem_read']['bits'] = ['z']
        def undriven(m): m['ports']['mem_read']['bits'] = [999999]
        def missing_q(m): del m['ports']['mem_q0']
        def wrong_q(m): m['ports']['mem_q0']['bits'].pop()
        def alias_state(m): m['netnames']['r_valid']['bits'] = m['netnames']['r_active']['bits']
        def width(m): m['cells']['r_active']['parameters']['WIDTH'] = '10'
        def extra_port(m): m['ports']['hidden'] = {'direction': 'input', 'bits': [999999]}
        def memory(m): m['memories'] = {'hidden': {}}
        def blackbox(m): m['attributes']['blackbox'] = '1'
        for kind in ['core', 'chip']:
            rb = pr.backend(kind)
            for mutate in [wrong_clock, other_clock, asynchronous, initialized, unknown,
                           high_z, undriven, missing_q, wrong_q, alias_state, width,
                           extra_port, memory, blackbox]:
                with self.subTest(kind=kind, defect=mutate.__name__):
                    module = fixture(rb)
                    mutate(module)
                    with self.assertRaises(ValueError):
                        self.read(rb, module)

    def test_interface_manifest_is_exact(self):
        for kind in ['core', 'chip']:
            rb = pr.backend(kind)
            interface = {key: [{'name': n, 'width': w, **({'reference': n} if key == 'registers' else {})}
                              for n, (w, _) in values.items()]
                         for key, values in [('inputs', rb.INPUTS), ('registers', rb.REGISTERS), ('outputs', rb.OUTPUTS)]}
            pr.check_interface(rb, interface)
            for key in interface:
                for defect in ['missing', 'duplicate', 'width', 'boolean-width']:
                    with self.subTest(kind=kind, key=key, defect=defect):
                        changed = copy.deepcopy(interface)
                        if defect == 'missing': changed[key].pop()
                        elif defect == 'duplicate': changed[key].append(changed[key][0])
                        elif defect == 'width': changed[key][0]['width'] += 1
                        else: changed[key][0]['width'] = True
                        with self.assertRaises(ValueError): pr.check_interface(rb, changed)
            interface['registers'][0]['reference'] = 'another_register'
            with self.assertRaises(ValueError): pr.check_interface(rb, interface)

    def test_duplicate_json_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'duplicate.json'
            path.write_text('{"modules": {"m": 1, "m": 2}}')
            with self.assertRaisesRegex(ValueError, 'Duplicate JSON key'):
                pr.read_json(path)

    def test_cyclic_selected_equations_are_rejected(self):
        x = (1, 'var', (), 0)
        pair = dict(left=x, right=x, variables=[(1, 'rtl', 'n0')], definitions=[],
                    constraints=[(x, (1, 'not', (x,), None))])
        with self.assertRaisesRegex(ValueError, 'Cyclic gate equation'):
            pr.expand_constraints(pair)

    def test_shared_hint_labels_are_only_hints(self):
        rb = pr.backend('core')
        graph = rb.Graph()
        graph.nodes['v0'] = rb.Node(64, 'lit', value=0)
        prefix = 'Pinwheel.Hardware.Storage.PairedController.Computation.'
        cuts = [{'node': prefix + str(k), 'label': '%v0'} for k in range(45)]
        # A label can be proposed without proving it; Lean must check every equation.
        pr.check_cuts(cuts, graph)
        for changed in [cuts[:-1], cuts[:-1] + [cuts[0]],
                        [{**cuts[0], 'label': '%missing'}, *cuts[1:]],
                        [{**cuts[0], 'node': 'foreign'}, *cuts[1:]]]:
            with self.assertRaises(ValueError): pr.check_cuts(changed, graph)


if __name__ == '__main__':
    unittest.main()
