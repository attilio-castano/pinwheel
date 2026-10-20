"""Controller artifact refusal controls; no CAD or historical artifacts required."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import buffered_sram_readback as br


def fixture(rb):
    cursor = 1
    def bits(width):
        nonlocal cursor
        result = list(range(cursor, cursor + width))
        cursor += width
        return result
    ports = {'clk': {'direction': 'input', 'bits': bits(1)}}
    ports.update({name: {'direction': 'input', 'bits': bits(width)}
                  for name, (width, _) in rb.INPUTS.items()})
    cells, nets = {}, {}
    for name, (width, _) in rb.REGISTERS.items():
        wires = bits(width)
        nets[name] = {'bits': wires, 'attributes': {}}
        cells[name] = {'type': '$dff',
            'parameters': {'WIDTH': f'{width:b}', 'CLK_POLARITY': '1'},
            'connections': {'CLK': ports['clk']['bits'], 'D': wires[:], 'Q': wires[:]},
            'port_directions': {'CLK': 'input', 'D': 'input', 'Q': 'output'}}
    ports.update({name: {'direction': 'output', 'bits': ['0'] * width}
                  for name, (width, _) in rb.OUTPUTS.items()})
    return {'ports': ports, 'cells': cells, 'netnames': nets, 'attributes': {}}


class BufferedSramReadback(unittest.TestCase):
    def setUp(self):
        self.rb = br.backend()

    def read(self, module):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'import.json'
            path.write_text(json.dumps({'modules': {self.rb.TOP: module}}))
            return br.read_rtl(self.rb, path)

    def test_complete_contract_and_private_importer(self):
        self.assertEqual((len(self.rb.INPUTS), len(self.rb.REGISTERS), len(self.rb.OUTPUTS)),
                         (19, 117, 31))
        self.assertEqual(sum(width for width, _ in self.rb.REGISTERS.values()), 3151)
        self.assertEqual(len(self.read(fixture(self.rb)).next), 117)
        import backend_readback
        self.assertEqual(backend_readback.TOP, 'pinwheel_atomic_small_dense_cached')
        self.assertNotIn('mem_q1', backend_readback.INPUTS)
        self.assertEqual(self.rb.TOP, br.backend().TOP)

    def test_semantic_cut_requires_matching_typed_graph_coordinates(self):
        graph = self.read(fixture(self.rb))
        for source, target in [('missing', 'r_pending'), ('r_count', 'r_pending')]:
            with self.subTest(source=source, target=target), self.assertRaisesRegex(
                    ValueError, 'Invalid semantic cut interface'):
                br.partitions(self.rb, graph, graph, None,
                    semantic_pairs={source: (target, 'selection_entry')})

    def test_reference_certificate_refuses_missing_selection_proof_boundary(self):
        graph = self.read(fixture(self.rb))
        with self.assertRaisesRegex(ValueError, 'Expected one checked dictionary-selection cut'):
            br.reference_certificate_sources(self.rb, graph, graph, graph, [])

    def test_every_state_coordinate_is_required(self):
        for name in self.rb.REGISTERS:
            module = fixture(self.rb)
            del module['cells'][name]
            with self.subTest(register=name), self.assertRaisesRegex(ValueError, 'Missing backend registers'):
                self.read(module)

    def test_every_input_and_output_is_required(self):
        for name in [*self.rb.INPUTS, *self.rb.OUTPUTS]:
            module = fixture(self.rb)
            del module['ports'][name]
            with self.subTest(port=name), self.assertRaisesRegex(ValueError, 'Changed port contract'):
                self.read(module)

    def test_independent_responses_and_exact_widths(self):
        for name in ['mem_q0', 'mem_q1', 'mem_addr0', 'mem_addr1', 'mem_data', 'tx_data']:
            module = fixture(self.rb)
            module['ports'][name]['bits'].pop()
            with self.subTest(port=name), self.assertRaisesRegex(ValueError, 'Changed port contract'):
                self.read(module)
        module = fixture(self.rb)
        module['ports']['mem_q1']['bits'] = module['ports']['mem_q0']['bits'][:]
        with self.assertRaisesRegex(ValueError, 'aliased'):
            self.read(module)

    def test_clock_initialization_and_hidden_state_refused(self):
        for name in ['r_metadata63', 'r_branch15', 'r_phase', 'r_tx_data', 'r_start_word']:
            module = fixture(self.rb)
            module['cells'][name]['parameters']['CLK_POLARITY'] = '0'
            with self.subTest(register=name), self.assertRaisesRegex(ValueError, 'clock'):
                self.read(module)
        module = fixture(self.rb)
        module['netnames']['r_phase']['attributes']['init'] = '000'
        with self.assertRaisesRegex(ValueError, 'Implicit register initialization'):
            self.read(module)
        module = fixture(self.rb)
        extra = copy.deepcopy(module['cells']['r_phase'])
        extra['connections']['Q'] = [100000, 100001, 100002]
        module['cells']['hidden'] = extra
        with self.assertRaisesRegex(ValueError, 'Changed state mapping'):
            self.read(module)

    def test_unknown_values_memories_and_blackboxes_refused(self):
        module = fixture(self.rb)
        module['ports']['mem_data']['bits'][0] = 'x'
        with self.assertRaisesRegex(ValueError, 'Unknown/high-impedance'):
            self.read(module)
        for key, value in [('memories', {'hidden': {}}), ('attributes', {'blackbox': '1'})]:
            module = fixture(self.rb)
            module[key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'memory or black box'):
                self.read(module)

    def test_duplicate_json_keys_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'bad.json'
            path.write_text('{"modules":{},"modules":{}}')
            with self.assertRaisesRegex(ValueError, 'Duplicate JSON key'):
                br.read_rtl(self.rb, path)

    def test_assembly_exact_contract(self):
        interface = {'schema': 1, 'module': br.TOP}
        for name, fields in [('inputs', self.rb.INPUTS), ('registers', self.rb.REGISTERS),
                             ('outputs', self.rb.OUTPUTS)]:
            interface[name] = [{'name': n, 'width': w, **({'reference': n} if name == 'registers' else {})}
                               for n, (w, _) in fields.items()]
        br.check_interface(self.rb, interface)
        for kind in ['inputs', 'registers', 'outputs']:
            changed = copy.deepcopy(interface)
            changed[kind] = changed[kind][:-1]
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, 'Changed buffered SRAM interface'):
                br.check_interface(self.rb, changed)
        changed = copy.deepcopy(interface)
        changed['inputs'][0]['width'] = True
        with self.assertRaisesRegex(ValueError, 'Invalid interface entries'):
            br.check_interface(self.rb, changed)
        changed = copy.deepcopy(interface)
        changed['schema'] = True
        with self.assertRaisesRegex(ValueError, 'assembly module/schema'):
            br.check_interface(self.rb, changed)


if __name__ == '__main__':
    unittest.main()
