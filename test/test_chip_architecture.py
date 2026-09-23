import copy
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location('architecture', SCRIPTS / 'report-chip-architecture.py')
architecture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(architecture)
from chip_organization import SourceGraph, mapped_partition, private_funnels, placed_funnels, projection_screen
from chip_map_slice import cell_areas, map_coordinates, map_slice_report, readback_view


def gate(kind, inputs, output):
    connections = {**inputs, 'X': [output]}
    return {'type': kind, 'parameters': {}, 'connections': connections,
            'port_directions': {p: 'output' if p == 'X' else 'input' for p in connections}}


def fixture():
    # Q -> XOR -> buffer -> D is a legal sequential feedback loop. Both the
    # buffer and XOR are observed, so their cones overlap and cannot be added.
    return {'ports': {'clk': {'direction': 'input', 'bits': [2]},
                      'data': {'direction': 'input', 'bits': [3]},
                      'out': {'direction': 'output', 'bits': [6, 7]}},
            'netnames': {'controller.r_serial_fire': {'bits': [5]},
                         'controller.r_cached_word': {'bits': [20, 21]}},
            'cells': {'ff': {'type': architecture.FF, 'parameters': {},
                             'connections': {'CLK': [2], 'D': [7], 'Q': [5], 'RESET_B': ['1']},
                             'port_directions': {'CLK': 'input', 'D': 'input', 'Q': 'output', 'RESET_B': 'input'}},
                      'xor': gate('sg13cmos5l_xor2_1', {'A': [3], 'B': [5]}, 6),
                      'buf': gate('sg13cmos5l_buf_1', {'A': [6]}, 7)}}


def manifest():
    return {'schema': 1, 'owners': ['serial_receiver', 'fetch_state'],
            'registers': [{'name': 'controller.r_serial_fire', 'width': 1, 'owner': 'serial_receiver'},
                          {'name': 'controller.r_cached_word', 'width': 2, 'owner': 'fetch_state'}]}


def graph(module, assembly=None):
    return architecture.Graph(module, manifest() if assembly is None else assembly)


def crossing_fixture():
    m, a = fixture(), manifest()
    a['crossings'] = []
    for index in range(2):
        name = f'ram{index}'
        m['cells'][name] = {
            'type': architecture.MACROS['hybrid'], 'parameters': {},
            'connections': {'A_ADDR': [3 + 2 * index, '0'], 'A_DIN': [3, 5],
                            'A_DOUT': [30 + 2 * index, 31 + 2 * index], 'A_WEN': ['0'], 'A_REN': ['1']},
            'port_directions': {'A_ADDR': 'input', 'A_DIN': 'input', 'A_DOUT': 'output',
                                'A_WEN': 'input', 'A_REN': 'input'}}
        m['netnames'][f'controller.addr{index}'] = {'bits': [3 + 2 * index, '0', '0', '0']}
        m['netnames'][f'controller.q{index}'] = {'bits': [30 + 2 * index, 31 + 2 * index]}
        a['crossings'] += [
            {'name': f'addr{index}', 'width': 4, 'physical_width': 2, 'producer': 'controller',
             'consumers': [name], 'phase': 'before', 'macro_port': 'A_ADDR'},
            {'name': f'q{index}', 'width': 2, 'physical_width': 2, 'producer': name,
             'consumers': ['controller'], 'phase': 'after', 'macro_port': 'A_DOUT'}]
    for name, port, bits in [('data', 'A_DIN', [3, 5]), ('read', 'A_REN', ['1']), ('write', 'A_WEN', ['0'])]:
        m['netnames']['controller.' + name] = {'bits': bits}
        a['crossings'].append({'name': name, 'width': len(bits), 'physical_width': len(bits),
                               'producer': 'controller', 'consumers': ['ram0', 'ram1'],
                               'phase': 'before', 'macro_port': port})
    return m, a


def source_fixture():
    text = '''module {
  hw.module @controller(in %clk : i1, in %bank : i1, in %write : i1, in %upload : i64, in %mem_q0 : i64, in %mem_q1 : i64, out mem_addr0 : i9, out mem_addr1 : i9, out mem_data : i64, out mem_write : i1) {
    %clock = seq.to_clock %clk
    %pc0 = comb.extract %mem_q0 from 0 : (i64) -> i8
    %pc1 = comb.extract %mem_q1 from 24 : (i64) -> i8
    %read0 = comb.concat %bank, %pc0 : i1, i8
    %read1 = comb.concat %bank, %pc1 : i1, i8
    %addr0 = comb.mux %write, %r_loader_cursor, %read0 : i9
    %addr1 = comb.mux %write, %r_loader_cursor, %read1 : i9
    %r_loader_cursor = seq.compreg %r_loader_cursor, %clock : i9
    hw.output %addr0, %addr1, %upload, %write : i9, i9, i64, i1
  }
}
'''
    probes = [('successor', 'mem_q0', 64), ('candidate0', 'pc0', 8), ('candidate1', 'pc1', 8),
              ('read_address0', 'read0', 9), ('read_address1', 'read1', 9),
              ('write_address', 'r_loader_cursor', 9), ('write_data', 'upload', 64), ('write_enable', 'write', 1)]
    assembly = {'registers': [{'name': 'controller.r_loader_cursor', 'width': 9, 'owner': 'loader'}],
                'computations': [{'name': n, 'mlir_value': '%' + v, 'width': w} for n, v, w in probes]}
    return text, assembly


def map_fixture(bank_words=2):
    module = {'ports': {'clk': {'direction': 'input', 'bits': [2]},
                        'data': {'direction': 'input', 'bits': [3, 4]},
                        'enable': {'direction': 'input', 'bits': [10]},
                        'row': {'direction': 'input', 'bits': list(range(11, 11+2*bank_words))}},
              'cells': {}, 'netnames': {}}
    assembly = {'schema': 1, 'owners': ['index_maps'], 'registers': []}
    for row in range(2*bank_words):
        name = f'controller.r_opaque{row}'
        bits = [100+2*row, 101+2*row]
        module['netnames'][name] = {'bits': bits}
        assembly['registers'].append({'name': name, 'width': 2, 'owner': 'index_maps',
                                      'index_location': {'bank': row//bank_words, 'word': row%bank_words}})
        module['cells'][f'row{row}'] = gate('sg13cmos5l_and2_1', {'A': [10], 'B': [11+row]}, 30+row)
        for position, q in enumerate(bits):
            module['cells'][f'update{q}'] = gate('sg13cmos5l_mux2_1',
                {'A': [q], 'B': [3+position], 'S': [30+row]}, 1000+q)
            module['cells'][f'ff{q}'] = {'type': architecture.FF, 'parameters': {},
                'connections': {'Q': [q], 'D': [1000+q], 'CLK': [2], 'RESET_B': ['1']},
                'port_directions': {'Q': 'output', 'D': 'input', 'CLK': 'input', 'RESET_B': 'input'}}
    for replica in range(2):
        addresses = []
        for position in range(2):
            base, j = 200+100*replica+30*position, 0
            # Match the source read tree: high-bit pairs are nearest the data.
            nbits = bank_words.bit_length()-1
            order = [bank*bank_words+int(f'{word:0{nbits}b}'[::-1], 2)
                     for bank in range(2) for word in range(bank_words)]
            level = [100+2*word+position for word in order]
            while len(level) > 1:
                following = []
                for a, b in zip(level[::2], level[1::2]):
                    module['cells'][f'read{replica}_{position}_{j}'] = gate('sg13cmos5l_xor2_1', {'A': [a], 'B': [b]}, base+j)
                    following.append(base+j)
                    j += 1
                level = following
            addresses.append(level[0])
        module['cells'][f'ram{replica}'] = {'type': architecture.MACROS['hybrid'], 'parameters': {},
            'connections': {'A_ADDR': addresses+['0'], 'A_DIN': [3, 4], 'A_DOUT': [2000+replica]},
            'port_directions': {'A_ADDR': 'input', 'A_DIN': 'input', 'A_DOUT': 'output'}}
    modules = {kind: {'attributes': {'area': str(area)}} for kind, area in [
        (architecture.FF, 10), ('sg13cmos5l_and2_1', 1), ('sg13cmos5l_mux2_1', 2), ('sg13cmos5l_xor2_1', 3)]}
    return module, assembly, modules


class ChipArchitecture(unittest.TestCase):
    def test_read_tree_tiles_keep_strided_subtrees_inside(self):
        m, a, libs = map_fixture(bank_words=4)
        g = architecture.Graph(m, a)
        r = map_slice_report(g, a, cell_areas(libs, g), tile_words=2)
        for reader in ['read0', 'read1']:
            self.assertEqual(r['word_tiles']['selected']['roles'][reader]['owned_cells'], 0)
            self.assertEqual(r['read_tree_tiles']['selected']['roles'][reader]['owned_cells'], 2)
        self.assertEqual(r['read_tree_tiles']['cell_groups']['ff100'], 'bank0_low000')
        self.assertEqual(r['read_tree_tiles']['cell_groups']['ff104'], 'bank0_low000')
        self.assertEqual(r['read_tree_tiles']['cell_groups']['ff102'], 'bank0_low001')

    def test_slice_readback_view_ignores_net_numbers_and_cell_names(self):
        m, a, libs = map_fixture()
        g = architecture.Graph(m, a)
        original = map_slice_report(g, a, cell_areas(libs, g), tile_words=1)
        m['cells'] = {f'cell_{k}': cell for k, cell in enumerate(reversed(list(m['cells'].values())))}
        arrays = [p['bits'] for p in m['ports'].values()] + [n['bits'] for n in m['netnames'].values()]
        arrays += [bits for cell in m['cells'].values() for bits in cell['connections'].values()]
        for bits in arrays:
            bits[:] = [bit+10000 if type(bit) is int else bit for bit in bits]
        g = architecture.Graph(m, a)
        renamed = map_slice_report(g, a, cell_areas(libs, g), tile_words=1)
        self.assertEqual(readback_view(original), readback_view(renamed))

    def test_map_slice_counts_state_both_readers_updates_and_shared_control(self):
        m, a, libs = map_fixture()
        g = architecture.Graph(m, a)
        report = map_slice_report(g, a, cell_areas(libs, g), tile_words=1)
        plane = report['planes']['groups']['bit0']
        self.assertEqual((plane['flip_flops'], plane['combinational_cells'], plane['area_um2']), (4, 10, 66))
        self.assertEqual((plane['incoming_nets'], plane['outgoing_nets']), (5, 2))
        self.assertEqual(report['planes']['groups']['shared']['combinational_cells'], 4)
        tile = report['word_tiles']['groups']['bank0_words000']
        self.assertEqual((tile['flip_flops'], tile['combinational_cells'], tile['area_um2']), (2, 3, 25))
        for partition in [report['planes'], report['word_tiles']]:
            self.assertEqual(sum(b['area_um2'] for b in partition['groups'].values()), 136)
            self.assertEqual(sum(b['flip_flops'] for b in partition['groups'].values()), 8)
        self.assertEqual(report['planes']['selected']['roles']['read0']['owned_cells'], 3)
        self.assertEqual(report['planes']['selected']['roles']['read1']['owned_cells'], 3)
        self.assertEqual(report['planes']['selected']['roles']['update']['owned_cells'], 4)
        self.assertEqual(report['planes']['selected']['outgoing_roles'], {'read0': 1, 'read1': 1})

    def test_map_coordinates_survive_register_and_cell_renaming(self):
        m, a, libs = map_fixture()
        g = architecture.Graph(m, a)
        original = map_slice_report(g, a, cell_areas(libs, g), tile_words=1)
        m['cells'] = {f'cell_{k}': cell for k, cell in enumerate(reversed(list(m['cells'].values())))}
        for k, slot in enumerate(a['registers']):
            renamed = f'controller.r_unrelated_{100-k}'
            m['netnames'][renamed] = m['netnames'].pop(slot['name'])
            slot['name'] = renamed
        g = architecture.Graph(m, a)
        renamed = map_slice_report(g, a, cell_areas(libs, g), tile_words=1)
        for kind in ['planes', 'word_tiles']:
            self.assertEqual(original[kind]['groups'], renamed[kind]['groups'])
            self.assertEqual(original[kind]['unique_slice_crossing_nets'], renamed[kind]['unique_slice_crossing_nets'])

    def test_map_coordinates_reject_missing_duplicate_and_incomplete_banks(self):
        m, a, _ = map_fixture()
        for change, error in [
            (lambda x: x['registers'][0].pop('index_location'), 'Missing typed'),
            (lambda x: x['registers'][0].update(index_location=x['registers'][1]['index_location']), 'Duplicate'),
            (lambda x: x['registers'][0].update(index_location={'bank': 3, 'word': 0}), 'Invalid'),
            (lambda x: x['registers'][0].update(index_location={'bank': 0, 'word': 2}), 'Incomplete')]:
            mutated = copy.deepcopy(a)
            change(mutated)
            with self.assertRaisesRegex(ValueError, error):
                map_coordinates(architecture.Graph(m, mutated), mutated)

    def test_map_slice_rejects_cross_bit_update(self):
        m, a, libs = map_fixture()
        m['cells']['ff100']['connections']['D'] = [101]
        g = architecture.Graph(m, a)
        with self.assertRaisesRegex(ValueError, 'another stored map bit'):
            map_slice_report(g, a, cell_areas(libs, g), tile_words=1)

    def test_map_slice_rejects_wrong_read_plane(self):
        m, a, libs = map_fixture()
        m['cells']['ram0']['connections']['A_ADDR'][0] = m['cells']['ram0']['connections']['A_ADDR'][1]
        g = architecture.Graph(m, a)
        with self.assertRaisesRegex(ValueError, 'exactly its stored map plane'):
            map_slice_report(g, a, cell_areas(libs, g), tile_words=1)

    def test_shared_control_with_external_consumer_stays_outside_tile(self):
        m, a, libs = map_fixture()
        m['ports']['observed_decode'] = {'direction': 'output', 'bits': [30]}
        g = architecture.Graph(m, a)
        report = map_slice_report(g, a, cell_areas(libs, g), tile_words=1)
        self.assertEqual(report['word_tiles']['cell_groups']['row0'], 'shared')
        self.assertEqual(report['word_tiles']['groups']['bank0_words000']['combinational_cells'], 2)

    def test_map_slice_rejects_area_and_tile_shape_errors(self):
        m, a, libs = map_fixture()
        g = architecture.Graph(m, a)
        for value in ['nan', '-1', None]:
            libs[architecture.FF]['attributes']['area'] = value
            with self.assertRaisesRegex(ValueError, '(Invalid|Missing) mapped cell area'):
                cell_areas(libs, g)
        libs[architecture.FF]['attributes']['area'] = 10
        with self.assertRaisesRegex(ValueError, 'Tile size'):
            map_slice_report(g, a, cell_areas(libs, g), tile_words=3)

    def test_projection_counts_input_cost_as_well_as_shorter_output(self):
        # Moving g toward its macro shortens the output by 99, but lengthens
        # both incoming nets by 99. Every net is counted once.
        context = {'instances': {
            'a': {'macro': False, 'bbox': [-1, 99, 1, 101]},
            'b': {'macro': False, 'bbox': [1, 99, 3, 101]},
            'g': {'macro': False, 'bbox': [4, 99, 6, 101]},
            'ram': {'macro': True}}, 'ports': [],
            'macro_pins': [{'instance': 'ram', 'pin': 'A_ADDR[0]', 'bbox': [5, 0, 5, 0]}],
            'nets': {n: {'type': 'SIGNAL', 'ports': [], 'terminals': [
                {'instance': src, 'pin': 'X'}, {'instance': dst, 'pin': pin}]}
                for n, src, dst, pin in [('a-g', 'a', 'g', 'A'), ('b-g', 'b', 'g', 'B'),
                                         ('g-ram', 'g', 'ram', 'A_ADDR[0]')]}}
        funnels = {'ram': {'cuts': {'3': {'cells': ['g']}}}}
        windows = {'ram': [4, 0, 6, 2]}
        result = projection_screen(context, funnels, windows)
        self.assertEqual(result['joint']['incident_nets'], 3)
        self.assertEqual(result['joint']['before_span_um'], 108)
        self.assertEqual(result['joint']['projected_span_um'], 207)
        self.assertEqual(result['isolated_improving_moves'], [])
        with self.assertRaisesRegex(ValueError, 'exactly'):
            projection_screen(context, funnels, {})
        with self.assertRaisesRegex(ValueError, 'exceeds'):
            projection_screen(context, funnels, {'ram': [4, 0, 5, 2]})
        context['macro_pins'] = []
        with self.assertRaisesRegex(ValueError, 'Missing endpoint geometry'):
            projection_screen(context, funnels, windows)

    def test_private_funnels_stop_at_shared_state_and_depth(self):
        # s is shared by two address ports; u also updates state and is ineligible.
        inputs = {'s': {1}, 'a': {2, 3}, 'b': {2, 4}, 'tail': {5}, 'u': {7}}
        drivers = {2: 's', 5: 'a', 6: 'b', 8: 'tail', 9: 'u'}
        targets = {'ram0': {8, 9}, 'ram1': {6}}
        result = private_funnels(inputs, drivers, targets, {9}, depths=(1, 2))
        self.assertEqual(result['ram0']['private_address_cells'], 2)
        self.assertEqual(result['ram0']['cuts']['1']['cells'], ['tail'])
        self.assertEqual(result['ram0']['cuts']['2']['cells'], ['a', 'tail'])
        self.assertEqual(result['ram0']['cuts']['2']['incoming_nets'], [2, 3])
        self.assertEqual(result['ram1']['cuts']['2']['cells'], ['b'])
        for item in result.values():
            self.assertNotIn('s', item['cuts']['2']['cells'])
            self.assertNotIn('u', item['cuts']['2']['cells'])
        with self.assertRaisesRegex(ValueError, 'positive'):
            private_funnels(inputs, drivers, targets, {9}, depths=(0,))

    def test_placed_funnels_use_connectivity_and_geometric_proxy(self):
        instances = {'ram0': {'cell': architecture.MACROS['hybrid'], 'macro': True},
                     'ram1': {'cell': architecture.MACROS['hybrid'], 'macro': True},
                     'buf': {'cell': 'sg13cmos5l_buf_4', 'macro': False, 'bbox': [10, 20, 12, 22]}}
        nets = {'in': {'type': 'SIGNAL', 'ports': ['in'], 'terminals': [
            {'instance': 'buf', 'pin': 'A', 'direction': 'INPUT'}]}}
        pins = []
        for ram in ('ram0', 'ram1'):
            for bit in range(6):
                net = f'{ram}_{bit}'
                nets[net] = {'type': 'SIGNAL', 'ports': [], 'terminals': [
                    {'instance': ram, 'pin': f'A_ADDR[{bit}]', 'direction': 'INPUT'}]}
                pins.append({'instance': ram, 'pin': f'A_ADDR[{bit}]', 'bbox': [0, 0, 1, 1]})
        nets['ram0_0']['terminals'].append({'instance': 'buf', 'pin': 'X', 'direction': 'OUTPUT'})
        context = {'instances': instances, 'nets': nets, 'macro_pins': pins,
                   'database': 'fixture.odb', 'database_sha256': 'fixture'}
        report = placed_funnels(context, architecture.COMB)
        cut = report['funnels']['ram0']['cuts']['3']
        self.assertEqual(cut['cells'], ['buf'])
        self.assertEqual(cut['mean_center_distance_um'], 30)
        self.assertEqual(cut['cell_area_um2'], 4)
        instances['buf']['cell'] = 'unknown_sequential_cell'
        with self.assertRaisesRegex(ValueError, 'Unknown placed cell'):
            placed_funnels(context, architecture.COMB)

    def test_source_phase_cuts_and_bit_positions(self):
        g = SourceGraph(*source_fixture())
        modes = g.report()['request_modes']
        self.assertEqual(modes['read_edge']['roots'],
                         {'bank': [0], 'mem_q0': list(range(8)), 'mem_q1': list(range(24, 32))})
        self.assertEqual(modes['write_edge']['roots'], {'r_loader_cursor': list(range(9))})
        self.assertIn('write', modes['all_edges']['roots'])
        self.assertNotIn('write', modes['read_edge']['roots'])
        frontier = g.report()['computations']['read_address0']['frontier']['roots']
        self.assertEqual(frontier, {'bank': [0], 'candidate0': list(range(8))})

    def test_source_subtraction_includes_lower_carry_bits(self):
        text, assembly = source_fixture()
        text = text.replace('    hw.output', '''    %delta = comb.sub %mem_q0, %mem_q1 : i64
    %bit = comb.extract %delta from 4 : (i64) -> i1
    hw.output''')
        roots = SourceGraph(text, assembly).cone(['bit'])['roots']
        self.assertEqual(roots, {'mem_q0': list(range(5)), 'mem_q1': list(range(5))})

    def test_source_rejects_wrong_phase_probe_and_operation(self):
        text, assembly = source_fixture()
        changes = []
        a = copy.deepcopy(assembly); a['computations'][3]['mlir_value'] = '%read1'; changes.append((text, a))
        a = copy.deepcopy(assembly); a['computations'][0]['width'] = 63; changes.append((text, a))
        a = copy.deepcopy(assembly); a['computations'].append(a['computations'][0]); changes.append((text, a))
        a = copy.deepcopy(assembly); a['computations'].pop(); changes.append((text, a))
        changes += [(text.replace('comb.concat', 'comb.unknown'), assembly),
                    (text.replace('from 24', 'from 60'), assembly),
                    (text.replace('%write, %r_loader_cursor, %read0', '%write, %read0, %r_loader_cursor'), assembly),
                    (text.replace('comb.extract %mem_q0', 'comb.extract %missing'), assembly)]
        for t, a in changes:
            with self.assertRaises(ValueError):
                SourceGraph(t, a)

    def test_partition_assigns_shared_gates_once_and_counts_crossings(self):
        m, a = fixture(), manifest()
        a['owner_regions'] = {'serial_receiver': 'interface', 'fetch_state': 'fetch'}
        second = copy.deepcopy(m['cells']['ff'])
        second['connections'].update(D=[6], Q=[20])
        m['cells']['fetch_ff'] = second
        part = mapped_partition(graph(m, a), a)
        self.assertEqual(part['cells']['xor']['region'], 'shared')
        self.assertEqual(part['cells']['buf']['region'], 'interface')
        self.assertEqual(len(part['cells']), 4)
        groups = part['summary']['groups']
        self.assertEqual(sum(g['combinational_cells'] for g in groups.values()), 2)
        self.assertEqual(sum(g['flip_flops'] for g in groups.values()), 2)
        self.assertEqual(part['summary']['crossing_pairs']['shared -> fetch'], {'nets': 1, 'sink_pins': 1})
        self.assertNotIn(2, [c['bit'] for c in part['crossings']])  # Clock excluded.

    def test_partition_refuses_incomplete_regions(self):
        a = manifest(); a['owner_regions'] = {'serial_receiver': 'interface'}
        with self.assertRaisesRegex(ValueError, 'owner regions'):
            mapped_partition(graph(fixture(), a), a)

    def test_sequential_cut_and_shared_cone(self):
        g = graph(fixture())
        self.assertEqual(g.cone([6, 7])['combinational_cells'], 2)
        self.assertEqual(g.cone([6, 7])['max_cell_depth'], 2)
        self.assertEqual(g.cone([7])['root_bits_by_owner'], {'package_inputs': 1, 'serial_receiver': 1})
        self.assertEqual(g.cone([5])['combinational_cells'], 0)
        self.assertEqual(g.cone(['0', '1'])['root_bits_by_owner'], {})

    def test_unused_named_registers_are_not_physical_storage(self):
        state = graph(fixture()).state()
        self.assertEqual(state['fetch_state']['named_bits'], 2)
        self.assertEqual(state['fetch_state']['mapped_ff_bits'], 0)
        self.assertEqual(len(state['fetch_state']['unimplemented_bits']), 2)
        self.assertEqual(state['serial_receiver']['mapped_ff_bits'], 1)

    def test_fingerprint_ignores_auto_names_and_bit_numbers(self):
        original = graph(fixture())
        renamed = fixture()
        for port in renamed['ports'].values():
            port['bits'] = [b + 100 for b in port['bits']]
        for wire in renamed['netnames'].values():
            wire['bits'] = [b + 100 for b in wire['bits']]
        for cell in renamed['cells'].values():
            cell['connections'] = {p: [b + 100 if type(b) is int else b for b in bits]
                                   for p, bits in cell['connections'].items()}
        renamed['cells'] = {f'auto{i}': c for i, c in enumerate(renamed['cells'].values())}
        self.assertEqual(original.boundary_signature(), graph(renamed).boundary_signature())

    def test_fingerprint_detects_logic_sequential_input_and_pin_changes(self):
        original = graph(fixture()).boundary_signature()
        changes = []
        m = fixture(); m['cells']['xor']['type'] = 'sg13cmos5l_or2_1'; changes.append(m)
        m = fixture(); m['cells']['ff']['connections']['D'] = [6]; changes.append(m)
        m = fixture(); m['cells']['ff']['connections']['RESET_B'] = ['0']; changes.append(m)
        m = fixture(); m['ports']['out']['bits'] = [7, 6]; changes.append(m)
        for m in changes:
            self.assertNotEqual(original, graph(m).boundary_signature())

    def test_rejects_multiple_drivers_cycle_and_undriven_input(self):
        changes = []
        m = fixture(); m['cells']['extra'] = gate('sg13cmos5l_buf_1', {'A': [3]}, 5)
        changes.append((m, 'Multiple'))
        m = fixture(); m['cells']['xor']['connections']['A'] = [7]; changes.append((m, 'cycle'))
        m = fixture(); m['cells']['xor']['connections']['A'] = [99]; changes.append((m, 'Undriven'))
        for m, error in changes:
            with self.subTest(error=error), self.assertRaisesRegex(ValueError, error):
                graph(m)

    def test_rejects_unknown_owners_and_ambiguous_state(self):
        m = fixture(); m['netnames']['controller.r_unknown'] = {'bits': [5]}
        with self.assertRaisesRegex(ValueError, 'manifest mismatch'):
            graph(m)
        m = fixture(); m['netnames']['controller.r_start_pending'] = {'bits': [5]}
        a = manifest()
        a['registers'].append({'name': 'controller.r_start_pending', 'width': 1, 'owner': 'fetch_state'})
        with self.assertRaisesRegex(ValueError, 'ambiguous'):
            graph(m, a)
        m = fixture(); del m['netnames']['controller.r_serial_fire']
        a = manifest(); a['registers'].pop(0)
        with self.assertRaisesRegex(ValueError, 'Unowned'):
            graph(m, a)

    def test_rejects_unknown_cells_and_ports(self):
        m = fixture(); m['cells']['xor']['type'] = 'unmodeled_latch'
        with self.assertRaisesRegex(ValueError, 'Unsupported cell'):
            graph(m)
        m = fixture(); del m['cells']['xor']['port_directions']['A']
        with self.assertRaisesRegex(ValueError, 'Missing cell port'):
            graph(m)

    def test_port_budget_separates_broadcast_constants_and_unused_outputs(self):
        m = fixture()
        macro = {'type': architecture.MACROS['hybrid'], 'parameters': {},
                 'connections': {'A_ADDR': [3, 3], 'A_DIN': [3, '0'], 'A_DOUT': [30, 31]},
                 'port_directions': {'A_ADDR': 'input', 'A_DIN': 'input', 'A_DOUT': 'output'}}
        m['cells']['ram0'] = macro
        m['cells']['ram1'] = copy.deepcopy(macro)
        m['cells']['ram1']['connections']['A_DOUT'] = [32, 33]
        m['ports']['out']['bits'] += [30]
        g = graph(m)
        self.assertEqual(g.port_budget(['ram0', 'ram1'], 'A_DIN'),
                         {'endpoint_pins': 4, 'nonconstant_endpoint_pins': 2,
                          'distinct_nonconstant_nets': 1, 'loaded_nets': 1})
        self.assertEqual(g.port_budget(['ram0', 'ram1'], 'A_DOUT')['loaded_nets'], 1)
        self.assertEqual(g.cone([30])['root_bits_by_owner'], {'ram0': 1})
        changed = copy.deepcopy(m)
        changed['cells']['ram1']['connections']['A_ADDR'][0] = 5
        self.assertNotEqual(g.boundary_signature(), graph(changed).boundary_signature())

    def test_hash_guard_rejects_changed_input(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'source').write_text('before')
            expected = {'source': architecture.sha(root / 'source')}
            architecture.check_hashes(root, expected)
            (root / 'source').write_text('after')
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                architecture.check_hashes(root, expected)

    def test_state_binding_rejects_missing_duplicate_width_and_owner(self):
        bad = []
        a = manifest(); a['registers'].pop(); bad.append(a)
        a = manifest(); a['registers'].append(a['registers'][0]); bad.append(a)
        a = manifest(); a['registers'][0]['width'] = 2; bad.append(a)
        a = manifest(); a['registers'][0]['owner'] = 'reference_image'; bad.append(a)
        for a in bad:
            with self.assertRaises(ValueError):
                graph(fixture(), a)

    def test_ownership_survives_names_without_any_semantic_pattern(self):
        m, a = fixture(), manifest()
        m['netnames']['controller.r_opaque'] = m['netnames'].pop('controller.r_serial_fire')
        a['registers'][0]['name'] = 'controller.r_opaque'
        self.assertEqual(graph(m, a).state()['serial_receiver']['mapped_ff_bits'], 1)

    def test_complete_macro_binding_and_zero_extended_addresses(self):
        m, a = crossing_fixture()
        self.assertEqual(architecture.check_crossings(graph(m, a), a),
                         {'crossings': 7, 'macro_terminals': 10, 'address_truncation_checked': True})

    def test_crossing_mutations_rejected(self):
        changes = []
        m, a = crossing_fixture(); a['crossings'].pop(); changes.append((m, a))
        m, a = crossing_fixture(); a['crossings'].append(a['crossings'][0]); changes.append((m, a))
        m, a = crossing_fixture(); a['crossings'][0]['phase'] = 'after'; changes.append((m, a))
        m, a = crossing_fixture(); a['crossings'][0]['physical_width'] = 3; changes.append((m, a))
        m, a = crossing_fixture(); a['crossings'][1]['producer'] = 'ram1'; changes.append((m, a))
        m, a = crossing_fixture(); m['netnames']['controller.addr0']['bits'][3] = 3; changes.append((m, a))
        m, a = crossing_fixture(); a['crossings'][-1]['consumers'] = ['ram0']; changes.append((m, a))
        for m, a in changes:
            with self.assertRaises(ValueError):
                architecture.check_crossings(graph(m, a), a)


if __name__ == '__main__':
    unittest.main()
