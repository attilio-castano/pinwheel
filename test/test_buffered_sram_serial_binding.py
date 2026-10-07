"""Independent serial-package wiring fixtures and saved Yosys readback probes."""
from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import buffered_sram_serial_binding as binding
from validation_run import Commands

# These fixture boundaries are stated independently of the checker's tables.
INPUTS = dict(initialize=1, command=3, address=6, word=64, control=24,
    branch=56, count=7, virtual_span=11, idle_levels=3, idle_enabled=3,
    tx_data=32, tx_length=6, rx_capacity=6, expected_generation=16,
    expected_transfer=16, read_index=5, raw_inputs=2)
STATUSES = dict(valid=1, busy=1, retained=1, pending=1, rejected=1,
    mode=2, pc=8, remaining=8, levels=3, enabled=3, tx_consumed=6,
    rx_length=6, rx_data=32, read_valid=1, read_bit=1, generation=16,
    transfer=16, exhausted=1, stage1=2, stage2=2, virtual_pc=10,
    env0=3, env1=3, phase=3, wait_left=8, scratch=16)
PHYSICAL = dict(clk=1, initialize=1, csn=1, sck=1, mosi=1, raw_inputs=2,
    miso=1, ready=1, busy=1, levels=3, enabled=3)
MEMORY = dict(mem_addr0=6, mem_addr1=6, mem_data=64,
    mem_write=1, mem_read=1, mem_q0=64, mem_q1=64)


def fixture():
    cursor, nets, ports, cells = 2, {}, {}, {}

    def wire(name, width, bits=None):
        nonlocal cursor
        if bits is None:
            bits = list(range(cursor, cursor + width))
            cursor += width
        nets[name] = dict(bits=list(bits))
        return list(bits)

    for name, width in PHYSICAL.items():
        bits = wire(name, width)
        ports[name] = dict(direction='output' if name in
            ('miso', 'ready', 'busy', 'levels', 'enabled') else 'input', bits=bits)
        if name not in ('busy', 'levels', 'enabled'):
            wire('frontend.' + name, width, bits)
    for name, width in INPUTS.items():
        bits = wire('core_' + name, width,
                    nets['raw_inputs']['bits'] if name == 'raw_inputs' else None)
        wire('frontend.core_' + name, width, bits)
        wire('controller.' + name, width, bits)
    for name, width in STATUSES.items():
        bits = wire('status_' + name, width,
                    nets[name]['bits'] if name in ('busy', 'levels', 'enabled') else None)
        wire('frontend.status_' + name, width, bits)
        wire('controller.' + name, width, bits)
    for name, width in MEMORY.items():
        bits = wire(name, width)
        wire('controller.' + name, width, bits)
        wire('memory.' + name, width, bits)
    wire('controller.clk', 1, nets['clk']['bits'])
    wire('memory.clk', 1, nets['clk']['bits'])
    for name, module in (('frontend', 'pinwheel_buffered_sram_serial_frontend'),
            ('controller', 'pinwheel_buffered_shared_branches_sram_controller'),
            ('memory', 'pinwheel_buffered_sram_memory')):
        cells[name] = dict(type='$scopeinfo', parameters=dict(TYPE='module'),
                          attributes=dict(module=module), connections={}, port_directions={})
    common = dict(A_CLK=nets['clk']['bits'], A_MEN=['1'], A_DLY=['1'],
        A_WEN=nets['mem_write']['bits'], A_REN=nets['mem_read']['bits'],
        A_DIN=nets['mem_data']['bits'], A_BM=['1'] * 64,
        A_BIST_CLK=['0'], A_BIST_EN=['0'], A_BIST_MEN=['0'],
        A_BIST_WEN=['0'], A_BIST_REN=['0'], A_BIST_ADDR=['0'] * 6,
        A_BIST_DIN=['0'] * 64, A_BIST_BM=['0'] * 64)
    for k in range(2):
        connections = dict(common, A_ADDR=nets[f'mem_addr{k}']['bits'],
            A_DOUT=nets[f'mem_q{k}']['bits'])
        cells[f'memory.storage{k}'] = dict(type='RM_IHPSG13_1P_64x64_c2_bm_bist',
            connections=deepcopy(connections), port_directions={
                name: 'output' if name == 'A_DOUT' else 'input' for name in connections})
    return dict(modules={binding.TOP: dict(ports=ports, netnames=nets, cells=cells)})


class SerialBindingTests(unittest.TestCase):
    def rejected(self, data, message):
        with self.assertRaisesRegex(RuntimeError, message):
            binding.binding_readback(data)

    def test_exact_public_frontend_controller_memory_boundary(self):
        result = binding.binding_readback(fixture())
        self.assertEqual((result['public_input_ports'], result['public_output_ports']), (6, 5))
        self.assertEqual((result['core_input_aliases'], result['status_aliases']), (17, 26))
        self.assertEqual((result['macros'], result['ports_per_macro']), (2, 17))
        self.assertTrue(result['raw_input_passthrough'] and result['common_clock'])

    def test_frontend_version_and_other_module_identities_must_match(self):
        for scope in ('frontend', 'controller', 'memory'):
            data = fixture()
            data['modules'][binding.TOP]['cells'][scope]['attributes']['module'] += '_v2'
            with self.subTest(scope=scope):
                self.rejected(data, 'module identity')

    def test_all_public_directions_widths_and_port_aliases_are_checked(self):
        for name in PHYSICAL:
            for field in ('direction', 'bits'):
                data = fixture(); port = data['modules'][binding.TOP]['ports'][name]
                port[field] = ('output' if port[field] == 'input' else 'input') if field == 'direction' else []
                with self.subTest(port=name, field=field):
                    self.rejected(data, 'public wrapper boundary')
            data = fixture()
            data['modules'][binding.TOP]['ports'][name]['bits'][0] = 10000
            with self.subTest(alias=name):
                self.rejected(data, 'public port wire')
        data = fixture(); data['modules'][binding.TOP]['ports']['status_transfer'] = dict(direction='output', bits=[2])
        self.rejected(data, 'public wrapper boundary')

    def test_every_frontend_core_and_status_alias_is_checked(self):
        aliases = [('frontend.' + name, 'frontend physical') for name in
                   ('clk', 'initialize', 'csn', 'sck', 'mosi', 'raw_inputs', 'miso', 'ready')]
        aliases += [(prefix + name, 'core wire') for prefix in
                    ('core_', 'frontend.core_', 'controller.') for name in INPUTS]
        aliases += [(prefix + name, 'status wire') for prefix in
                    ('status_', 'frontend.status_', 'controller.') for name in STATUSES]
        aliases += [(prefix + name, 'memory wire') for prefix in
                    ('controller.', 'memory.') for name in MEMORY]
        aliases += [('controller.clk', 'controller clock'), ('memory.clk', 'memory clock')]
        for name, message in aliases:
            data = fixture(); data['modules'][binding.TOP]['netnames'][name]['bits'][0] = 10000
            with self.subTest(alias=name):
                self.rejected(data, message)

    def test_raw_input_passthrough_and_protocol_output_aliases_are_checked(self):
        data = fixture(); module = data['modules'][binding.TOP]
        for name in ('core_raw_inputs', 'frontend.core_raw_inputs', 'controller.raw_inputs'):
            module['netnames'][name]['bits'] = [10000, 10001]
        self.rejected(data, 'raw input passthrough')
        for name in ('busy', 'levels', 'enabled'):
            data = fixture(); module = data['modules'][binding.TOP]
            module['ports'][name]['bits'][0] = 10000
            module['netnames'][name]['bits'][0] = 10000
            with self.subTest(output=name):
                self.rejected(data, 'protocol output wire')

    def test_exact_macro_census_rejects_extra_unknown_and_wrong_type(self):
        for kind in ('RM_IHPSG13_1P_512x64_c2_bm_bist', 'unknown_blackbox'):
            data = fixture(); data['modules'][kind] = dict(attributes=dict(blackbox='1'))
            data['modules'][binding.TOP]['cells']['frontend.unqualified'] = dict(
                type=kind, connections={}, port_directions={})
            with self.subTest(kind=kind):
                self.rejected(data, 'macro instances')
        data = fixture(); data['modules'][binding.TOP]['cells'].pop('memory.storage1')
        self.rejected(data, 'macro instances')
        data = fixture(); data['modules'][binding.TOP]['cells']['memory.storage1']['type'] = 'RM_IHPSG13_wrong'
        self.rejected(data, 'macro type')

    def test_macro_broadcast_mask_bist_address_response_clock_and_directions(self):
        for port, value in (('A_ADDR', 'mem_addr0'), ('A_DOUT', 'mem_q0'),
                ('A_CLK', 'sck'), ('A_WEN', ['0']), ('A_REN', ['0']),
                ('A_DIN', ['0'] * 64), ('A_BM', ['1'] * 63 + ['0']),
                ('A_BIST_EN', ['1']), ('A_BIST_BM', ['1'] * 64)):
            data = fixture(); module = data['modules'][binding.TOP]
            module['cells']['memory.storage1']['connections'][port] = (
                module['netnames'][value]['bits'] if type(value) is str else value)
            with self.subTest(port=port):
                self.rejected(data, 'macro port binding')
        data = fixture(); cell = data['modules'][binding.TOP]['cells']['memory.storage0']
        for port in list(cell['port_directions']):
            mutant = deepcopy(data)
            mutant['modules'][binding.TOP]['cells']['memory.storage0']['port_directions'][port] = (
                'input' if port == 'A_DOUT' else 'output')
            with self.subTest(direction=port):
                self.rejected(mutant, 'macro port directions')

    def test_only_exact_frontend_and_controller_operator_prefixes_are_owned(self):
        for name in ('frontend.$eq$1', 'controller.$not$2',
                '$flatten\\frontend.$xor$3', '$flatten\\controller.$add$4'):
            data = fixture(); data['modules'][binding.TOP]['cells'][name] = dict(type='$xor', connections={})
            with self.subTest(allowed=name):
                self.assertEqual(binding.binding_readback(data)['macros'], 2)
        for name in ('wrapper_output_gate', '$flatten\\memory.$dff$1',
                '$flatten\\frontendx.$eq$1', 'frontend_response.$dff$1',
                '$flatten\\other_wrapper.$not$1'):
            data = fixture(); data['modules'][binding.TOP]['cells'][name] = dict(type='$xor', connections={})
            with self.subTest(rejected=name):
                self.rejected(data, 'outside serial frontend')

    def test_register_clocks_and_positive_edge_are_checked_in_both_scopes(self):
        for name in ('frontend.r_response', '$flatten\\controller.$procdff$1'):
            data = fixture(); module = data['modules'][binding.TOP]
            module['cells'][name] = dict(type='$dff', parameters=dict(CLK_POLARITY='1'),
                connections=dict(CLK=module['netnames']['clk']['bits'], D=[9000], Q=[9001]))
            self.assertEqual(binding.binding_readback(data)['checked_clocked_cells'], 1)
            mutant = deepcopy(data); mutant['modules'][binding.TOP]['cells'][name]['connections']['CLK'] = module['netnames']['sck']['bits']
            self.rejected(mutant, 'register clock')
            mutant = deepcopy(data); mutant['modules'][binding.TOP]['cells'][name]['parameters']['CLK_POLARITY'] = '0'
            self.rejected(mutant, 'clock polarity')
        for kind, port in (('$_DFF_P_', 'C'), ('sg13cmos5l_dfrbpq_1', 'CLK')):
            data = fixture(); module = data['modules'][binding.TOP]
            module['cells']['frontend.mapped_ff'] = dict(type=kind,
                connections={port: module['netnames']['clk']['bits']})
            self.assertEqual(binding.binding_readback(data)['checked_clocked_cells'], 1)
            module['cells']['frontend.mapped_ff']['connections'][port] = module['netnames']['sck']['bits']
            self.rejected(data, 'register clock')
        for kind in ('$_DFF_N_', '$_DFFE_NP_', '$dlatch'):
            data = fixture(); data['modules'][binding.TOP]['cells']['frontend.bad_state'] = dict(
                type=kind, connections=dict(C= data['modules'][binding.TOP]['netnames']['clk']['bits']))
            self.rejected(data, 'clock polarity|latch')

    def test_missing_malformed_or_boolean_net_entries_fail_closed(self):
        for value in ({}, {'modules': {}}, {'modules': {binding.TOP: {}}}):
            self.rejected(value, 'Missing')
        for value in (None, [], [True], ['not_a_bit']):
            data = fixture(); data['modules'][binding.TOP]['netnames']['miso']['bits'] = value
            self.rejected(data, 'complete serial wire')


def stub_module(name, ins, outs, body):
    def declaration(direction, label, width):
        return direction + (' ' if width == 1 else f' [{width-1}:0] ') + label
    ports = [declaration('input', n, w) for n, w in ins.items()]
    ports += [declaration('output', n, w) for n, w in outs.items()]
    return 'module ' + name + '(' + ',\n'.join(ports) + ');\n' + body + '\nendmodule\n'


class SavedYosysSerialBindingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not (binding.CAD / 'yosys').is_file() or not (
                binding.VIEWS / (binding.MACRO + '_typ_1p20V_25C.lib')).is_file():
            raise unittest.SkipTest('Pinned Yosys and SRAM Liberty required')

    def test_actual_flattened_anonymous_cells_aliases_and_quoted_paths(self):
        with tempfile.TemporaryDirectory(prefix='pinwheel-serial-binding-') as folder:
            out = Path(folder) / 'quoted paths'; out.mkdir()
            front_ins = dict(clk=1, initialize=1, csn=1, sck=1, mosi=1, raw_inputs=2)
            front_ins.update({'status_' + n: w for n, w in STATUSES.items()})
            front_outs = {'core_' + n: w for n, w in INPUTS.items()}
            front_outs.update(miso=1, ready=1)
            status_parity = ' ^ '.join('(^status_' + name + ')' for name in STATUSES)
            front_body = 'reg q; always @(posedge clk) q <= initialize ? 0 : (~q ^ ' + status_parity + ');\n'
            front_body += 'assign miso = initialize ? 0 : q; assign ready = q;\n'
            for name, width in INPUTS.items():
                source = 'raw_inputs' if name == 'raw_inputs' else 'initialize' if name == 'initialize' else ('mosi' if width == 1 else f'{{{width}{{mosi}}}}')
                front_body += f'assign core_{name} = {source};\n'
            front = out / 'frontend.sv'; front.write_text(stub_module(binding.FRONTEND, front_ins, front_outs, front_body))
            core_ins = dict(clk=1, **INPUTS, mem_q0=64, mem_q1=64)
            core_outs = dict(STATUSES, mem_addr0=6, mem_addr1=6, mem_data=64, mem_write=1, mem_read=1)
            core_body = 'reg q; always @(posedge clk) q <= initialize ? 0 : ~q;\n'
            core_body += 'assign mem_addr0 = address; assign mem_addr1 = ~address;\n'
            core_body += 'assign mem_data = word; assign mem_write = command[0]; assign mem_read = ~command[0];\n'
            for name, width in STATUSES.items():
                source = '(mem_q0[31:0] ^ mem_q1[31:0])' if name == 'rx_data' else ('q' if width == 1 else f'{{{width}{{q}}}}')
                core_body += f'assign {name} = {source};\n'
            core = out / 'controller.sv'; core.write_text(stub_module(binding.CONTROLLER, core_ins, core_outs, core_body))
            result = binding.read_complete_binding(Commands(ROOT, out), out, front, core, 'probe')
            self.assertEqual(result['checked_clocked_cells'], 2)
            import json
            data = json.loads((out / 'probe-binding.json').read_text())
            actual = data['modules'][binding.TOP]['cells']
            self.assertTrue(any(name.startswith('$flatten\\frontend.') for name in actual))
            self.assertTrue(any(name.startswith('$flatten\\controller.') for name in actual))
            actual['$flatten\\other_wrapper.$not$1'] = dict(type='$not', connections={})
            with self.assertRaisesRegex(RuntimeError, 'outside serial frontend'):
                binding.binding_readback(data)


if __name__ == '__main__':
    unittest.main()
