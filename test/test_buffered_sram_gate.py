"""Fail-closed oracle, macro binding and directed deadline census checks."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
SPEC = importlib.util.spec_from_file_location('buffered_sram_gate',
    ROOT / 'scripts/check-buffered-sram.py')
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


class BufferedSramGateTests(unittest.TestCase):
    def pair(self):
        request = dict(schema='pinwheel-buffered-shared-branches-input-v1', cases=[
            dict(name='arbitrary-observation', checks=[], vectors=[dict(command={}, raw_inputs=0)])])
        vectors = dict(schema='pinwheel-buffered-shared-branches-vectors-v1', cases=[
            dict(name='arbitrary-observation', vectors=[dict(command={}, raw_inputs=0,
                state={name: 0 for name in gate.BASE.STATE_WIDTHS})])])
        return request, vectors

    def test_unchecked_public_field_must_match_frozen_oracle(self):
        request, expected = self.pair()
        candidate = deepcopy(expected)
        result = gate.check_export(request, candidate, expected)
        self.assertEqual(result['all_public_field_comparisons'], len(gate.BASE.STATE_WIDTHS))
        candidate['cases'][0]['vectors'][0]['state']['scratch'] = 1
        with self.assertRaisesRegex(RuntimeError, 'independent shared-bank oracle'):
            gate.check_export(request, candidate, expected)

    def test_oracle_names_coverage_and_boolean_transcripts_fail_closed(self):
        request, expected = self.pair()
        for oracle in (dict(expected, cases=[]), dict(expected, cases=expected['cases'] * 2)):
            with self.assertRaises(RuntimeError): gate.check_export(request, expected, oracle)
        candidate = deepcopy(expected); candidate['cases'][0]['vectors'][0]['raw_inputs'] = False
        with self.assertRaisesRegex(RuntimeError, 'raw input type'):
            gate.check_export(request, candidate, expected)

    def test_branch_deadlines_have_independent_checks_on_every_running_edge(self):
        cases = gate.directed_cases()['cases']
        self.assertEqual(len(cases), 5)
        for case in cases[:4]:
            checks = [c['state'] for c in case['checks'] if c['state'].get('phase') == 3]
            self.assertEqual(len(checks), 129)
            self.assertTrue(all(c['remaining'] == 0 and c['busy'] == 1 for c in checks))
            self.assertEqual({c['pc'] for c in checks}, {0, 1, 2})
            self.assertEqual({v['raw_inputs'] for v in case['vectors']}, {0, 1, 2, 3})
        rows = [v['command']['address'] for v in cases[-1]['vectors']
            if v['command'].get('command') == 1]
        self.assertEqual(set(rows), set(range(64)))
        self.assertEqual(rows.count(0), 3)  # replacement, full image, short image
        self.assertEqual(cases[-1]['checks'][-1]['state'],
            dict(pc=0, phase=7, retained=1, rx_length=0, tx_consumed=0))

    def binding(self):
        widths = dict(clk=1, mem_write=1, mem_read=1, mem_data=64,
            mem_addr0=6, mem_addr1=6, mem_q0=64, mem_q1=64)
        cursor, nets = 2, {}
        for name, width in widths.items():
            nets[name] = dict(bits=list(range(cursor, cursor+width))); cursor += width
        common = dict(A_CLK=nets['clk']['bits'], A_MEN=['1'], A_DLY=['1'],
            A_WEN=nets['mem_write']['bits'], A_REN=nets['mem_read']['bits'],
            A_DIN=nets['mem_data']['bits'], A_BM=['1'] * 64,
            A_BIST_CLK=['0'], A_BIST_EN=['0'], A_BIST_MEN=['0'], A_BIST_WEN=['0'],
            A_BIST_REN=['0'], A_BIST_ADDR=['0'] * 6, A_BIST_DIN=['0'] * 64, A_BIST_BM=['0'] * 64)
        cells = {}
        for k in range(2):
            connections = dict(common, A_ADDR=nets[f'mem_addr{k}']['bits'], A_DOUT=nets[f'mem_q{k}']['bits'])
            cells[f'memory.storage{k}'] = dict(type=gate.MACRO, connections=connections,
                port_directions={name: 'output' if name == 'A_DOUT' else 'input' for name in connections})
        ports = {}
        for direction, widths in (('input', dict(clk=1, raw_inputs=2, **gate.BASE.COMMAND_FIELDS)),
                ('output', gate.BASE.STATE_WIDTHS)):
            for name, width in widths.items():
                if name not in nets:
                    nets[name] = dict(bits=list(range(cursor, cursor+width))); cursor += width
                ports[name] = dict(direction=direction, bits=list(nets[name]['bits']))
        for name in list(nets): nets['controller.' + name] = dict(bits=list(nets[name]['bits']))
        return dict(modules={gate.TOP: dict(netnames=nets, cells=cells, ports=ports)})

    def test_complete_binding_census_rejects_alias_write_and_response_mutants(self):
        before = self.binding()
        self.assertEqual(gate.binding_readback(before)['macros'], 2)
        for port, value in (('A_ADDR', before['modules'][gate.TOP]['netnames']['mem_addr0']['bits']),
                ('A_DOUT', before['modules'][gate.TOP]['netnames']['mem_q0']['bits']),
                ('A_WEN', ['0']), ('A_BM', ['1'] * 63 + ['0']), ('A_BIST_EN', ['1'])):
            data = deepcopy(before)
            data['modules'][gate.TOP]['cells']['memory.storage1']['connections'][port] = value
            with self.subTest(port=port), self.assertRaisesRegex(RuntimeError, 'port binding'):
                gate.binding_readback(data)
        data = deepcopy(before); data['modules'][gate.TOP]['cells'].pop('memory.storage1')
        with self.assertRaisesRegex(RuntimeError, 'instances'): gate.binding_readback(data)

    def test_other_macro_or_unknown_blackbox_cannot_escape_complete_census(self):
        for cell_type in ('RM_IHPSG13_1P_512x64_c2_bm_bist', 'unqualified_memory'):
            data = self.binding()
            data['modules'][gate.TOP]['cells']['memory.unexpected'] = dict(type=cell_type,
                connections={}, port_directions={})
            data['modules'][cell_type] = dict(attributes=dict(blackbox='1'))
            with self.subTest(cell_type=cell_type), self.assertRaisesRegex(RuntimeError, 'instances'):
                gate.binding_readback(data)
        data = self.binding()
        data['modules'][gate.TOP]['cells']['memory.storage1']['type'] = 'RM_IHPSG13_1P_512x64_c2_bm_bist'
        with self.assertRaisesRegex(RuntimeError, 'macro type'): gate.binding_readback(data)

    def test_wrong_macro_direction_and_public_wrapper_width_direction_are_rejected(self):
        data = self.binding()
        data['modules'][gate.TOP]['cells']['memory.storage1']['port_directions']['A_DOUT'] = 'input'
        with self.assertRaisesRegex(RuntimeError, 'port directions'): gate.binding_readback(data)
        for field, value in (('direction', 'input'), ('bits', [2])):
            data = self.binding(); data['modules'][gate.TOP]['ports']['rx_data'][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(RuntimeError, 'public wrapper boundary'):
                gate.binding_readback(data)
        data = self.binding(); data['modules'][gate.TOP]['ports']['unexpected'] = dict(direction='input', bits=[2])
        with self.assertRaisesRegex(RuntimeError, 'public wrapper boundary'): gate.binding_readback(data)

    def test_controller_memory_and_public_aliases_must_be_direct(self):
        for name in ('mem_q0', 'mem_q1', 'mem_addr0', 'mem_addr1', 'mem_data',
                'mem_write', 'mem_read', 'clk', 'command', 'rx_data'):
            data = self.binding()
            data['modules'][gate.TOP]['netnames']['controller.' + name]['bits'][0] = 10000
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'controller wire'):
                gate.binding_readback(data)
        data = self.binding(); data['modules'][gate.TOP]['ports']['rx_data']['bits'][0] = 10000
        with self.assertRaisesRegex(RuntimeError, 'public port wire'): gate.binding_readback(data)
        data = self.binding()
        data['modules'][gate.TOP]['cells']['wrapper_response_register'] = dict(type='$dff',
            connections={}, port_directions={})
        with self.assertRaisesRegex(RuntimeError, 'outside controller'): gate.binding_readback(data)

    def test_poison_fixture_varies_each_replica_and_preserves_normal_bridge(self):
        original = gate.BRIDGE.read_bytes()
        with tempfile.TemporaryDirectory() as out:
            first = gate.poison_bridge(out, 1).read_text()
            second = gate.poison_bridge(out, 7).read_text()
            self.assertNotEqual(first, second)
            self.assertIn('dut.memory.storage0.i_SRAM_1P_behavioral_bm_bist.memory[poison_index]', first)
            self.assertIn('dut.memory.storage1.i_SRAM_1P_behavioral_bm_bist.memory[poison_index]', first)
            self.assertEqual(first.count('.dr_r ='), 2)
        self.assertEqual(gate.BRIDGE.read_bytes(), original)


if __name__ == '__main__':
    unittest.main()
