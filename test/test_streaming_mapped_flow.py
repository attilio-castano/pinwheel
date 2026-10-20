"""The proposed state boundary refuses disappearing or aliased register bits."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_mapped_flow import mapping_script, source_state, state_inventory
from streaming_mapped_liberty import parse_library
from test_streaming_mapped_liberty import LIBRARY, TYPES
from test_streaming_mapped_netlist import fixture


def source():
    data = fixture(); module = data['modules']['top']
    module['netnames'] = dict(r_state=dict(bits=[4]))
    module['cells']['state'] = dict(type='$dff', parameters=dict(CLK_POLARITY='1', WIDTH='1'),
        port_directions=dict(CLK='input', D='input', Q='output'),connections=dict(CLK=[3], D=[6], Q=[4]))
    return data


def mapped():
    data = fixture(); data['modules']['top']['netnames'] = dict(r_state=dict(bits=[4])); return data


class FlowTests(unittest.TestCase):
    def test_positive_full_q_bijection_contains_both_d_functions(self):
        result = state_inventory(source(), mapped(), 'top', parse_library(LIBRARY, TYPES))
        self.assertTrue(result['complete_ff_q_bijection'])
        self.assertEqual((result['register_fields'], result['register_bits']), (1, 1))
        self.assertEqual(result['registers'][0]['source_d'], 6)
        self.assertEqual(result['registers'][0]['mapped_d'], 6)

    def test_source_constant_alias_or_unnamed_q_refuses(self):
        for mode in ('constant', 'alias', 'missing', 'extra'):
            data = source(); names = data['modules']['top']['netnames']
            if mode == 'constant': names['r_state']['bits'] = ['0']
            elif mode == 'alias': names['r_alias'] = dict(bits=[4])
            elif mode == 'missing': del names['r_state']
            else: names['r_unstored'] = dict(bits=[99])
            with self.subTest(mode=mode), self.assertRaises(ValueError): source_state(data, 'top')

    def test_mapped_missing_extra_constant_aliased_and_resized_registers_refuse(self):
        for mode in ('missing', 'extra', 'constant', 'alias', 'width'):
            data = mapped(); names = data['modules']['top']['netnames']
            if mode == 'missing': names.clear()
            elif mode == 'extra': names['r_extra'] = dict(bits=[99])
            elif mode == 'constant': names['r_state']['bits'] = ['0']
            elif mode == 'alias': names['r_extra'] = dict(bits=[4])
            else: names['r_state']['bits'] = [4, 5]
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                state_inventory(source(), data, 'top', parse_library(LIBRARY, TYPES))

    def test_changed_port_contract_refuses(self):
        for mode in ('name', 'width'):
            data = mapped(); ports = data['modules']['top']['ports']
            if mode == 'name': ports['renamed'] = ports.pop('z')
            else: ports['z']['bits'] = [5]
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                state_inventory(source(), data, 'top', parse_library(LIBRARY, TYPES))

    def test_source_clock_polarity_and_storage_kind_refuse(self):
        for mode in ('polarity', 'clock', 'storage'):
            data = source(); cell = data['modules']['top']['cells']['state']
            if mode == 'polarity': cell['parameters']['CLK_POLARITY'] = '0'
            elif mode == 'clock': cell['connections']['CLK'] = [2]
            else: cell['type'] = '$adff'
            with self.subTest(mode=mode), self.assertRaises(ValueError): source_state(data, 'top')

    def test_flow_contains_no_global_synthesis_optimization_or_retiming(self):
        script = mapping_script('/tmp/a.json', 'top', '/tmp/out', '/tmp/cells.lib', '/tmp/abc')
        self.assertIn('setattr -set keep 1 t:$dff', script)
        self.assertIn('techmap\n', script)
        self.assertFalse(any(line.startswith(('synth', 'opt', 'fsm', 'flatten', 'retime')) for line in script.splitlines()))
        for top in ('bad top', 'top; delete', 'top\nclean'):
            with self.subTest(top=top), self.assertRaises(ValueError): mapping_script('/tmp/a', top, '/tmp/b', '/tmp/c', '/tmp/d')


if __name__ == '__main__': unittest.main()
