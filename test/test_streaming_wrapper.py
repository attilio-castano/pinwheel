"""Complete port-inventory refusal and public pin chronology controls."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from streaming_wrapper import PUBLIC_INPUTS, bridge_source, package_source, tt_source, validate


def fixture(depth=2):
    def items(mapping):
        return [dict(name=name, width=width) for name, width in mapping.items()]
    ci = dict(initialize=1, command=4, raw_inputs=2, tx_data=32)
    co = dict(busy=1, levels=3, enabled=3, rx_data=32)
    return (dict(module='pinwheel_streaming_core_d' + str(depth), inputs=items(ci), outputs=items(co)),
        dict(module='pinwheel_streaming_quad_frontend',
            inputs=items({**PUBLIC_INPUTS, **{'status_' + name: bits for name, bits in co.items()}}),
            outputs=items({**{'core_' + name: bits for name, bits in ci.items()}, 'miso': 4, 'ready': 1})))


class WrapperTests(unittest.TestCase):
    def test_all_component_ports_have_named_connections(self):
        for depth in (2, 4):
            core, front = fixture(depth)
            ci, co, _, _ = validate(core, front)
            source = package_source(core, front)
            for name in ci:
                self.assertIn('.' + name + '(core_' + name + ')', source)
                self.assertIn('.core_' + name + '(core_' + name + ')', source)
            for name in co:
                self.assertIn('.' + name + '(status_' + name + ')', source)
                self.assertIn('.status_' + name + '(status_' + name + ')', source)
            self.assertNotIn('.*', source)

    def test_dropped_added_changed_and_duplicate_ports_refused(self):
        core, front = fixture()
        for key in ('inputs', 'outputs'):
            for mutate in ('drop', 'add', 'width', 'duplicate', 'inject'):
                candidate = deepcopy(front)
                if mutate == 'drop': candidate[key].pop()
                elif mutate == 'add': candidate[key].append(dict(name='unbound', width=1))
                elif mutate == 'width': candidate[key][0]['width'] += 1
                elif mutate == 'duplicate': candidate[key].append(candidate[key][0])
                else: candidate[key][0]['name'] = 'x); injected('
                with self.subTest(key=key, mutation=mutate), self.assertRaises(ValueError):
                    package_source(core, candidate)

    def test_module_identity_and_public_width_changes_refused(self):
        core, front = fixture()
        for name in ('core', 'frontend'):
            c, f = deepcopy(core), deepcopy(front)
            (c if name == 'core' else f)['module'] += '_other'
            with self.assertRaises(ValueError): package_source(c, f)
        core['outputs'][0]['width'] = 2
        front['inputs'][5]['width'] = 2
        with self.assertRaises(ValueError): package_source(core, front)

    def test_tt_pin_map_and_bridge_observation_boundary(self):
        source = tt_source(2)
        self.assertIn('.mosi({ui_in[7:5], ui_in[2]})', source)
        self.assertIn('.raw_inputs(ui_in[4:3])', source)
        self.assertIn("active ? {2'b0, busy, ready, miso} : 8'b0", source)
        bridge = bridge_source(2)
        self.assertLess(bridge.index('edge_miso=uo_out[3:0]'), bridge.index('clk=1;#10'))
        self.assertGreater(bridge.index('$display("STREAM_QUAD'), bridge.index('clk=1;#10'))
        self.assertNotIn('dut.', bridge)
        for bad in (1, 3, True):
            with self.assertRaises(ValueError): tt_source(bad)
            with self.assertRaises(ValueError): bridge_source(bad)


if __name__ == '__main__':
    unittest.main()
