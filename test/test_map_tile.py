"""The arbitrary-state checker must reject missing or misidentified hardware."""
from copy import deepcopy
import importlib.util
from pathlib import Path
import sys
import unittest

SCRIPTS = Path(__file__).resolve().parents[1] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location('map_tile_check', SCRIPTS / 'check-map-tile.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def manifest():
    return {'inputs': [{'name': n, 'width': w} for n, w in check.MAP_INPUTS.items()],
            'tile_inputs': [{'name': n, 'width': w} for n, w in check.TILE_INPUTS.items()],
            'outputs': [{'name': n, 'width': 5} for n in ('index0', 'index1')],
            'tiles': [{'bank': b, 'low': low, 'name': f'tile_b{b}_l{low}',
                       'words': list(range(low, 256, 16))} for b in range(2) for low in range(16)]}


def module(mapped=False):
    ports, nets, cells, bit = {}, {}, {}, 2
    for name, width in {**check.TILE_INPUTS, 'clk': 1}.items():
        ports[name] = {'direction': 'input', 'bits': list(range(bit, bit + width))}
        bit += width
    for word in range(16):
        nets[f'r_word{word}'] = {'bits': list(range(bit, bit + 5))}
        for index in range(5):
            pins = {'D': [ports['write_data']['bits'][index]], 'Q': [bit + index]}
            pins['CLK' if mapped else 'C'] = ports['clk']['bits']
            if mapped:
                pins['RESET_B'] = ['1']
            cells[f'ff{word}_{index}'] = {'type': check.FF if mapped else '$_DFF_P_',
                                         'connections': pins,
                                         'port_directions': {p: 'output' if p == 'Q' else 'input' for p in pins}}
        bit += 5
    for index in range(2):
        ports[f'index{index}'] = {'direction': 'output', 'bits': nets[f'r_word{index}']['bits']}
    return {'ports': ports, 'netnames': nets, 'cells': cells}


class MapTileChecks(unittest.TestCase):
    def test_coordinates_and_interfaces(self):
        check.validate_manifest(manifest())
        self.assertEqual(len(check.state_names('tiled', manifest())), 512)
        self.assertEqual(check.state_names('tiled', manifest())[16], 'tile_b0_l0.r_word1')
        self.assertEqual(check.state_names('tiled', manifest())[257], 'tile_b1_l1.r_word0')

    def test_reject_coordinate_alias_and_incorrect_ports(self):
        for mutate in (lambda m: m['tiles'].__setitem__(1, m['tiles'][0]),
                       lambda m: m['tiles'][0]['words'].reverse(),
                       lambda m: m['tile_inputs'][0].__setitem__('width', 2)):
            with self.subTest(mutate=mutate):
                m = manifest()
                mutate(m)
                with self.assertRaises(ValueError):
                    check.validate_manifest(m)

    def test_canonical_state_is_exact_q_and_d(self):
        for mapped in (False, True):
            with self.subTest(mapped=mapped):
                m = module(mapped)
                original = deepcopy(m)
                cut = check.cut_state(m, 'tile', manifest())
                self.assertEqual(m, original)
                self.assertEqual(cut['cells'], {})
                self.assertEqual(cut['ports']['next_state']['bits'], m['ports']['write_data']['bits'] * 16)
                self.assertEqual(cut['ports']['state']['bits'],
                                 [b for word in range(16) for b in m['netnames'][f'r_word{word}']['bits']])

    def test_reject_missing_aliased_and_extra_state(self):
        for mutate in (lambda m: m['netnames'].pop('r_word0'),
                       lambda m: m['netnames'].__setitem__('r_word0', m['netnames']['r_word1']),
                       lambda m: m['cells'].pop('ff0_0')):
            with self.subTest(mutate=mutate):
                m = module()
                mutate(m)
                with self.assertRaises(ValueError):
                    check.cut_state(m, 'tile', manifest())

    def test_reject_clock_reset_and_unsupported_ff(self):
        for pins in ({'CLK': ['0']}, {'RESET_B': ['0']}, {'RESET_B': [999]}):
            with self.subTest(pins=pins):
                m = module(True)
                m['cells']['ff0_0']['connections'].update(pins)
                with self.assertRaises(ValueError):
                    check.cut_state(m, 'tile', manifest())
        m = module()
        m['cells']['ff0_0']['type'] = '$_DFF_N_'
        with self.assertRaises(ValueError):
            check.cut_state(m, 'tile', manifest())

    def test_area_and_port_depth_and_fanout(self):
        m = module(True)
        library = {check.FF: {'attributes': {'area': '12.5'}}}
        result = check.metrics(m, library, 'tile', manifest())
        self.assertEqual(result['state_bits'], 80)
        self.assertEqual(result['combinational_cells'], 0)
        self.assertEqual(result['area_um2'], 1000)
        self.assertEqual(result['logic_depth'], {'index0': 0, 'index1': 0, 'next_state': 0})
        self.assertEqual(result['input_maximum_fanout']['write_data'], 16)
        library[check.FF]['attributes']['area'] = 'nan'
        with self.assertRaises(ValueError):
            check.metrics(m, library, 'tile', manifest())


if __name__ == '__main__':
    unittest.main()
