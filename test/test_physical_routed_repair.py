"""Reject semantic, clock, power and geometry changes in native repair output."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_routed_repair import compare_repair, verify_geometry
from test_physical_region_placement import fixture


class IdentityLibrary:
    def pin(self, corner, cell, pin):
        return 'direction : input;' if pin == 'A' else 'direction : output; function : "A";'


def modules():
    def cell(kind, ports):
        return dict(type=kind, parameters={}, connections={p: [b] for p, b in ports.items()},
                    port_directions={p: 'output' if p == 'X' else 'input' for p in ports})
    before = dict(ports={'in': dict(direction='input', bits=[1]), 'out': dict(direction='output', bits=[2])},
                  cells={'gate': cell('sg13cmos5l_inv_1', {'A': 1, 'X': 2})})
    after = deepcopy(before); after['ports']['out']['bits'] = [3]
    after['cells']['hold_new'] = cell('sg13cmos5l_dlygate4sd3_1', {'A': 2, 'X': 3})
    return before, after


class RoutedRepair(unittest.TestCase):
    def test_delay_insertion_preserves_logic(self):
        before, after = modules()
        proof = compare_repair(before, after, IdentityLibrary(), ['fast', 'slow'])
        self.assertEqual(proof['added_cells'], {'hold_new': 'sg13cmos5l_dlygate4sd3_1'})

    def test_false_identity_liberty_rejected(self):
        class BadLibrary(IdentityLibrary):
            def pin(self, corner, cell, pin):
                return super().pin(corner, cell, pin).replace('"A"', '"!A"')
        with self.assertRaises(ValueError):
            compare_repair(*modules(), BadLibrary(), ['fast'])

    def test_native_buf16_requires_identity_at_every_corner(self):
        before, after = modules()
        after['cells']['hold_new']['type'] = 'sg13cmos5l_buf_16'
        proof = compare_repair(before, after, IdentityLibrary(), ['fast', 'slow'])
        self.assertEqual(proof['added_cells'], {'hold_new': 'sg13cmos5l_buf_16'})
        class WrongSlowFunction(IdentityLibrary):
            def pin(self, corner, cell, pin):
                body = super().pin(corner, cell, pin)
                return body.replace('"A"', '"!A"') if corner == 'slow' else body
        with self.assertRaisesRegex(ValueError, 'does not implement identity'):
            compare_repair(before, after, WrongSlowFunction(), ['fast', 'slow'])
        after['cells']['hold_new']['type'] = 'sg13cmos5l_buf_32'
        with self.assertRaisesRegex(ValueError, 'non-transport'):
            compare_repair(before, after, IdentityLibrary(), ['fast', 'slow'])

    def test_sizing_requires_identical_pinned_function_at_every_corner(self):
        b, a = modules(); a['cells']['gate']['type'] = 'sg13cmos5l_inv_2'
        proof = compare_repair(b, a, IdentityLibrary(), ['fast', 'slow'], allow_resizing=True)
        self.assertEqual(proof['resized_cells']['gate']['after'], 'sg13cmos5l_inv_2')
        class WrongSlowFunction(IdentityLibrary):
            def pin(self, corner, cell, pin):
                value = super().pin(corner, cell, pin)
                return value.replace('"A"', '"!A"') if corner == 'slow' and cell.endswith('inv_2') else value
        with self.assertRaises(ValueError):
            compare_repair(b, a, WrongSlowFunction(), ['fast', 'slow'], allow_resizing=True)
        a['cells']['gate']['type'] = 'sg13cmos5l_buf_2'
        with self.assertRaises(ValueError):
            compare_repair(b, a, IdentityLibrary(), ['fast'], allow_resizing=True)

    def test_changed_logic_or_bypass_rejected(self):
        for mode in ['resize', 'remove', 'bypass', 'wrong_cell', 'cycle']:
            b, a = modules()
            if mode == 'resize': a['cells']['gate']['type'] = 'sg13cmos5l_inv_2'
            elif mode == 'remove': del a['cells']['gate']
            elif mode == 'bypass': a['cells']['hold_new']['connections']['A'] = [1]
            elif mode == 'wrong_cell': a['cells']['hold_new']['type'] = 'sg13cmos5l_inv_1'
            else: a['cells']['hold_new']['connections']['A'] = [3]
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                compare_repair(b, a, IdentityLibrary(), ['fast'])

    def test_empty_corners_and_changed_parameters_rejected(self):
        b, a = modules()
        with self.assertRaises(ValueError):
            compare_repair(b, a, IdentityLibrary(), [])
        a = deepcopy(b); a['cells']['gate']['parameters']['behavior'] = '1'
        with self.assertRaises(ValueError):
            compare_repair(b, a, IdentityLibrary(), ['fast'])

    def test_legal_move_rejects_protected_clock_power_and_geometry_changes(self):
        p, b = fixture(); b['nets']['VGND'] = deepcopy(b['nets']['VDD']); b['nets']['VGND']['type'] = 'GROUND'
        b['nets']['VPWR'] = b['nets'].pop('VDD')
        for t in b['nets']['VGND']['terminals']: t['pin'] = 'VSS'
        a = deepcopy(b); a['instances']['a'].update(bbox=[30, 0, 32, 2], bbox_dbu=[30, 0, 32, 2])
        definitions = {'row0': dict(orientation='R0', site_width_dbu=1, site_height_dbu=2)}
        proof = verify_geometry(b, a, ['state', 'clock', 'hold1'], definitions)
        self.assertEqual(proof['moved_original_cells'], 1)
        for mode in ['state', 'clock', 'power', 'row', 'overlap', 'cell', 'macro']:
            bad = deepcopy(a)
            if mode == 'state': bad['instances']['state']['orientation'] = 'MY'
            elif mode == 'clock': bad['nets']['clock']['terminals'].pop()
            elif mode == 'power': bad['nets']['VPWR']['terminals'].pop()
            elif mode == 'row': bad['instances']['a']['orientation'] = 'MX'
            elif mode == 'overlap': bad['instances']['a'].update(bbox=[8, 0, 10, 2], bbox_dbu=[8, 0, 10, 2])
            elif mode == 'cell': bad['instances']['a']['cell'] = 'sg13cmos5l_buf_8'
            else: bad['macro_pins'] = [{}]
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                verify_geometry(b, bad, ['state', 'clock', 'hold1'], definitions)

    def test_new_delay_cell_needs_both_power_connections(self):
        _, b = fixture(); b['nets']['VGND'] = deepcopy(b['nets']['VDD']); b['nets']['VGND']['type'] = 'GROUND'
        b['nets']['VPWR'] = b['nets'].pop('VDD')
        for t in b['nets']['VGND']['terminals']: t['pin'] = 'VSS'
        a = deepcopy(b)
        a['instances']['hold_new'] = dict(cell='sg13cmos5l_dlygate4sd3_1', macro=False,
            bbox=[30, 0, 32, 2], bbox_dbu=[30, 0, 32, 2], orientation='R0')
        for net, pin in [('VPWR', 'VDD'), ('VGND', 'VSS')]:
            a['nets'][net]['terminals'].append(dict(instance='hold_new', pin=pin, direction='INOUT'))
        rows = {'row0': dict(orientation='R0', site_width_dbu=1, site_height_dbu=2)}
        self.assertEqual(verify_geometry(b, a, ['state', 'clock'], rows)['added_cells'], ['hold_new'])
        for net in ['VPWR', 'VGND']:
            bad = deepcopy(a); bad['nets'][net]['terminals'].pop()
            with self.subTest(net=net), self.assertRaises(ValueError):
                verify_geometry(b, bad, ['state', 'clock'], rows)


if __name__ == '__main__':
    unittest.main()
