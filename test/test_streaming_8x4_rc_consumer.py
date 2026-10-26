import importlib.util
from decimal import Decimal
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('rc_consumer', Path(__file__).resolve().parents[1] / 'scripts/streaming_8x4_rc_consumer.py')
C = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(C)


def spef():
    return '''*SPEF "IEEE 1481-1998"
*R_UNIT 0.001 KOHM
*NAME_MAP
*1 probe
*2 probe_A
*3 probe_B
*PORTS
*2 I
*3 O
*D_NET *1 0.01
*CONN
*P *2 I
*P *3 O
*CAP
1 *2 0.01
*RES
1 *2 *1:1 3
2 *1:1 *3 4
*END
'''


class ConsumerTests(unittest.TestCase):
    def test_exact_declared_fixture_membership(self):
        inventory = {'explicit_vias': {name: {'cut_layer': layer} for name, layer in
                                     [('Via1_XX', 'Via1'), ('Via1_DC1B', 'Via1'), ('Via2_XX', 'Via2'),
                                      ('Via3_XX', 'Via3'), ('TopVia1EWNS', 'TopVia1')]}}
        self.assertEqual([r['name'] for r in C.fixtures(inventory)], C.P.consumer_protocol()['fixtures'])

    def test_units_and_complete_series_graph(self):
        row = C.parse_spef(spef(), {'probe'})['probe']
        self.assertEqual(Decimal(row['R_ohm']), 7)
        self.assertEqual(row['edges'], 2)

    def test_missing_extra_duplicate_net_rejected(self):
        for raw, expected in ((spef(), {'probe', 'other'}), (spef() + spef()[spef().index('*D_NET'):], {'probe'})):
            with self.assertRaises(ValueError):
                C.parse_spef(raw, expected)

    def test_disconnected_cycle_cannot_hide(self):
        raw = spef().replace('*END', '3 x y 1\n4 y z 1\n5 z x 1\n*END')
        with self.assertRaisesRegex(ValueError, 'Disconnected/cyclic'):
            C.parse_spef(raw, {'probe'})

    def test_duplicate_negative_nonfinite_unknown_unit_rejected(self):
        for raw in (spef().replace('2 *1:1 *3 4', '1 *1:1 *3 4'),
                    spef().replace('*3 4', '*3 -4'), spef().replace('*3 4', '*3 NaN'),
                    spef().replace('KOHM', 'MYSTERY')):
            with self.assertRaises(ValueError):
                C.parse_spef(raw, {'probe'})

    def test_repair_changes_only_empty_stanza_and_divides_two_cuts(self):
        raw = 'prefix\r\nVIARES 0 Default LEF Vias:\r\nEND VIARES\r\nsuffix\r\n'
        inventory = {'explicit_vias': {'two': {'cut_layer': 'Via1', 'cut_count': 2,
                                                'cut_bbox_um': tuple(map(Decimal, ('-.2', '-.1', '.2', '.1')))}}}
        itf = {('VIA', 'Via1'): {'FROM': 'Metal1', 'TO': 'Metal2', 'RPV': Decimal(9)}}
        result, entries = C.repair_rules(raw, inventory, itf)
        self.assertEqual(entries, ['4.5 two cuts 2 TopMetal 2 BotMetal 1 dx 400 dy 200'])
        self.assertTrue(result.startswith('prefix\r\n'))
        self.assertTrue(result.endswith('suffix\r\n'))
        with self.assertRaises(ValueError):
            C.repair_rules(result, inventory, itf)

    def test_via_subtraction_uses_matched_controls_and_policy(self):
        plan = {'fixture_rows': [{'name': 'Metal1_L50', 'segments': [('Metal1', '50', '.16')], 'via': None},
                                 {'name': 'Metal2_L50', 'segments': [('Metal2', '50', '.2')], 'via': None},
                                 {'name': 'two', 'segments': [('Metal1', '50', '.16'), ('Metal2', '50', '.2')], 'via': 'two'}],
                'corners': {'TYP': {'wire_sheet_R': {'Metal1': '.11', 'Metal2': '.088'}, 'via_per_cut_R': {'Via1': '9'}}},
                'LEF_inventory': {'explicit_vias': {'two': {'resistance_ohm': '20', 'cut_count': 2, 'cut_layer': 'Via1'}}}}
        values = {name: {'R_ohm': value} for name, value in [('Metal1_L50', '34.375'), ('Metal2_L50', '22'), ('two', '60.875')]}
        self.assertTrue(C.analyze_values(plan, 'TYP', 'owned_explicit_via_rules', values)['passed'])
        self.assertFalse(C.analyze_values(plan, 'TYP', 'retained_rules', values)['passed'])


if __name__ == '__main__':
    unittest.main()
