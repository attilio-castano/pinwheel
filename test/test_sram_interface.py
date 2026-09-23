"""Checks for misleading traffic counts and incomplete geometric comparisons."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from sram_interface import analyze, hpwl, incident_points, traffic_groups, union_area


def term(instance, pin, direction='INPUT'):
    return dict(instance=instance,pin=pin,direction=direction)


def context():
    return dict(instances={
        'sram':dict(cell='macro',macro=True,bbox_dbu=[0,10,100,30],orientation='R0'),
        'buffer':dict(cell='sg13cmos5l_buf_4',macro=False),
        'delay':dict(cell='sg13cmos5l_dlygate4sd3_1',macro=False),
        'flop':dict(cell='sg13cmos5l_dfrbp_1',macro=False),
        'tie':dict(cell='sg13cmos5l_tielo',macro=False),
        'load':dict(cell='sg13cmos5l_buf_1',macro=False)}, nets={
        'upstream':dict(type='SIGNAL',terminals=[term('flop','Q','OUTPUT'),term('buffer','A')],ports=[]),
        'middle':dict(type='SIGNAL',terminals=[term('buffer','X','OUTPUT'),term('delay','A')],ports=[]),
        'upload':dict(type='SIGNAL',terminals=[term('delay','X','OUTPUT'),term('sram','A_DIN[0]')],ports=[]),
        'input':dict(type='SIGNAL',terminals=[term('flop','D'),term('load','A')],ports=['host']),
        'fixed':dict(type='SIGNAL',terminals=[term('tie','L_LO','OUTPUT'),term('sram','A_BIST_EN')],ports=[])})


class TrafficTests(unittest.TestCase):
    def test_buffer_and_hold_chain_remains_upload(self):
        labels=traffic_groups(context())
        for n in ['upload','middle','upstream']:
            self.assertEqual(labels[n],'upload')

    def test_no_traversal_through_register(self):
        self.assertEqual(traffic_groups(context())['input'],'transit')

    def test_static_pins_require_actual_constant_driver(self):
        c=context();self.assertEqual(traffic_groups(c)['fixed'],'static')
        c['instances']['tie']['cell']='sg13cmos5l_nand2_1'
        with self.assertRaisesRegex(ValueError,'lacks a verified tie'):
            traffic_groups(c)

    def test_unknown_buffer_pin_rejected(self):
        c=context();c['nets']['middle']['terminals'][0]['pin']='Y'
        with self.assertRaisesRegex(ValueError,'Unexpected buffer interface'):
            traffic_groups(c)

    def test_active_constant_rejected(self):
        c=context();c['nets']['fixed']['terminals'][1]['pin']='A_DIN[1]'
        with self.assertRaisesRegex(ValueError,'constant on active'):
            traffic_groups(c)


class GeometryTests(unittest.TestCase):
    def test_union_does_not_double_count_power_over_obstruction(self):
        self.assertEqual(union_area([[0,0,10,10],[5,5,15,15],[0,0,10,10]]),175)

    def test_all_shapes_and_other_terminals_enter_projection(self):
        c=context()
        g=dict(pins={'tie/L_LO':[dict(bbox_dbu=[45,0,47,2])],
                     'sram/A_BIST_EN':[dict(bbox_dbu=[45,10,47,12]),dict(bbox_dbu=[47,10,49,12])]})
        before=incident_points(c,g,'fixed')
        after=incident_points(c,g,'fixed',['sram'])
        self.assertEqual(before,[(46,1),(47,11)])
        self.assertEqual(after,[(46,1),(47,29)])
        self.assertEqual(hpwl(after)-hpwl(before),18)

    def test_mismatched_checkpoint_rejected(self):
        with self.assertRaisesRegex(ValueError,'different checkpoints'):
            analyze({'database_sha256':'a'},{'database_sha256':'b'},[],{'database_sha256':'a'})

    def test_units_mismatch_rejected(self):
        with self.assertRaisesRegex(ValueError,'coordinate units'):
            analyze({'database_sha256':'a','dbu_per_micron':1000},
                    {'database_sha256':'a','dbu_per_micron':1},[],
                    {'database_sha256':'a','dbu_per_micron':1000})

    def test_empty_pins_rejected(self):
        with self.assertRaisesRegex(ValueError,'Empty pin set'):
            hpwl([])


if __name__=='__main__':
    unittest.main()
