"""Counterexamples to incomplete region ownership and free cell displacement."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from word_region import (FF, Region, SpanCost, bind_readback, bind_state,
                         collisions, clock_geometry, exchange_sites, hold_arc_changes)


def example():
    kinds={'serial':FF,'other':FF,'pure':'sg13cmos5l_buf_1',
           'mixed':'sg13cmos5l_and2_1','delay':'sg13cmos5l_dlygate4sd3_1',
           'memory.storage0':'SRAM','memory.storage1':'SRAM'}
    cells={n:dict(cell=k,macro=k=='SRAM',bbox_dbu=[j*20,0,j*20+10,10],orientation='R0')
           for j,(n,k) in enumerate(kinds.items())}
    def net(*terms,kind='SIGNAL',ports=()):
        return dict(type=kind,ports=list(ports),terminals=[dict(instance=n,pin=p,direction=d)
                    for n,p,d in terms])
    nets={
      'word':net(('serial','Q','OUTPUT'),('serial','D','INPUT'),('pure','A','INPUT')),
      'buffered':net(('pure','X','OUTPUT'),('mixed','A','INPUT'),('delay','A','INPUT')),
      'upload':net(('delay','X','OUTPUT'),('memory.storage0','A_DIN[0]','INPUT'),
                   ('memory.storage1','A_DIN[0]','INPUT')),
      'q_other':net(('other','Q','OUTPUT'),('mixed','B','INPUT')),
      'mixed_out':net(('mixed','X','OUTPUT'),('other','D','INPUT'),ports=('out',)),
      'clock':net(('serial','CLK','INPUT'),('other','CLK','INPUT'),kind='CLOCK',ports=('clk',)),
    }
    c=dict(instances=cells,nets=nets,dbu_per_micron=1,database_sha256='frozen',
           ports=[dict(name='out',bbox_dbu=[200,0,200,0]),dict(name='clk',bbox_dbu=[0,0,0,0])])
    g=dict(database_sha256='frozen',pins={t['instance']+'/'+t['pin']:[{'bbox_dbu':
           [cells[t['instance']]['bbox_dbu'][0]+2,2]*2}]
           for i in nets.values() for t in i['terminals']})
    s={'serial':dict(owner='serial_receiver'),'other':dict(owner='loader')}
    return c,g,s


class OwnershipTests(unittest.TestCase):
    def test_mixed_state_stops_private_region_but_endpoint_still_counted(self):
        c,g,s=example();r=Region(c,s,1)
        self.assertIn('pure',r.members()['members'])
        self.assertNotIn('mixed',r.members()['members'])
        self.assertIn(('loader',True),[(e['owner'],e['mixed']) for e in r.endpoints()])
        self.assertIn('package_outputs',[e['owner'] for e in r.endpoints()])

    def test_word_feedback_is_internal_and_other_state_is_boundary(self):
        c,g,s=example();r=Region(c,s,1)
        self.assertFalse(r.support('word')[1])
        self.assertTrue(r.support('mixed_out')[1])
        self.assertNotIn('other',r.members()['members'])

    def test_unknown_state_cell_cannot_be_assumed_combinational(self):
        c,g,s=example();c['instances']['pure']['cell']='sg13cmos5l_unknown_ff'
        with self.assertRaisesRegex(ValueError,'Unknown combinational'):Region(c,s,1)

    def test_cycle_outside_data_cone_rejected(self):
        c,g,s=example()
        c['nets']['buffered']['terminals'].remove(dict(instance='mixed',pin='A',direction='INPUT'))
        c['nets']['mixed_out']['terminals'].append(dict(instance='mixed',pin='A',direction='INPUT'))
        with self.assertRaisesRegex(ValueError,'cycle'):Region(c,s,1)

    def test_state_alias_cannot_assign_one_ff_twice(self):
        c,g,s=example();m={'cells':{'serial':{'type':FF,'connections':{'Q':[2]}},
            'other':{'type':FF,'connections':{'Q':[3]}}},'netnames':{
            'controller.engine.x':{'bits':[2]},'controller.engine.y':{'bits':[2]}}}
        d={'registers':[dict(name='engine.x',reference='r_x',width=1),dict(name='engine.y',reference='r_y',width=1)]}
        sem={'registers':[dict(name='controller.r_x',width=1,owner='serial_receiver'),
                          dict(name='controller.r_y',width=1,owner='loader')]}
        with self.assertRaisesRegex(ValueError,'Duplicate or missing'):bind_state(c,m,d,sem)


class ReadbackTests(unittest.TestCase):
    def fixture(self):
        c=dict(instances={'b':dict(cell='sg13cmos5l_buf_1')},nets={
            'in':dict(type='SIGNAL',ports=['i'],terminals=[dict(instance='b',pin='A',direction='INPUT')]),
            'out':dict(type='SIGNAL',ports=['o'],terminals=[dict(instance='b',pin='X',direction='OUTPUT')]),
            'unused':dict(type='SIGNAL',ports=[],terminals=[])})
        m=dict(cells={'b':dict(type='sg13cmos5l_buf_1',connections={'A':[2],'X':[3]},
                              port_directions={'A':'input','X':'output'})},
               ports={'i':{'bits':[2]},'o':{'bits':[3]}})
        return c,m

    def test_empty_database_alias_does_not_invent_connection(self):
        c,m=self.fixture();self.assertEqual(bind_readback(c,m),{'in':2,'out':3})

    def test_rewired_package_pin_rejected(self):
        c,m=self.fixture();m['ports']['o']['bits']=[2]
        with self.assertRaisesRegex(ValueError,'splits'):bind_readback(c,m)

    def test_net_merge_rejected(self):
        c,m=self.fixture();m['ports']['o']['bits']=[2];m['cells']['b']['connections']['X']=[2]
        with self.assertRaisesRegex(ValueError,'merges'):bind_readback(c,m)

    def test_unreported_physical_pin_rejected(self):
        c,m=self.fixture();c['nets']['out']['terminals']=[]
        with self.assertRaisesRegex(ValueError,'Unaccounted'):bind_readback(c,m)


class GeometryTests(unittest.TestCase):
    def test_external_consumer_and_displaced_cell_costs_are_included(self):
        c,g,s=example();g['pins']['other/D']=[{'bbox_dbu':[102,2,102,2]}];cost=SpanCost(c,g)
        # Moving the pure buffer toward the SRAM worsens its incoming net and
        # changes its decoder branch; moving the decoder also charges q_other
        # and the distant package output. No region-only net truncation.
        moves={'pure':(20,0),'mixed':(-20,0)}
        report=cost.report(moves)
        self.assertEqual(set(report['nets']),{'word','buffered','q_other','mixed_out'})
        self.assertEqual(report['nets']['mixed_out']['change_um'],20)
        changed=deepcopy(g);changed['pins']['other/Q']=[{'bbox_dbu':[1000,2,1000,2]}]
        self.assertNotEqual(SpanCost(c,changed).report(moves)['totals']['all']['change_um'],
                            report['totals']['all']['change_um'])

    def test_clock_pin_multiset_is_stronger_than_equal_span(self):
        c,g,s=example()
        self.assertEqual(clock_geometry(c,g,{'serial':(20,0),'other':(-20,0)})['changed_geometry_nets'],[])
        # Collinear motion can leave HPWL unchanged while changing pin geometry.
        g['pins']['serial/CLK']=[{'bbox_dbu':[12,2,12,2]}]
        self.assertEqual(SpanCost(c,g).report({'serial':(1,0)})['totals']['clock']['change_um'],0)
        self.assertEqual(clock_geometry(c,g,{'serial':(1,0)})['changed_geometry_nets'],['clock'])

    def test_unchanged_hold_cell_does_not_imply_unchanged_hold_wire(self):
        c,g,s=example();changes=hold_arc_changes(c,g,{'pure':(10,0)})
        self.assertEqual(changes['shortened_arcs'],2)
        self.assertEqual(changes['largest_shortening_um'],10)
        self.assertEqual(hold_arc_changes(c,g,{'pure':(-10,0)})['largest_shortening_um'],0)

    def test_equal_footprint_exchange_preserves_occupancy(self):
        c,g,s=example();self.assertEqual(collisions(c,{'pure':(20,0),'mixed':(-20,0)}),[])
        self.assertIn(('mixed','pure'),collisions(c,{'pure':(20,0)}))

    def test_exchange_preserves_clock_and_delay_and_costs_each_pair(self):
        c,g,s=example();r=Region(c,s,1);cost=SpanCost(c,g)
        ex=exchange_sites(c,r,cost,100,max_pairs=4)
        self.assertNotIn('delay',ex['moves'])
        self.assertFalse(collisions(c,ex['moves']))
        self.assertFalse(clock_geometry(c,g,ex['moves'])['changed_geometry_nets'])
        self.assertAlmostEqual(sum(p['gain_um'] for p in ex['pairs']),
                               -cost.report(ex['moves'])['totals'].get('all',{}).get('change_um',0))


if __name__=='__main__':unittest.main()
