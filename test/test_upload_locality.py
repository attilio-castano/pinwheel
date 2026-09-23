"""Reject misleading SRAM-only ownership and optimistic packing claims."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from upload_locality import Distribution,FF,free_rows,width_capacity,payload_projection,stage_census


def example():
    inst={
        'source':{'cell':FF,'macro':False},
        'shared':{'cell':'sg13cmos5l_buf_1','macro':False},
        'only':{'cell':'sg13cmos5l_dlygate4sd3_1','macro':False},
        'decode':{'cell':'sg13cmos5l_nand2_1','macro':False},
        'm0':{'cell':'SRAM','macro':True},'m1':{'cell':'SRAM','macro':True}}
    def net(items,kind='SIGNAL',ports=()):
        return {'type':kind,'ports':list(ports),'terminals':[
            {'instance':i,'pin':p,'direction':d} for i,p,d in items]}
    nets={
        'root':net([('source','Q','OUTPUT'),('shared','A','INPUT')]),
        'branch':net([('shared','X','OUTPUT'),('decode','A','INPUT'),('only','A','INPUT')]),
        'memory':net([('only','X','OUTPUT'),('m0','A_DIN[0]','INPUT'),('m1','A_DIN[0]','INPUT')])}
    return {'instances':inst,'nets':nets}


class DistributionTests(unittest.TestCase):
    def test_shared_source_does_not_make_decoder_branch_exclusive(self):
        c=example();c['nets']['branch']['terminals'].remove({'instance':'decode','pin':'A','direction':'INPUT'})
        c['instances']['other']={'cell':'sg13cmos5l_buf_2','macro':False}
        c['nets']['root']['terminals'].append({'instance':'other','pin':'A','direction':'INPUT'})
        c['nets']['unrelated']={'type':'SIGNAL','ports':[], 'terminals':[
            {'instance':'other','pin':'X','direction':'OUTPUT'},
            {'instance':'decode','pin':'A','direction':'INPUT'}]}
        d=Distribution(c)
        self.assertEqual(d.role('root'),'shared')
        self.assertEqual(d.role('branch'),'sram-only')
        self.assertEqual(d.role('unrelated'),'other-consumers')

    def test_stage_feed_stops_before_shared_consumer(self):
        d=Distribution(example())
        bit=d.payload(['m0','m1'],1)[0]
        self.assertEqual(bit['source_net'],'branch')
        self.assertEqual(bit['source_ff'],'source')
        self.assertEqual(d.role('memory'),'sram-only')
        self.assertEqual(d.role('branch'),'shared')

    def test_multiple_driver_rejected(self):
        c=example();c['nets']['root']['terminals'].append({'instance':'decode','pin':'X','direction':'OUTPUT'})
        with self.assertRaisesRegex(ValueError,'Multiple drivers'):Distribution(c)

    def test_cycle_rejected(self):
        c=example();c['nets']['root']['terminals']=[{'instance':'only','pin':'X','direction':'OUTPUT'},
            {'instance':'shared','pin':'A','direction':'INPUT'}]
        c['nets']['memory']['terminals']=c['nets']['memory']['terminals'][1:]
        with self.assertRaisesRegex(ValueError,'cycle'):Distribution(c).leaves('root')

    def test_replica_root_mismatch_rejected(self):
        c=example();c['instances']['source2']={'cell':FF,'macro':False}
        pin=c['nets']['memory']['terminals'].pop()
        c['nets']['second']={'type':'SIGNAL','ports':[],'terminals':[
            {'instance':'source2','pin':'Q','direction':'OUTPUT'},pin]}
        with self.assertRaisesRegex(ValueError,'roots disagree'):Distribution(c).payload(['m0','m1'],1)

    def test_unknown_logic_is_not_a_transparent_buffer(self):
        c=example();c['instances']['only']['cell']='sg13cmos5l_inv_1'
        with self.assertRaisesRegex(ValueError,'expected FF Q'):Distribution(c).payload(['m0','m1'],1)


class GeometryTests(unittest.TestCase):
    def test_free_union_counts_overlaps_once(self):
        c={'rows':[{'bbox_dbu':[0,0,100,10]}], 'instances':{
            'a':{'bbox_dbu':[10,0,30,10]},'b':{'bbox_dbu':[20,0,40,10]},
            'touch':{'bbox_dbu':[40,10,60,20]}}}
        area,free=free_rows(c,[0,0,100,10])
        self.assertEqual(area,1000)
        self.assertEqual(free,[[0,0,10,10],[40,0,100,10]])
        self.assertEqual(width_capacity(free,30,10),2)

    def test_total_area_is_not_contiguous_capacity(self):
        free=[[0,0,9,10],[11,0,20,10]]
        self.assertEqual(width_capacity(free,10,10),0)
        self.assertEqual(width_capacity(free,9,10),2)
        self.assertEqual(width_capacity(free,9,11),0)

    def test_release_only_named_instances_and_whole_rows(self):
        c={'rows':[{'bbox_dbu':[0,0,100,10]}], 'instances':{
            'remove':{'bbox_dbu':[10,0,40,10]},'keep':{'bbox_dbu':[50,0,70,10]}}}
        self.assertEqual(free_rows(c,[0,0,100,10],{'remove'})[1],[[0,0,50,10],[70,0,100,10]])
        self.assertEqual(free_rows(c,[0,1,100,10]),(0,[]))

    def test_projection_preserves_other_sinks_and_excludes_power(self):
        c=example();c.update(dbu_per_micron=1,rows=[{'bbox_dbu':[0,0,100,10]}])
        c['nets']['supply']={'type':'POWER','ports':['VDD'],'terminals':[
            {'instance':'only','pin':'VDD','direction':'INPUT'}]}
        coordinates={('source','Q'):(0,30),('shared','A'):(10,30),('shared','X'):(20,30),
            ('decode','A'):(100,30),('only','A'):(30,30),('only','X'):(40,30),
            ('m0','A_DIN[0]'):(50,20),('m1','A_DIN[0]'):(50,40)}
        g={'pins':{i+'/'+p:[{'bbox_dbu':[x,y,x,y]}] for (i,p),(x,y) in coordinates.items()}}
        d=Distribution(c);bits=d.payload(['m0','m1'],1)
        result=payload_projection(c,g,d,bits,{'only'},[[0,0,100,10]],2)
        # Old branch spans 80 + old macro branch 30; new feed remains 80 wide
        # because the decoder at x=100 stays, plus 25 to reach the stage row.
        self.assertEqual(result['affected_nets'],2)
        self.assertEqual(result['before_um'],110)
        self.assertEqual(result['after_um'],140)
        c2=deepcopy(c);g2=deepcopy(g)
        g2['pins']['decode/A']=[{'bbox_dbu':[200,30,200,30]}]
        r2=payload_projection(c2,g2,Distribution(c2),bits,{'only'},[[0,0,100,10]],2)
        self.assertEqual(r2['before_um']-result['before_um'],100)
        self.assertEqual(r2['after_um']-result['after_um'],100)


class MappedStageTests(unittest.TestCase):
    def module(self):
        m={'ports':{'clk':{'bits':[2]}},'netnames':{},'cells':{}}
        slot=0
        for name,width in [('upload_data',64),('upload_address',6),('upload_pending',1)]:
            bits=[]
            for k in range(width):
                q,d=100+slot,200+slot;bits.append(q)
                m['cells']['ff'+str(slot)]={'type':FF,'port_directions':{'CLK':'input','RESET_B':'input','D':'input','Q':'output'},
                    'connections':{'CLK':[2],'RESET_B':['1'],'D':[d],'Q':[q]}}
                kind='sg13cmos5l_mux2_1' if k<width-2 else 'sg13cmos5l_a21oi_1'
                m['cells']['driver'+str(slot)]={'type':kind,'port_directions':{'X':'output'},'connections':{'X':[d]}}
                slot+=1
            m['netnames']['controller.r_'+name]={'bits':bits}
        return m

    def test_count_actual_payload_muxes_instead_of_registers(self):
        r=stage_census(self.module())
        self.assertEqual(r['total_ff'],71)
        self.assertEqual(r['payload_mux_pairs'],62)
        self.assertEqual(r['groups']['upload_data']['input_cells']['sg13cmos5l_a21oi_1'],2)

    def test_changed_clock_rejected(self):
        m=self.module();m['cells']['ff0']['connections']['CLK']=[3]
        with self.assertRaisesRegex(ValueError,'clock/reset'):stage_census(m)

    def test_aliased_stage_state_rejected(self):
        m=self.module();m['netnames']['controller.r_upload_address']['bits'][0]=100
        with self.assertRaisesRegex(ValueError,'distinct mapped FF'):stage_census(m)


if __name__=='__main__':unittest.main()
