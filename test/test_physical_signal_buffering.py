"""Branches preserve signals only when their actual terminals and cells match."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from physical_signal_buffering import validate_plan,verify_context,verify_actual,render_tcl
from test_physical_decoder_replication import physical,mapped


def fixture():
    _,b,_=physical()
    existing=dict(cell='sg13cmos5l_buf_1',macro=False,bbox_dbu=[40,0,42,2],bbox=[40,0,42,2],orientation='R0')
    b['instances']['size_reference']=deepcopy(existing)
    op=dict(net='result',driver='gate/X',consumers=['second/D'],instance='branch',new_net='branch_net',
        cell='sg13cmos5l_buf_1',footprint_dbu=[30,0,32,2],orientation='R0')
    p=dict(schema=1,source_database_sha256='frozen',site_pitch_dbu=1,buffers=[op],added_area_um2=4)
    a=deepcopy(b);a['instances']['branch']=dict(existing,bbox_dbu=[30,0,32,2],bbox=[30,0,32,2])
    term=lambda n,p,d:dict(instance=n,pin=p,direction=d)
    a['nets']['result']['terminals'][-1]=term('branch','A','INPUT')
    a['nets']['branch_net']=dict(type='SIGNAL',ports=[],terminals=[term('branch','X','OUTPUT'),term('second','D','INPUT')])
    for n,pin in [('VPWR','VDD'),('VGND','VSS')]:a['nets'][n]['terminals'].append(term('branch',pin,'INOUT'))
    before,_,_=mapped();after=deepcopy(before)
    after['cells']['branch']=dict(type='sg13cmos5l_buf_1',parameters={},port_directions={'A':'input','X':'output'},connections={'A':[4],'X':[8]})
    after['cells']['second']['connections']['D']=[8]
    return p,b,a,before,after


class SignalBuffering(unittest.TestCase):
    def test_exact_branch_preserves_signal_and_physical_state(self):
        p,b,a,r,s=fixture()
        self.assertTrue(verify_actual(p,b,a,r,s)['connectivity']['buffer_contracted_connectivity'])
        self.assertIn('check_placement',render_tcl(p,b,'/probe/local'))

    def test_all_consumers_can_be_driven_by_one_added_buffer(self):
        p,b,a,r,s=fixture();p['buffers'][0]['consumers'].append('first/D')
        a['nets']['result']['terminals']=[t for t in a['nets']['result']['terminals'] if t['instance']!='first']
        a['nets']['branch_net']['terminals'].append(dict(instance='first',pin='D',direction='INPUT'))
        s['cells']['first']['connections']['D']=[8]
        self.assertTrue(verify_actual(p,b,a,r,s)['physical']['exact_plan_implemented'])

    def test_wrong_source_consumer_identity_and_membership_fail(self):
        for change in ('source','driver','empty','duplicate','unknown','name','net','cell','injection'):
            p,b,*_=fixture();op=p['buffers'][0]
            if change=='source':p['source_database_sha256']='other'
            if change=='driver':op['driver']='parent_a/Q'
            if change=='empty':op['consumers']=[]
            if change=='duplicate':op['consumers']*=2
            if change=='unknown':op['consumers']=['first/CLK']
            if change=='name':op['instance']='first'
            if change=='net':op['new_net']='a'
            if change=='cell':op['cell']='ff'
            if change=='injection':op['new_net']='x;exit'
            with self.subTest(change=change),self.assertRaises(ValueError):validate_plan(p,b)

    def test_geometry_and_area_fail_closed(self):
        for change in ('overlap','offrow','parity','size','area','nan','clock','port','supply'):
            p,b,*_=fixture();op=p['buffers'][0]
            if change=='overlap':op['footprint_dbu']=[0,0,2,2]
            if change=='offrow':op['footprint_dbu']=[30,1,32,3]
            if change=='parity':op['orientation']='MX'
            if change=='size':op['footprint_dbu']=[30,0,34,2]
            if change=='area':p['added_area_um2']=0
            if change=='nan':p['added_area_um2']=float('nan')
            if change=='clock':b['nets']['result']['type']='CLOCK'
            if change=='supply':b['nets']['result']['type']='POWER'
            if change=='port':b['nets']['result']['ports']=['output']
            with self.subTest(change=change),self.assertRaises(ValueError):validate_plan(p,b)

    def test_unplanned_actual_edits_fail_even_if_other_checks_pass(self):
        for change in ('power','clock','state','placement','extra','geometry','macro'):
            p,b,a,r,s=fixture()
            if change=='power':a['nets']['VPWR']['terminals']=[]
            if change=='clock':s['cells']['first']['connections']['CLK']=[3]
            if change=='state':s['cells']['first']['parameters']['INIT']='1'
            if change=='placement':a['instances']['first']['orientation']='MX'
            if change=='extra':s['cells']['extra']=deepcopy(s['cells']['branch'])
            if change=='geometry':a['rows']=[]
            if change=='macro':a['macro_pins']=[dict(instance='second',pin='D',net='wrong')]
            with self.subTest(change=change),self.assertRaises(ValueError):verify_actual(p,b,a,r,s)

    def test_two_branches_cannot_claim_the_same_consumer_or_footprint(self):
        for change in ('consumer','footprint','net'):
            p,b,*_=fixture();op=deepcopy(p['buffers'][0])
            op.update(instance='branch2',new_net='branch2_net',footprint_dbu=[35,0,37,2],consumers=['first/D'])
            if change=='consumer':op['consumers']=['second/D']
            if change=='footprint':op['footprint_dbu']=[30,0,32,2]
            if change=='net':op['new_net']='branch_net'
            p['buffers'].append(op);p['added_area_um2']=8
            with self.subTest(change=change),self.assertRaises(ValueError):validate_plan(p,b)


if __name__=='__main__':unittest.main()
