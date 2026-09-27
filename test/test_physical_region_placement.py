"""Placement permission must not accidentally authorize logic or state edits."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from physical_region_placement import select_region, validate_policy, verify_context, render_tcl
from physical_organization_edits import FIXED


def fixture():
    c = {k:[] for k in FIXED}
    c.update(database_sha256='source', dbu_per_micron=1, macro_pins=[],
             rows=[dict(name='row0',bbox_dbu=[0,0,60,2])], instances={}, nets={})
    for n, x, cell in [('state',0,'dfxtp_1'), ('a',4,'buf_1'), ('b',8,'nor2_1'),
                       ('output',12,'buf_1'), ('hold1',16,'buf_1'), ('clock',20,'buf_1')]:
        c['instances'][n] = dict(cell='sg13cmos5l_'+cell, macro=False, bbox=[x,0,x+2,2],
                                 bbox_dbu=[x,0,x+2,2], orientation='R0')
    def net(name, ends, ports=(), kind='SIGNAL'):
        c['nets'][name] = dict(type=kind, ports=list(ports), terminals=[
            dict(instance=n, pin=p, direction=d) for n,p,d in ends])
    net('data', [('state','Q','OUTPUT'),('a','A','INPUT')])
    net('first', [('a','X','OUTPUT'),('b','A','INPUT'),('hold1','A','INPUT')])
    net('held', [('hold1','X','OUTPUT'),('b','B','INPUT')])
    net('last', [('b','Y','OUTPUT'),('output','A','INPUT')])
    net('out', [('output','X','OUTPUT')], ['out'])
    net('clock', [('clock','X','OUTPUT'),('state','CLK','INPUT')], kind='CLOCK')
    net('VDD', [(n,'VDD','INOUT') for n in c['instances']], kind='POWER')
    s = select_region(c,'out',4)
    p = dict(schema=1,source_database_sha256='source',output_net='out',depth=4,protected=[],
             instances=s['instances'],max_instances=10,site_pitch_dbu=1,max_displacement_um=40)
    return p,c


class RegionPlacement(unittest.TestCase):
    def test_joint_moves_preserve_identity_with_same_area(self):
        p,b=fixture();a=deepcopy(b)
        a['instances']['a'].update(bbox=[30,0,32,2],bbox_dbu=[30,0,32,2])
        a['instances']['b'].update(bbox=[32,0,34,2],bbox_dbu=[32,0,34,2])
        proof=verify_context(p,b,a)
        self.assertEqual(proof['moved_instances'],2)
        self.assertEqual(proof['added_area_um2'],0)

    def test_cone_excludes_state_hold_clock_and_package_driver(self):
        p,c=fixture()
        self.assertEqual(p['instances'],['a','b'])
        self.assertEqual(select_region(c,'out',4,['b'])['instances'],['a'])
        self.assertEqual(select_region(c,'out',1)['instances'],['b'])

    def test_policy_cannot_enlarge_region_or_change_source(self):
        for mode in ['source','state','hold','clock','output','bound','nan','injection']:
            p,c=fixture()
            if mode=='source':p['source_database_sha256']='other'
            elif mode=='bound':p['max_instances']=1
            elif mode=='nan':p['max_displacement_um']=float('nan')
            elif mode=='injection':p['instances'].append('a;exit')
            else:p['instances'].append(mode if mode!='hold' else 'hold1')
            with self.subTest(mode=mode),self.assertRaises(ValueError):validate_policy(p,c)

    def test_physical_or_logical_mutation_rejected(self):
        for mode in ['state','clock','hold1','output','cell','size','power','signal','macro','rows','extra']:
            p,b=fixture();a=deepcopy(b)
            if mode in ['state','clock','hold1','output']:a['instances'][mode]['orientation']='MY'
            elif mode=='cell':a['instances']['a']['cell']='sg13cmos5l_buf_4'
            elif mode=='size':a['instances']['a']['bbox_dbu'][2]+=1
            elif mode=='power':a['nets']['VDD']['terminals'].pop()
            elif mode=='signal':a['nets']['first']['terminals'].pop()
            elif mode=='macro':a['macro_pins']=[{}]
            elif mode=='rows':a['rows']=[]
            elif mode=='extra':a['instances']['extra']=deepcopy(a['instances']['a'])
            with self.subTest(mode=mode),self.assertRaises(ValueError):verify_context(p,b,a)

    def test_geometry_checks_actual_placement_not_just_membership(self):
        for mode in ['overlap','offrow','parity','displacement','blockage']:
            p,b=fixture();a=deepcopy(b);box=[30,0,32,2]
            if mode=='overlap':box=[8,0,10,2]
            if mode=='offrow':box=[30,1,32,3]
            if mode=='parity':a['instances']['a']['orientation']='MX'
            if mode=='displacement':p['max_displacement_um']=5
            if mode=='blockage':
                b['placement_blockages']=[dict(bbox_dbu=[29,0,34,2])]
                a['placement_blockages']=deepcopy(b['placement_blockages'])
            a['instances']['a'].update(bbox=box[:],bbox_dbu=box[:])
            with self.subTest(mode=mode),self.assertRaises(ValueError):verify_context(p,b,a)

    def test_timing_placement_does_not_keep_virtual_cell_edits(self):
        p,c=fixture();tcl=render_tcl(p,c,'/probe/timed',True)
        self.assertIn('-keep_resize_below_overflow 0',tcl)
        self.assertIn('$inst setPlacementStatus FIRM',tcl)
        self.assertIn('$inst setPlacementStatus [dict get $original_status $name]',tcl)
        with self.assertRaises(ValueError):render_tcl(p,c,'/probe/x;exit')

    def test_empty_row_requires_independent_definition_and_matching_rails(self):
        p,b=fixture();b['rows'].append(dict(name='row1',bbox_dbu=[0,2,60,4]));a=deepcopy(b)
        a['instances']['a'].update(bbox=[30,2,32,4],bbox_dbu=[30,2,32,4],orientation='MX')
        definitions={n:dict(orientation=o,site_width_dbu=1,site_height_dbu=2)
                     for n,o in [('row0','R0'),('row1','MX')]}
        with self.assertRaises(ValueError):verify_context(p,b,a)
        self.assertEqual(verify_context(p,b,a,definitions)['moved_instances'],1)
        for mode in ['missing','height','width','original_rails','new_rails']:
            d=deepcopy(definitions)
            if mode=='missing':d.pop('row1')
            elif mode=='height':d['row1']['site_height_dbu']=3
            elif mode=='width':d['row1']['site_width_dbu']=2
            elif mode=='original_rails':d['row0']['orientation']='MX'
            else:d['row1']['orientation']='R0'
            with self.subTest(mode=mode),self.assertRaises(ValueError):verify_context(p,b,a,d)


if __name__=='__main__':unittest.main()
