"""PG-diode HOST controls: real failure geometry, conservation and bridge seams."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_pg_diode as P

ROOT=Path(__file__).resolve().parents[1]
FIX=ROOT/'test/fixtures'
PROFILE=FIX/'streaming_8x4_pg_diode_profile.lef'
GEOMETRY=FIX/'streaming_8x4_pg_diode_geometry.def'


def actual_model():
    text=PROFILE.read_text()
    return P.profile_text(text,text)


def geo():
    return dict(rows=[dict(y=3780+i*3780,orient='N' if i%2==0 else 'FS') for i in range(186)],
        tracks={('Metal2','X'):(480,3591,480),('Metal1','Y'):(420,1691,420)})


def fixture():
    # Measured ANTENNA_115 / net343: its A pin lies beneath the VPWR strap.
    inst=dict(master=P.MASTER,box=(1112160,461160,1113600,464940),orient='MX',status='PLACED')
    return dict(instances={'ANTENNA_115':inst},terminals={('ANTENNA_115','A'):('INPUT','SIGNAL','net343')},
        nets={'net343':('SIGNAL',1,1),'VPWR':('POWER',0,0)},ports={'port':('OUTPUT','SIGNAL','net343')},
        public=[],pg=[('VPWR','Metal2',(1112380,7340,1113380,703300),'0')],blockages=[],
        special=[('VPWR','Metal2',(1112380,7340,1113380,703300),'STRIPE')],special_nets=['VPWR'])


class PGDiode(unittest.TestCase):
    def test_actual_failure_before_pg_safe_site_after(self):
        model=actual_model();current=fixture();old=current['instances']['ANTENNA_115']
        self.assertIsNone(P.access(old['box'][0],old['box'][1],old['orient'],model,geo(),current['pg']))
        moves=P.plan(current,['ANTENNA_115'],geo(),model,'A')
        self.assertEqual(len(moves),1);move=moves[0]
        self.assertNotEqual(move['box'],old['box']);self.assertLessEqual(abs(move['x']-old['box'][0]),16*480)
        self.assertIsNotNone(P.access(move['x'],move['y'],move['orient'],model,geo(),current['pg']))
        self.assertEqual(model['spacing'],{'Metal1':600,'Metal2':600})
        self.assertEqual(move['certificate']['via'],'Via1_YY')

    def test_all_four_orientations_are_bbox_relative(self):
        rect=(380,2080,980,2680)
        self.assertEqual(P.transform(rect,10,20,'R0'),(390,2100,990,2700))
        self.assertEqual(P.transform(rect,10,20,'MX'),(390,1120,990,1720))
        self.assertEqual(P.transform(rect,10,20,'MY'),(470,2100,1070,2700))
        self.assertEqual(P.transform(rect,10,20,'R180'),(470,1120,1070,1720))
        with self.assertRaises(ValueError):P.transform(rect,0,0,'R90')

    def test_preserve_all_masters_terminals_pg_and_existing_placements(self):
        current=fixture();moves=P.plan(current,['ANTENNA_115'],geo(),actual_model(),'A');after=copy.deepcopy(current)
        m=moves[0];after['instances'][m['instance']].update(box=tuple(m['box']),orient=m['orient'])
        P.unchanged(current,after,moves)
        for key in ('terminals','nets','ports','pg','blockages'):
            bad=copy.deepcopy(after)
            if isinstance(bad[key],dict):bad[key]={}
            else:bad[key]=['changed']
            with self.assertRaises(ValueError):P.unchanged(current,bad,moves)
        bad=copy.deepcopy(after);bad['instances']['ANTENNA_115']['master']='different'
        with self.assertRaises(ValueError):P.unchanged(current,bad,moves)

    def test_target_detection_is_unique_new_names_not_39_ceiling(self):
        current=fixture();before=copy.deepcopy(current)
        before['instances']={};before['terminals']={}
        self.assertEqual(P.targets(before,current),['ANTENNA_115'])
        for i in range(116,156):
            current['instances']['ANTENNA_'+str(i)]=dict(current['instances']['ANTENNA_115'])
            current['terminals']['ANTENNA_'+str(i),'A']=('INPUT','SIGNAL','net343')
        self.assertEqual(len(P.targets(before,current)),41)
        with self.assertRaises(ValueError):P.targets(before,current,['ANTENNA_115','ANTENNA_115'])
        before=copy.deepcopy(current);bad=copy.deepcopy(current);del bad['instances']['ANTENNA_115']
        with self.assertRaises(ValueError):P.targets(before,bad)
        bad=copy.deepcopy(current);bad['instances']['ANTENNA_115']['master']='changed'
        with self.assertRaises(ValueError):P.targets(before,bad)

    def test_fixed_cells_blockages_and_finite_search_reject(self):
        current=fixture();current['blockages']=[((2880,3780,1721280,706860),'0')]
        with self.assertRaises(ValueError):P.plan(current,['ANTENNA_115'],geo(),actual_model(),'A')
        current=fixture();current['instances']['fixed']=dict(master='cell',box=P.CORE,orient='R0',status='FIRM')
        with self.assertRaises(ValueError):P.plan(current,['ANTENNA_115'],geo(),actual_model(),'A')
        with self.assertRaises(ValueError):P.plan(fixture(),['ANTENNA_115'],geo(),actual_model(),'C')

    def test_pg_envelope_is_rule_clearance_not_only_overlap(self):
        current=fixture();model=actual_model();x=1112160-3*480
        # This clears direct overlap but remains inside the full .60um+via margin.
        self.assertIsNone(P.access(x,461160,'MX',model,geo(),current['pg']))
        self.assertIsNotNone(P.access(x-480,461160,'MX',model,geo(),current['pg']))
        model=copy.deepcopy(model);model['via']['Metal1']=(-2000,-2000,2000,2000)
        self.assertIsNone(P.access(x-480,461160,'MX',model,geo(),current['pg']))

    def test_offsite_wrong_master_wrong_net_reject(self):
        for field,bad in [('master','other'),('box',(1112161,461160,1113601,464940))]:
            value=fixture();value['instances']['ANTENNA_115'][field]=bad
            with self.assertRaises(ValueError):
                names=P.targets(value,value,['ANTENNA_115']);P.plan(value,names,geo(),actual_model(),'A')
        value=fixture();value['terminals']['ANTENNA_115','A']=('INPUT','SIGNAL','missing')
        with self.assertRaises(ValueError):P.targets(value,value,['ANTENNA_115'])

    def test_bridge_reachable_in_both_unmodified_callers(self):
        # Native caller-body hashes/injection are separately admitted by the
        # new flow controller; this portable control checks the public bridge.
        body=P.hook_tcl('/request.json',python_executable='/python',helper_path='/helper.py',initial_names=['ANTENNA_115'])
        self.assertIn('rename ::repair_antennas ::pgd::canonical_repair_antennas',body)
        self.assertIn('set result [::pgd::canonical_repair_antennas {*}$args]',body)
        self.assertLess(body.index('set result [::pgd::canonical_repair_antennas'),body.index('::pgd::apply $d ""'))
        self.assertIn('proc pg_diode_apply_existing {names}',body)
        self.assertIn('grt::start_incremental',body);self.assertIn('grt::end_incremental',body)
        self.assertNotIn('global_route -start_incremental',body)
        self.assertIn('check_placement -verbose',body)
        self.assertIn('return $result',body)
        self.assertNotIn('getId',body)

    def test_real_official_rows_and_exact_source_request(self):
        g=P.geometry(GEOMETRY);self.assertEqual(len(g['rows']),186)
        self.assertEqual(g['tracks']['Metal2','X'],(480,3591,480))
        req=P.make_request(PROFILE,PROFILE,
            native_tech_lef='/work/tech.lef',native_cell_lef='/work/cell.lef')
        self.assertEqual(req['tech_lef'],'/work/tech.lef');self.assertEqual(req['source_sha256'],P.sha(P.__file__))
        with self.assertRaises(ValueError):P.dbu('0.0001')
        with self.assertRaises(ValueError):P.literal('/unsafe{path}')

    def test_fixture_hashes_and_native_full_lef_binding(self):
        expected=json.loads((FIX/'streaming_8x4_pg_diode_fixtures.json').read_text())
        self.assertEqual(expected['fixtures'],{GEOMETRY.name:P.sha(GEOMETRY),PROFILE.name:P.sha(PROFILE)})
        self.assertEqual(expected['source_tech_sha256'],P.TECH_SHA)
        # Small exact excerpts are HOST geometry fixtures, never substitutes
        # for the complete Native LEF authority.
        req=P.make_request(PROFILE,PROFILE)
        with self.assertRaises(ValueError):P.profile(PROFILE,PROFILE,req)

    def test_live_snapshot_complete_census_and_duplicate_rejection(self):
        text='\n'.join(['SNAPSHOT\t2','TOP\t'+P.TOP,
            'INST\tANTENNA_115\t'+P.MASTER+'\t1112160\t461160\t1113600\t464940\tMX\tPLACED',
            'ITERM\tANTENNA_115\tA\tINPUT\tSIGNAL\tnet343',
            'NET\tnet343\tSIGNAL\t1\t1\t0','NET\tVPWR\tPOWER\t0\t0\t1',
            'BTERM\tport\tOUTPUT\tSIGNAL\tnet343',
            'PG\tVPWR\tMetal2\t1112380\t7340\t1113380\t703300\t0',
            'SPECIAL\tVPWR\tMetal2\t1112380\t7340\t1113380\t703300\tSTRIPE'])+'\n'
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'snapshot.tsv';path.write_text(text)
            value=P.read_snapshot(path);self.assertEqual(value,fixture())
            self.assertEqual(len(P.plan(value,P.targets(value,value,['ANTENNA_115']),geo(),actual_model(),'A')),1)
            for bad in (text.replace('SIGNAL\t1\t1','SIGNAL\t2\t1'),
                        text+text.splitlines()[2]+'\n',text.replace('\tPLACED','\tFIRM'),
                        '\n'.join(l for l in text.splitlines() if not l.startswith('SPECIAL'))+'\n',
                        text.replace('POWER\t0\t0\t1','POWER\t0\t0\t0')):
                path.write_text(bad)
                with self.assertRaises(ValueError):
                    value=P.read_snapshot(path);P.targets(value,value,['ANTENNA_115'])

    def test_global_B_heap_order_is_complete_unique_and_manhattan_minimal(self):
        g=dict(rows=[dict(y=y,orient='N') for y in (0,3780,7560)])
        box=(480,3780,1920,7560)
        with patch.object(P,'CORE',(0,0,3360,11340)):
            actual=list(P.search_sites(box,g,'B'))
        expected=sorted([(k,x,row['y']) for k,row in enumerate(g['rows']) for x in range(0,1921,480)],
            key=lambda r:(abs(r[1]-box[0])+abs(r[2]-box[1]),abs(r[2]-box[1]),r[2],r[1]))
        self.assertEqual(actual,expected);self.assertEqual(len(actual),15);self.assertEqual(len(set(actual)),15)
        original=list(P.search_sites((1112160,461160,1113600,464940),geo(),'A'))
        self.assertEqual([r[1]-1112160 for r in original],[0]+[s*k*480 for k in range(1,17) for s in (-1,1)])

    def test_global_B_selects_nearest_admissible_site_and_keeps_non_targets(self):
        value=fixture();value['special']=[];value['pg']=[]
        name='ANTENNA_115';old=value['instances'][name]['box'];row=(old[1]-3780)//3780
        allowed={(old[0]-20*480,old[1]),(old[0],old[1]+3780)}
        def witness(x,y,*_):return {'test_witness':True} if (x,y) in allowed else None
        with patch.object(P,'access',side_effect=witness):
            moves=P.plan(value,[name],geo(),actual_model(),'B')
        move=moves[0];self.assertEqual((move['x'],move['y']),(old[0],old[1]+3780))
        self.assertEqual(move['orient'],'R0' if geo()['rows'][row+1]['orient']=='N' else 'MX')
        after=copy.deepcopy(value);after['instances'][name].update(box=move['box'],orient=move['orient'])
        P.unchanged(value,after,moves)
        req=P.make_request(PROFILE,PROFILE,'B');self.assertEqual(req['policy_definition'],P.POLICIES['B'])
        P.validate_request(req,'B')
        req['policy_definition']['order'].reverse()
        with self.assertRaises(ValueError):P.validate_request(req,'B')
        self.assertEqual(P.POLICIES['B']['order'][0],'distance')

    def test_measured_A_132_still_fails_with_unchanged_policy(self):
        # Exact subset of actual postcanonical.tsv SHA05c2feb7...; removing
        # every other target/obstruction still leaves all33 A slots blocked.
        value=fixture();value['instances']={}
        for n,m,l,r in [('ANTENNA_132',P.MASTER,1362240,1363680),
            ('engine.core._2450_','sg13cmos5l_dfrbpq_1',1349280,1362240),
            ('fanout2295','sg13cmos5l_buf_1',1363680,1365600),
            ('engine.core._5906_._136_','sg13cmos5l_nor2b_1',1368480,1370880),
            ('engine.core._5905_._200_','sg13cmos5l_mux2_1',1370880,1375680)]:
            value['instances'][n]=dict(master=m,box=(l,207900,r,211680),orient='MY',status='PLACED')
        value['pg']=[('VGND','Metal2',(1366900,3560,1367900,707080),'0'),
            ('VPWR','Metal2',(1362380,7340,1363380,703300),'0')]
        value['special']=[(n,l,b,'STRIPE') for n,l,b,_ in value['pg']]
        with self.assertRaisesRegex(ValueError,'No finite PG-safe legal site for ANTENNA_132 under policy A'):
            P.plan(value,['ANTENNA_132'],geo(),actual_model(),'A')

    def test_measured_110_pin_access_passes_but_whole_site_raster_rejects(self):
        model=actual_model();value=fixture();body=(1112160,3780,1113600,7560)
        self.assertIsNotNone(P.access(body[0],body[1],'R0',model,geo(),value['pg']))
        regions=P.blocked_regions(value['special'],model)
        self.assertTrue(any(P.intersect(body,r) for _,_,r in regions))
        # The native site covering begins at core y3780 even though the real
        # vertical stripe begins at7340: precisely the missed failedB01 case.
        self.assertEqual(next(r for n,l,r in regions if n=='VPWR')[1],3780)
        self.assertEqual(next(r for n,l,r in regions if n=='VPWR')[:1],(1112160,))
        self.assertFalse(any(P.intersect((1110720,3780,1112160,7560),r) for _,_,r in regions))
        with self.assertRaises(ValueError):P.blocked_regions(None,model)

    def test_native_blocked_layer_applicability_and_nonpg_special_shapes(self):
        model=actual_model();vertical=(9600,7340,10600,100000);horizontal=(9600,7340,10600,7540)
        records=[('clock','Metal2',vertical,'STRIPE')]
        self.assertEqual(len(P.blocked_regions(records,model)),1)
        self.assertEqual(P.blocked_regions([('clock','Metal2',vertical,'DRCFILL')],model),[])
        self.assertEqual(P.blocked_regions([('clock','Metal2',horizontal,'STRIPE')],model),[])
        self.assertEqual(P.blocked_regions([('clock','Metal3',vertical,'STRIPE')],model),[])
        self.assertEqual(P.blocked_regions([('clock','Metal4',vertical,'STRIPE')],model),[])
        wide=copy.deepcopy(model);wide['dpl_used_layers']=[1,2,3]
        self.assertEqual(len(P.blocked_regions([('clock','Metal3',vertical,'STRIPE')],wide)),1)

    def test_legacy_HOST_supplement_requires_complete_DEF_special_membership(self):
        value=fixture();value.update(special=None,special_nets=None)
        text='SPECIALNETS 1 ;\n- VPWR + ROUTED Metal2 1000 + SHAPE STRIPE ( 1112880 7340 ) ( 1112880 703300 ) ;\nEND SPECIALNETS\n'
        supplemented=P.legacy_host_specials(value,text)
        self.assertEqual(supplemented['special'],fixture()['special'])
        for bad in (text.replace('1000','900'),text.replace('STRIPE','DRCFILL'),text.replace('SPECIALNETS 1','SPECIALNETS 2')):
            with self.assertRaises(ValueError):P.legacy_host_specials(value,bad)


if __name__=='__main__':unittest.main()
