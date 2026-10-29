"""Portable exact-endface reference/geometry/failure controls; no CAD/build data."""
from decimal import Decimal as D
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import streaming_8x4_model24_r_decoder as W
import streaming_8x4_model24_r_endpoint as ORIGINAL
import streaming_8x4_model24_r_decoder_observe as O
import inspect
import streaming_8x4_model24_r_decoder_readback as R
G=W.G
SHEETS=dict(zip(G.METALS,('.110','.071','.071','.071','.018')))


def native():
    rows=['BLOCK\t1000\t0\t0\t30\t60\t1']
    for m in G.METALS:rows.append('\t'.join(['LAYER',m,str(int(D(G.WIDTHS[m])*1000)),G.DIRECTIONS[m],SHEETS[m]]))
    for m in G.METALS:
        w=str(int(D(G.WIDTHS[m])*2000));rows.append('\t'.join(['NDR','WIDE',m,w,w]))
    for r in G.cases():
        rows.append('\t'.join(['NET',r['name'],r['ndr'] or '-','0','2','0','0','SIGNAL']))
        events=[['PATH',r['layer'],'ROUTED']]
        if r['ndr']:events.append(['RULE',r['ndr'],r['layer'],str(r['width_dbu']),str(r['width_dbu'])])
        events += [['POINT_EXT',*map(str,r['start']),'0'],['POINT_EXT',*map(str,r['end']),'0'],['END_DECODE']]
        for i,event in enumerate(events):rows.append('\t'.join(['DECODE',r['name'],str(i),*event]))
        for i,suffix in enumerate(('A','B')):
            name=r['name']+'_'+suffix;point=r['start'] if i==0 else r['end'];box=r['contact_boxes'][i];glob=[v+point[j%2] for j,v in enumerate(box)]
            rows.append('\t'.join(['BTERM',name,r['name'],'INPUT' if i==0 else 'OUTPUT','SIGNAL','1']))
            rows.append('\t'.join(['BPIN',name,r['layer'],*map(str,glob),'FIRM']))
    return '\n'.join(rows)+'\n'


def spef(mult='1'):
    text='*SPEF "IEEE 1481-1998"\n*R_UNIT 1 OHM\n'
    for name,target in G.resistance(SHEETS).items():
        value=target*(D(mult) if name=='Metal1_W1_L50' else 1)
        text+=f'*D_NET {name} 0\n*CONN\n*P {name}_A I\n*P {name}_B O\n*CAP\n*RES\n1 {name}_A {name}_B {value}\n*END\n'
    return text


def log():return 'MODEL24_R_VERSION_BEGIN\nOpenROAD '+W.COMMIT+'\n\nMODEL24_R_VERSION_END\nMODEL24_R_TERMINAL\n'


class EndpointControls(unittest.TestCase):
    def test_fixed_ninety_cases_geometry_and_ideal_full_width_endfaces(self):
        rows=G.cases();self.assertEqual(len(rows)*len(G.CORNERS),90);self.assertEqual(G.geometry(G.fixture())['explicit_zero_extensions'],60)
        for r in rows:
            self.assertEqual(r['native_shape_length_minus_width_dbu'],1000*r['length_um']-r['width_dbu'])
            for b,p in zip(r['contact_boxes'],(r['start'],r['end'])):
                x0,y0,x1,y1=[v+p[i%2] for i,v in enumerate(b)];self.assertLess(x0,x1);self.assertLess(y0,y1)
                self.assertTrue(0<=x0<x1<G.DIE[2] and 0<=y0<y1<G.DIE[3])
                body=r['body_dbu'];area=max(0,min(x1,body[2])-max(x0,body[0]))*max(0,min(y1,body[3])-max(y0,body[1]));self.assertEqual(area,0)
        self.assertEqual(G.resistance(SHEETS)['Metal1_W1_L50'],D('34.375'))
        self.assertEqual(G.resistance(SHEETS)['Metal1_W2_L50'],D('17.1875'))
    def test_only_global_contact_equivalence_accepts_writer_recentering(self):
        text=G.fixture();old='( -100 -80 ) ( 0 80 )\n + FIXED ( 10000 10000 ) N'
        shifted=text.replace(old,'( -50 -80 ) ( 50 80 )\n + FIXED ( 9950 10000 ) N',1)
        self.assertNotEqual(text,shifted);self.assertEqual(G.geometry(shifted),G.geometry(text))
        for bad in (shifted.replace('( 9950 10000 )','( 9951 10000 )',1),text.replace('( -100 -80 ) ( 0 80 )','( -100 -79 ) ( 0 80 )',1),text.replace('( 10000 10000 ) N','( 10000 10000 ) S',1)):
            with self.assertRaises(ValueError):G.geometry(bad)
    def test_actual_extent_width_route_and_full_membership_cannot_relax(self):
        text=G.fixture()
        for bad in (text.replace('( 10000 10000 0 )','( 10000 10000 )',1),text.replace('( 10000 10000 0 )','( 10000 10000 80 )',1),text.replace('+ ROUTED Metal1','+ ROUTED Metal2',1),text.replace('MICRONS 1000','MICRONS 2000'),text.replace('WIDTH 320 SPACING 320','WIDTH 321 SPACING 320'),text.replace('NETS 30','NETS 29'),text.replace('( 60000 10000 0 ) ;','( 60000 10000 0 ) Via1_XX ;',1)):
            with self.assertRaises(ValueError):G.geometry(bad)
    def test_independent_native_inventory_reconciles_global_contacts_and_shape_extent(self):
        self.assertTrue(W.native_geometry(native(),SHEETS)['all_global_full_endface_contacts_checked'])
        for bad in (native().replace('POINT_EXT\t10000\t10000\t0','POINT_EXT\t10001\t10000\t0',1),native().replace('BPIN\tMetal1_W1_L50_A\tMetal1\t9900\t9920','BPIN\tMetal1_W1_L50_A\tMetal1\t9900\t9921'),native().replace('FIRM','PLACED',1),native().replace('NDR\tWIDE\tMetal1\t320','NDR\tWIDE\tMetal1\t321'),native()+native().splitlines()[0]+'\n'):
            with self.assertRaises(ValueError):W.native_geometry(bad,SHEETS)
    def test_native_raw_reference_pass_and_numeric_failure_are_distinct_measurements(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);(p/'native.log').write_text(log())
            for n in ('before.def','after.def'):(p/n).write_text(G.fixture())
            for n in ('before.tsv','after.tsv'):(p/n).write_text(native())
            (p/'result.spef').write_text(spef());good=W.parse_leaf(p,SHEETS);self.assertTrue(good['ideal_endface_controls_passed']);self.assertEqual(len(good['absolute_audits']),30)
            (p/'result.spef').write_text(spef('1.002'));bad=W.parse_leaf(p,SHEETS);self.assertFalse(bad['ideal_endface_controls_passed']);self.assertEqual(sum(not r['passed'] for r in bad['absolute_audits']),1)
            (p/'after.tsv').write_text(native().replace('POINT_EXT\t10000\t10000\t0','POINT_EXT\t10001\t10000\t0',1))
            with self.assertRaises(ValueError):W.parse_leaf(p,SHEETS)
    def test_printed_version_empty_return_and_conflicting_wrong_absent_revision(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)
            for n in ('before.def','after.def'):(p/n).write_text(G.fixture())
            for n in ('before.tsv','after.tsv'):(p/n).write_text(native())
            (p/'result.spef').write_text(spef());(p/'native.log').write_text(log());self.assertTrue(W.parse_leaf(p,SHEETS)['ideal_endface_controls_passed'])
            for raw in (log().replace(W.COMMIT,''),log().replace(W.COMMIT,'a'*40),log().replace(W.COMMIT,W.COMMIT+'0'),log().replace(W.COMMIT,W.COMMIT+'\n'+'a'*40),log()+'WARNING extra\n',log()+'MODEL24_R_TERMINAL\n'):
                (p/'native.log').write_text(raw)
                with self.assertRaises(ValueError):W.parse_leaf(p,SHEETS)
    def test_reference_uses_declared_actual_width_and_no_fitted_endpoint(self):
        targets=G.resistance(SHEETS)
        for r in G.cases():self.assertEqual(targets[r['name']],D(SHEETS[r['layer']])*r['length_um']*1000/r['width_dbu'])
        self.assertEqual(targets['Metal1_W1_L100']/targets['Metal1_W1_L50'],2)
        self.assertEqual(targets['Metal1_W1_L50']/targets['Metal1_W2_L50'],2)
    def test_complete_packet_budget_and_failed_numeric_never_promote(self):
        rows=[dict(passed=True,measurement_completed=True)]*3
        for duration in (119.9,120.1):
            report=dict(actual_work_seconds=duration,work_budget_passed=duration<=120,measurement_packet_completed=True,passed=duration<=120)
            self.assertEqual(R.packet_state(report,rows),(True,duration<=120))
            with self.assertRaises(ValueError):R.packet_state(report,rows[:-1])
        report=dict(actual_work_seconds=1,work_budget_passed=True,measurement_packet_completed=True,passed=False)
        self.assertEqual(R.packet_state(report,[dict(passed=False,measurement_completed=True)]+rows[:2]),(True,False))
        with self.assertRaises(ValueError):R.packet_state(dict(report,passed=True),[dict(passed=False,measurement_completed=True)]+rows[:2])
    def test_whole_r_graph_membership_and_units_are_strict(self):
        good=G.C.parse_spef(spef(),set(G.resistance(SHEETS)));self.assertEqual(len(good),30)
        for bad in (spef().replace('*R_UNIT 1 OHM','*R_UNIT 1 PF'),spef().replace('Metal1_W1_L50_B 34.375','Metal1_W1_L50_A 34.375',1),spef().replace('*D_NET Metal1_W1_L50','*D_NET extra',1)):
            with self.assertRaises(ValueError):G.C.parse_spef(bad,set(G.resistance(SHEETS)))
    def test_fixed_native_calls_budget_and_no_general_qualification_claim(self):
        p=W.policy();self.assertEqual((p['calls'],p['leaf_seconds'],p['work_seconds'],p['outer_seconds']),(3,30,120,180));self.assertTrue(p['no_fitted_subtraction']);self.assertEqual(p['original_R26_absolute_failures'],123)
        for key in ('model_qualified','qualified_timing','arbitrary_route_R_qualified','contact_spreading_and_via_physics_qualified','capacitance_qualified'):self.assertFalse(p[key])
        self.assertIn('extract_parasitics -lef_res ',W.tcl());self.assertNotIn('[$wire getLength]',W.tcl());self.assertIn('[$decoder getPoint_ext]',W.tcl());self.assertNotIn('getShape',W.tcl())
    def test_full_prepared_source_input_membership_is_mandatory_in_root_resource_seals(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);plan=dict(files={'tech.lef':dict(sha256='a'*64),'endpoint-source/dbShape.h':dict(sha256='b'*64)})
            seals={str((p/n).resolve()):r['sha256'] for n,r in plan['files'].items()};self.assertEqual(R.checked_input_seals(p,plan,dict(input_sha256=seals)),2)
            for bad in ({},dict(seals,**{str((p/'tech.lef').resolve()):'c'*64})):
                with self.assertRaises(ValueError):R.checked_input_seals(p,plan,dict(input_sha256=bad))
    def test_actual_proposal_uses_reviewed_image_interpreter_and_exact_caps(self):
        with tempfile.TemporaryDirectory() as d,patch.object(W,'verify',return_value=dict(producer_sha256={})):
            p=Path(d);row=W.proposal(p,'a'*64,p);a=row['argv']
            self.assertEqual(a[a.index('--entrypoint')+1:a.index('--entrypoint')+3],[W.S.N.C.PYTHON,W.S.N.C.IMAGE])
            self.assertEqual(a[a.index('--memory')+1],'2g');self.assertEqual(a[a.index('--memory-swap')+1],'2g');self.assertEqual(a[a.index('--cpus')+1],'1')
            self.assertEqual(row['timeout_seconds'],180);self.assertFalse(row['native_executed']);self.assertEqual(a[-1],'/model24-output-parent/'+W.OUTPUT)
    def test_actual_frozen_kernel_keys_and_owned_writer_reader_normalization_contract(self):
        # The frozen cap consumer returns dotted kernel filenames. This new R
        # writer intentionally normalizes its own schema before storing it;
        # do not infer an underscore schema for any older producer.
        kernel={'cpu.max':'100000 100000','memory.max':'2147483648','memory.swap.max':'0','pids.max':'128'}
        with patch.object(Path,'read_text',lambda p:kernel[p.name]):
            frozen=W.S.N.C.cgroups();owned=W.cgroups()
        self.assertEqual(frozen,kernel)
        self.assertEqual(owned,{'cpu_max':'100000 100000','memory_max':'2147483648','memory_swap_max':'0','pids_max':'128'})
        with tempfile.TemporaryDirectory() as d,patch.object(W.S.N,'resource_observation',return_value=True):
            p=Path(d);inputs=p/'inputs';owner=p/'leaf';inputs.mkdir();owner.mkdir()
            for n in ('tech.lef','fixture.def','run.tcl','rules.txt'):
                (inputs/('ITF_TYP-local.lef' if n=='tech.lef' else n)).write_text('input')
                (owner/n).write_text('input')
            for n in ('before.def','after.def'):(owner/n).write_text(G.fixture())
            for n in ('before.tsv','after.tsv'):(owner/n).write_text(native())
            (owner/'result.spef').write_text(spef());(owner/'native.log').write_text(log())
            row=dict(schema='pinwheel.model24-r-decoder-leaf.v1',plan_sha256='a'*64,corner='ITF_TYP',argv=['/native/bin/openroad','-no_init','-exit','run.tcl'],
                openroad_sha256=W.OPENROAD_SHA,native_executed=True,process_tree_reaped=True,inputs_sources_unchanged=True,copied_inputs_unchanged=True,openroad_unchanged=True,
                model_qualified=False,qualified_timing=False,environment=dict(PATH='/native/bin',HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE'),
                cgroups=owned,output_inventory=W.owned_inventory(owner),native_log_sha256=W.E.sha(owner/'native.log'),actual_work_seconds=1,work_budget_passed=True,
                exit_code=0,timed_out=False,memory_guard_triggered=False,output_guard_triggered=False,analysis=W.parse_leaf(owner,SHEETS),measurement_completed=True,resource_feasible=True,passed=True)
            receipt=owner/'report.json';receipt.write_text(__import__('json').dumps(row))
            self.assertTrue(R.read_leaf(inputs,'a'*64,dict(corner_sheet_R={'ITF_TYP':SHEETS}),'ITF_TYP',owner)['passed'])
            row['cgroups']=frozen;receipt.write_text(__import__('json').dumps(row))
            with self.assertRaises((ValueError,KeyError)):R.read_leaf(inputs,'a'*64,dict(corner_sheet_R={'ITF_TYP':SHEETS}),'ITF_TYP',owner)


class DecoderRepairControls(unittest.TestCase):
    def test_complete_decoder_stream_rejects_extra_missing_wrong_order_or_pointer(self):
        good=native();row='DECODE\tMetal1_W1_L50\t1\tPOINT_EXT\t10000\t10000\t0'
        for bad in (good.replace(row,row.replace('POINT_EXT','POINT')),good.replace(row,row.replace('\t0','\t80')),
            good.replace(row,''),good.replace(row,row+'\n'+row),good.replace(row,row.replace('\t1\t','\t2\t')),
            good.replace(row,row.replace('10000\t10000','_deadbeef_p_uint64_t\t10000')),
            good.replace('PATH\tMetal1\tROUTED','PATH\tMetal2\tROUTED',1),
            good.replace('RULE\tWIDE\tMetal1\t320\t320','RULE\tWIDE\tMetal1\t321\t320',1),
            good.replace('END_DECODE','TECH_VIA',1),good+'DECODE\tforeign\t0\tEND_DECODE\n'):
            with self.assertRaises((ValueError,TypeError)):W.native_geometry(bad,SHEETS)
    def test_shapes_are_derived_from_actual_points_width_not_labelled_as_api_length(self):
        r=W.native_geometry(native(),SHEETS);self.assertFalse(r['dbWire_getLength_numeric_measurement_claimed'])
        self.assertEqual(len(r['source_derived_shape_witnesses']),30)
        for actual,declared in zip(r['source_derived_shape_witnesses'],G.cases()):
            self.assertEqual(actual['source_derived_body_bbox_dbu'],declared['body_dbu'])
            self.assertEqual(actual['source_derived_long_dimension_minus_width_dbu'],declared['native_shape_length_minus_width_dbu'])
            self.assertTrue(actual['derived_quantity_not_observed_getLength'])
    def test_exact_observer_only_tcl_delta_no_consumer_math_resource_change(self):
        self.assertEqual(W.tcl().replace(O.DECODE,O.OLD_LINE),ORIGINAL.tcl())
        self.assertEqual(W.G,ORIGINAL.G)
        expected=ORIGINAL.policy();new=W.policy()
        for key,value in expected.items():
            if key not in ('schema','geometry_witness'):self.assertEqual(new[key],value)
        self.assertTrue(new['numerical_tuning_stop_preserved']);self.assertTrue(new['observer_API_correctness_repair_only'])
    def test_native_guard_and_math_bodies_reused_with_schema_only_normalization(self):
        for name in ('source_intake','corner_data','files','historical','owned_inventory','cgroups','copied','leaf','run','proposal','parse_leaf'):
            new=inspect.getsource(getattr(W,name)).replace('pinwheel.model24-r-decoder-','pinwheel.model24-r-endpoint-')
            self.assertEqual(new,inspect.getsource(getattr(ORIGINAL,name)),name)
    def test_old_failed_authority_identity_cannot_be_relabelled(self):
        self.assertEqual(W.PRIOR_FAILURE,'08cd85ea8bd440f093bf200c37bfcd2d3779e821499854775790247421b196a2')
        self.assertEqual(W.PRIOR_PLAN,'fc079452a9ca2abbea735a7e6fcc2e4fa654992c2fb16313689e1bb813994288')
        self.assertIn('prior_API_failure',inspect.getsource(R.readback))
        self.assertIn('ORIGINAL_READER.readback',inspect.getsource(R.preserved_old_failure))

if __name__=='__main__':unittest.main()
