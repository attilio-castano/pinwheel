"""Complete-universe HOST controls; no field solver or subprocess is run."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / (name + '.py'))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value); return value
W = module('streaming_8x4_rc_full_policy'); X = module('streaming_8x4_rc_full_execute'); R = module('streaming_8x4_rc_full_readback')
GOOD = (ROOT / 'test/fixtures/streaming-8x4-rc-wire-coarse-20261022.log').read_text()
BAD = (ROOT / 'test/fixtures/streaming-8x4-rc-layered-coarse-physics-failure-20261022.log').read_text()


class FullPolicyControls(unittest.TestCase):
    def uniform(self):
        cases = [{'name': 'historical_U_new_manual'}]
        for width in ('0p16', '0p32'):
            for length in ('10', '20', '30'): cases.append({'name': 'wire_w'+width+'_L'+length+'_M20'})
        for width in ('0p16', '0p32'):
            for length in ('20', '30'): cases.append({'name': 'wire_w'+width+'_L'+length+'_M30'})
        plan = {'profile': W.PROFILES[1], 'policy': W.policy(W.PROFILES[1]), 'cases': cases,
                'reference_join': {'analysis': {w: {'reference_F_per_m': '1e-10'} for w in ('0.16', '0.32')}},
                'original_protocol': W.P.frozen_protocol()}
        leaves = []
        for job in W.jobs(plan):
            length = W.P.number('10' if job['case'].startswith('historical') else job['case'].split('_L')[1].split('_')[0])
            cap = length * W.P.number('1e-16') + W.P.number('1e-16')
            matrix = [[str(cap*10),str(-cap)],[str(-cap),str(cap)]]
            leaves.append(dict(job, passed=True, numeric={'names':['g1_GND_SUB','g2_SIGNAL'], 'matrix':matrix, 'matrix_F':matrix,'mesh':job['mesh']}))
        return plan, leaves

    def test_exact_new_universes_resources_and_supported_preconditioners(self):
        for profile,cases,count,work in ((W.PROFILES[0],30,150,3600),(W.PROFILES[1],11,55,1800)):
            p=W.policy(profile);self.assertEqual(p['maximum_calls'],count);self.assertEqual(p['work_seconds'],work)
            self.assertEqual(p['outer_seconds'],work+60);self.assertEqual(p['seconds_per_leaf'],120)
            plan={'policy':p,'cases':[{'name':str(i)} for i in range(cases)]};jobs=W.jobs(plan)
            self.assertEqual(len(jobs),count);self.assertEqual(len({(x['case'],x['mesh']) for x in jobs}),count)
            for m in p['mesh_ladder']:
                argv=W.solver_argv(p,m);self.assertIn('-d0.25',argv);self.assertIn('-t0.0005',argv)
                self.assertEqual(argv[-2:]==['-pn','-ps128'],profile==W.PROFILES[1])
        with self.assertRaises(ValueError):W.policy('old-native06')

    def test_source_closure_covers_all_imports_and_old_geometry_reference_producers(self):
        closure=W.source_closure()
        for n in W.NEW+('streaming_8x4_rc_layered_geometry.py','streaming_8x4_rc_reference_run.py','streaming_8x4_acceptance_resources.py'):
            self.assertEqual(closure[n],W.E.sha(ROOT/'scripts'/n))

    def test_original_U_and_finite_wire_units_remain_distinct(self):
        self.assertEqual(W.case_unit(W.PROFILES[1],'historical_U_new_manual'),'0.00000095367431640625')
        self.assertEqual(W.case_unit(W.PROFILES[1],'wire_w0p16_L20_M30'),'0.000001')
        self.assertEqual(W.case_unit(W.PROFILES[0],'TYP-w.16-self-L10-E20'),'0.00000095367431640625')

    def test_captured_log_grammar_binds_new_policy_and_fatal_physics(self):
        for profile in W.PROFILES:
            p=W.policy(profile);plan={'policy':p};case={'matrix_names':['g1_GND_SUB','g2_SIGNAL'],'coordinate_unit_m':W.case_unit(profile,'wire_w0p16_L10_M20')}
            raw=GOOD.replace('(-d): 1','(-d): 0.25')
            if profile==W.PROFILES[1]:raw=raw.replace('Precond Type(s) (-p): Jacobi ','Precond Type(s) (-p): Two-levels, two-levels preconditioner dimension (-ps): 128 ')
            parsed=X.parse(raw,plan,case,p['mesh_ladder'][0]);self.assertFalse(parsed['model_qualified'])
            for wrong in (raw+'\nprogress Warning: bad\n',raw.replace('(-d): 0.25','(-d): 1'),raw+'\nPrecond Type(s) (-p): Jacobi\n'):
                with self.assertRaises(ValueError):X.parse(wrong,plan,case,p['mesh_ladder'][0])
        with self.assertRaises(ValueError):X.parse(BAD,{'policy':W.policy(W.PROFILES[0])},{'matrix_names':['g1_GND_SUB','g2_W1','g3_W2'],'coordinate_unit_m':'0.00000095367431640625'},'0.000383703')

    def test_complete_uniform_math_pass_and_no_prefix_duplicate_or_failed_leaf(self):
        plan,leaves=self.uniform();self.assertTrue(R.mathematical_analysis(plan,leaves)['passed'])
        for rows in (leaves[:-1],list(reversed(leaves)),leaves+[leaves[0]]):
            with self.assertRaises(ValueError):R.mathematical_analysis(plan,rows)
        failed=copy.deepcopy(leaves);failed[-1]['passed']=False
        with self.assertRaises(ValueError):R.mathematical_analysis(plan,failed)

    def test_original_two_percent_mesh_gate_and_reference_bound_unchanged(self):
        plan,leaves=self.uniform();jump=copy.deepcopy(leaves)
        jump[-1]['numeric']['matrix']=[[str(W.P.number(x)*2) for x in r] for r in jump[-1]['numeric']['matrix']]
        result=R.mathematical_analysis(plan,jump);self.assertFalse(result['passed']);self.assertIn('mesh gate',result['error'])
        wrong=copy.deepcopy(plan);wrong['reference_join']['analysis']['0.16']['reference_F_per_m']='1e-8'
        self.assertFalse(R.mathematical_analysis(wrong,leaves)['passed'])

    def test_full_resource_join_rejects_scope_cleanup_or_source_substitution(self):
        with tempfile.TemporaryDirectory() as temporary:
            owner=Path(temporary).resolve();proposal_path=owner/'proposal.json';proposal_path.write_text('{}');plan_path=owner/'plan.json';plan_path.write_text('{}')
            producer=Path(W.__file__).resolve();plan={'policy':W.policy(W.PROFILES[1]),'producer_sha256':{producer.name:W.E.sha(producer)}}
            proposal={'argv':['exact'],'plan_path':str(plan_path),'plan_sha256':W.E.sha(plan_path)};report={'passed':True}
            supervisor=W.E.sha(ROOT/'scripts/streaming_tt_resources.py')
            resource={'schema':'pinwheel.streaming-tt-resource-job.v1','exit_code':0,'status':'completed','argv':['exact'],
                'timeout_seconds':1860,'cleanup_confirmed':True,'inputs_unchanged':True,'containers_remaining':[],
                'owned_processes_remaining':[],'cleanup_errors':[],'supervisor_sha256':supervisor,
                'campaign_boundary':{'schema':'pinwheel.streaming-8x4-resource-boundary.v1','campaign_root':str(W.ROOT),
                    'campaign_kind':'rc_experiment','shared_lease':{'heavy_lock':str(W.ROOT/'build/streaming-tt-resources/heavy.lock')},
                    'wrapper_sha256':W.E.sha(ROOT/'scripts/streaming_8x4_acceptance_resources.py'),'inherited_supervisor_sha256':supervisor},
                'input_sha256':{str(proposal_path):W.E.sha(proposal_path),str(plan_path):W.E.sha(plan_path),str(W.ROOT/'scripts'/producer.name):W.E.sha(producer)}}
            path=owner/'resource.json'
            for changed in ({},{'cleanup_confirmed':False},{'timeout_seconds':1861},{'argv':['other']},{'input_sha256':{}},{'containers_remaining':['live']}):
                path.write_text(json.dumps(dict(resource,**changed)))
                if changed:
                    with self.assertRaises((ValueError,KeyError)):R.resource_join(path,proposal_path,proposal,plan,report)
                else:self.assertTrue(R.resource_join(path,proposal_path,proposal,plan,report)['cleanup_confirmed'])

    def test_failed_full_result_cannot_confer_downstream_authority(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'input.json';path.write_text('{}');pin=R.bound(path)
            row={'new_policy_plan':pin,'native_report':pin,'command_proposal':pin,'runtime_path':temporary,
                 'resource_cleanup_join':{'resource_report':pin},'limited_pilot_passed':False}
            result=Path(temporary)/'authority.json';result.write_text(json.dumps(row))
            with patch.object(R,'readback',return_value=row):
                with self.assertRaisesRegex(ValueError,'cannot confer authority'):R.closed_authority(result)

    def test_final_numeric_failure_closes_measurement_but_failed_reaping_does_not(self):
        plan,_=self.uniform();plan['runtime']={}
        for reaped in (True,False):
            with tempfile.TemporaryDirectory() as temporary:
                owner=Path(temporary)/('rc-full-'+plan['profile']+'-01');calls=[]
                def leaf(inputs,digest,prepared,case,mesh,runtime,output):
                    calls.append((case['name'],mesh));last=len(calls)==55;output.mkdir()
                    row={'exit_code':0,'solver_executed':True,'process_tree_reaped':(reaped if last else True),
                         'copied_inputs_unchanged':True,'source_runtime_unchanged':True,'producer_plan_unchanged':True,
                         'passed':not last}
                    W.write(output/'report.json',row);return row
                with patch.object(X.W,'verify',return_value=plan),patch.object(X.E,'tree',return_value={}),\
                     patch.object(X.E,'verify_cgroups',return_value={}),patch.object(X,'leaf',side_effect=leaf):
                    result=X.run(Path(temporary),'seal',Path('/solver/runtime'),owner)
                self.assertEqual(len(result['jobs']),55);self.assertIs(result['measurement_packet_completed'],reaped)
                self.assertFalse(result['all_numeric_leaves_passed']);self.assertFalse(result['passed'])
                self.assertFalse(result['limited_pilot_passed'])


if __name__=='__main__':unittest.main()
