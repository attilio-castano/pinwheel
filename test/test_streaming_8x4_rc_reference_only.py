"""HOST controls only: no operator/solver/container or subprocess is invoked."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from historical_evidence import historical_evidence
from streaming_8x4_reference_fixtures import reference_plan, reference_rows as fake_rows, cgroup_snapshot as cg
ROOT = Path(__file__).resolve().parents[1]
def module(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'scripts'/(name+'.py'))
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value
W=module('streaming_8x4_rc_reference_only');R=module('streaming_8x4_rc_reference_only_readback')
OLD=reference_plan()

class ReferenceOnlyControls(unittest.TestCase):
    def test_exact_eight_cases_32_grids_and_unchanged_operator(self):
        self.assertEqual(len(W.jobs(OLD)),32);self.assertEqual(len({tuple(r.values()) for r in W.jobs(OLD)}),32)
        keys=('case','step_um','extent_um','nodes','nx','ny')
        actual=W.A.grid_inventory(OLD['cases'])
        self.assertEqual([{k:g[k] for k in keys} for g in actual],OLD['grid_inventory'])
        self.assertTrue(all(g['exact_material_and_conductor_anchors_present'] and g['minimum_dx_um']>0 and g['minimum_dy_um']>0 for g in actual))
        self.assertEqual(sum(g['nodes'] for g in actual),893444)
        self.assertEqual(W.A.operator_derivation(),OLD['FVM_derivation'])
        self.assertLess(max(g['nodes'] for g in OLD['grid_inventory']),65000)
        self.assertFalse(W.policy()['BEM_prerequisite_required']);self.assertFalse(W.policy()['finite_BEM_passed'])

    @historical_evidence
    def test_exact_historical_plan_identity(self):
        path=ROOT/'build/campaigns/8x4-20261022-01/rc-all-layers-preparation-02/plan.json'
        self.assertEqual(W.E.sha(path),W.BASELINE)
        self.assertEqual(json.loads(path.read_text())['cases'],OLD['cases'])

    def test_transitive_sources_cover_reference_and_resource_consumers(self):
        sources=W.sources()
        for name in W.NEW+('streaming_8x4_rc_all_layers_reference.py','streaming_8x4_rc_reference.py',
            'streaming_8x4_acceptance_resources.py','streaming_tt_resources.py'):
            self.assertEqual(sources[name],W.E.sha(ROOT/'scripts'/name))

    def test_strict_actual_geometry_nodes_excitation_and_residual(self):
        for leaf in fake_rows(OLD):W.validate_row(OLD,leaf['job'],leaf['kernel_row'])
        leaf=fake_rows(OLD)[-1]
        for key,value in [('nodes',1),('names',['wrong']),('extent_um',16),('epsilon_layers',[]),('reciprocity_relative_error',float('nan'))]:
            row=copy.deepcopy(leaf['kernel_row']);row[key]=value
            with self.assertRaises((ValueError,KeyError,IndexError)):W.validate_row(OLD,leaf['job'],row)
        for mutation in ('residual','excitation','energy'):
            row=copy.deepcopy(leaf['kernel_row'])
            if mutation=='residual':row['excitations'][0]['true_residual_relative']=1e-5
            elif mutation=='energy':row['excitations'][0]['energy_flux_relative_error']=1e-5
            else:row['excitations'].reverse()
            with self.assertRaises(ValueError):W.validate_row(OLD,leaf['job'],row)

    def test_complete_reference_math_and_no_prefix_duplicate_or_failed_promotion(self):
        leaves=fake_rows(OLD);result=R.analysis(OLD,leaves)
        self.assertTrue(result['passed']);self.assertEqual(len(result['cases']),8)
        for wrong in (leaves[:-1],leaves+[leaves[0]],list(reversed(leaves))):
            with self.assertRaises(ValueError):R.analysis(OLD,wrong)
        wrong=copy.deepcopy(leaves);wrong[-1]['numeric_passed']=False
        with self.assertRaises(ValueError):R.analysis(OLD,wrong)
        wrong=copy.deepcopy(leaves);wrong[-1]['kernel_row']['ground_C_F_per_m'][0]*=2
        self.assertFalse(R.analysis(OLD,wrong)['passed'])
        wrong=copy.deepcopy(leaves);wrong[-2]['kernel_row']['matrix_F_per_m'][0][1]*=2
        self.assertFalse(R.analysis(OLD,wrong)['passed'])

    def test_actual_cgroup_missing_max_oom_peak_and_resource_failure(self):
        before=cg();after=cg();base={'cgroup_before':before,'cgroup_after':after,'counter_deltas':W.deltas(before,after),
            'maximum_polled_memory_current':1500,'process_tree_reaped':True,'timed_out':False,'memory_guard_triggered':False,'exit_code':0}
        self.assertTrue(W.resource_feasible(base))
        for key,value in [('timed_out',True),('process_tree_reaped',False),('memory_guard_triggered',True),('exit_code',-9)]:
            self.assertFalse(W.resource_feasible(dict(base,**{key:value})))
        for counter in ('max','oom','oom_kill'):
            wrong=copy.deepcopy(base);wrong['cgroup_after']['memory_events'][counter]=1
            wrong['counter_deltas']=W.deltas(wrong['cgroup_before'],wrong['cgroup_after']);self.assertFalse(W.resource_feasible(wrong))
        wrong=copy.deepcopy(before);del wrong['memory_events']['max']
        with self.assertRaises(ValueError):W.validate_snapshot(wrong)
        with self.assertRaises(ValueError):W.resource_feasible(dict(base,maximum_polled_memory_current=2001))
        wrong=copy.deepcopy(before);wrong['memory_max']=6442450944
        with self.assertRaises(ValueError):W.validate_snapshot(wrong)

    def test_fixed_native_command_does_not_mount_solver_or_modify_input(self):
        with tempfile.TemporaryDirectory() as temporary:
            owner=Path(temporary).resolve()
            with patch.object(W,'verify',return_value={'producer_sha256':{}}):
                command=W.proposal(owner,'pin',owner)['argv']
            self.assertIn('2g',command);self.assertIn('/tmp:rw,nosuid,noexec,size=134217728',command)
            self.assertEqual(command.count('--mount'),3);self.assertNotIn('/solver/runtime',' '.join(command))
            self.assertIn(W.W.C.D.IMAGE,command)
        command=W.dispatch_argv(Path('/rc-inputs'),'pin',0,Path('/out'))
        self.assertEqual(command[0],W.PYTHON);self.assertEqual(command[3],'/rc-source/'+W.NEW[0])

    def test_closed_final_numeric_failure_completes_measurements_but_not_pass(self):
        for resource in (True,False):
            with tempfile.TemporaryDirectory() as temporary:
                output=Path(temporary)/'out'
                def dispatch(inputs,digest,index,owner):
                    owner.mkdir();(owner/'dispatch.json').write_text('{}')
                    return {'numeric_passed':index!=31,'resource_feasible':resource if index==31 else True}
                with patch.object(W,'verify',return_value=OLD),patch.object(W,'snapshot',return_value=cg()),patch.object(W,'dispatch',side_effect=dispatch):
                    row=W.run(Path(temporary),'pin',output)
                self.assertEqual(len(row['jobs']),32);self.assertIs(row['measurement_packet_completed'],resource)
                self.assertFalse(row['all_numeric_leaves_passed']);self.assertFalse(row['passed']);self.assertFalse(row['reference_stability_passed'])

    def test_failed_reference_authority_cannot_confer_downstream_pass(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'input';path.write_text('{}');bound=W.H.bound(path)
            row={'new_reference_only_plan':bound,'execution_report':bound,'command_proposal':bound,
                'resource_cleanup_join':{'resource_report':bound},'reference_only_complete_passed':False}
            target=Path(temporary)/'authority.json';target.write_text(json.dumps(row))
            with patch.object(R,'readback',return_value=row):
                with self.assertRaisesRegex(ValueError,'cannot confer authority'):R.closed_authority(target)

    def test_exact_empty_log_warning_gate_preserves_closed_numeric_failure(self):
        for text in ('','RuntimeWarning: test warning\n'):
            with tempfile.TemporaryDirectory() as temporary:
                owner=Path(temporary)/'job-000';owner.mkdir()
                (owner/'native.log').write_text(text);(owner/'leaf.json').write_text('{}')
                before=cg();after=cg();empty=not text
                row={'schema':'pinwheel.streaming-8x4-rc-reference-only-dispatch.v1','index':0,
                    'plan_sha256':'pin','timeout_seconds':120,
                    'argv':W.dispatch_argv(Path('/rc-inputs'),'pin',0,Path('/rc-output-parent')/W.OUTPUT/'job-000/leaf.json'),
                    'log_sha256':W.E.sha(owner/'native.log'),'native_log_empty':empty,'wall_seconds':1.,
                    'cgroup_before':before,'cgroup_after':after,'counter_deltas':W.deltas(before,after),
                    'maximum_polled_memory_current':1500,'process_tree_reaped':True,'timed_out':False,
                    'memory_guard_triggered':False,'exit_code':0,'resource_feasible':True,
                    'leaf_sha256':W.E.sha(owner/'leaf.json'),'numeric_passed':empty}
                (owner/'dispatch.json').write_text(json.dumps(row))
                leaf={'numeric_passed':True,'kernel_row':fake_rows(OLD)[0]['kernel_row']}
                with patch.object(R,'numeric_leaf',return_value=leaf):
                    observed=R.dispatch(OLD,'pin',0,owner)
                    self.assertIs(observed['numeric_passed'],empty);self.assertTrue(observed['resource_feasible'])
                    if text:
                        row['numeric_passed']=True;(owner/'dispatch.json').write_text(json.dumps(row))
                        with self.assertRaises(ValueError):R.dispatch(OLD,'pin',0,owner)

    @historical_evidence
    def test_actual_current_guard_lease_receipt_and_foreign_supervisor_rejection(self):
        b=ROOT/'build/campaigns/8x4-20261022-01'
        resource=ROOT/'build/streaming-tt-resources/8x4-rc-incore-two-leaf-01/report.json'
        self.assertEqual(W.E.sha(resource),'80ed9b0d475abd0f1420701e671bcc130bbe4dc2a2d8b2090c3729737109e2fb')
        proposal_path=b/'rc-incore-command-proposal-02.json';proposal=json.loads(proposal_path.read_text())
        plan=json.loads((b/'rc-incore-preparation-02/plan.json').read_text())
        report=json.loads((b/'rc-native-outputs/rc-incore-two-leaf-01/report.json').read_text())
        self.assertTrue(R.resource_join(resource,proposal_path,proposal,plan,report)['cleanup_confirmed'])
        with tempfile.TemporaryDirectory() as temporary:
            wrong=json.loads(resource.read_text());wrong['supervisor_sha256']='0'*64
            path=Path(temporary)/'resource.json';path.write_text(json.dumps(wrong))
            with self.assertRaises(ValueError):R.resource_join(path,proposal_path,proposal,plan,report)

    def test_exact_shared_cleanup_sentinel_required(self):
        with tempfile.TemporaryDirectory() as temporary:
            path=Path(temporary)/'resource.json'
            row={'campaign_boundary':{'campaign_root':str(W.ROOT),'shared_lease':{'cleanup_sentinel':str(W.ROOT/'build/streaming-tt-resources/cleanup-unconfirmed.json')}}}
            for wrong in (False,True):
                if wrong:row['campaign_boundary']['shared_lease']['cleanup_sentinel']='other'
                path.write_text(json.dumps(row))
                with patch.object(W.H,'resource_join',return_value={'cleanup_confirmed':True}):
                    if wrong:
                        with self.assertRaises(ValueError):R.resource_join(path,None,None,None,None)
                    else:self.assertTrue(R.resource_join(path,None,None,None,None)['cleanup_confirmed'])


if __name__=='__main__':unittest.main()
