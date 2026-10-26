"""HOST-only exact historical27/fresh5 membership and resource-clock controls."""
import copy
import inspect
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path[:0]=[str(ROOT/'scripts'),str(ROOT/'test')]
import streaming_8x4_rc_reference_completion as W
import streaming_8x4_rc_reference_completion_readback as R
import test_streaming_8x4_rc_reference_expanded as T
B=ROOT/'build/campaigns/8x4-20261022-01'


class CompletionControls(unittest.TestCase):
    def test_exact_global_suffix_is_every_unfinished_original_case(self):
        parent=W.X.verify(B/'rc-reference-expanded-preparation-02',W.PARENT)
        self.assertEqual(W.INDICES,[27,28,29,30,31])
        calls=[W.jobs(parent)[i] for i in W.INDICES]
        self.assertEqual(calls[0],dict(case='TYP-Metal3-Metal4-centered',step='.02',extent='64'))
        self.assertEqual({c['case'] for c in calls[1:]},{'TYP-Metal4-TopMetal1-centered'})
        for key in ('maximum_nodes','memory_bytes','true_residual_relative_tolerance','energy_flux_relative_tolerance','maximum_mesh_change','maximum_domain_change','maximum_cg_iterations'):
            self.assertEqual(W.policy()[key],W.X.policy()[key])
        self.assertEqual((W.policy()['seconds_per_leaf'],W.policy()['work_seconds'],W.policy()['outer_seconds']),(180,1050,1110))

    def test_actual_original27_and_failed027_reopen_without_promotion(self):
        got=W.reopen_parent(B/'rc-reference-expanded-independent-readback-01.json')
        self.assertFalse(got['expanded_reference_complete_passed']);self.assertEqual(len(got['leaves']),28)
        self.assertTrue(all(r['numeric_passed'] and r['resource_feasible'] for r in got['leaves'][:27]))
        self.assertTrue(got['leaves'][27]['actual_dispatch']['timed_out']);self.assertIsNone(got['leaves'][27]['kernel_row'])
        bad=copy.deepcopy(got);bad['leaves'][27]['numeric_passed']=True
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'authority.json';p.write_text(json.dumps(bad))
            with patch.object(W,'FAILED',W.E.sha(p)):
                with self.assertRaises(ValueError):W.parent_failure(p)

    def test_same_kernel_object_and_identical_one_body_except_type_index(self):
        self.assertIs(W.F,W.X.F);self.assertIs(W.validate_row,W.X.validate_row);self.assertIs(W.jobs,W.X.jobs)
        expected=inspect.getsource(W.X.one).replace('0 <= index < 32','index in INDICES').replace('rc-reference-expanded-leaf','rc-reference-completion-leaf')
        self.assertEqual(inspect.getsource(W.one),expected)
        expected=inspect.getsource(W.X.dispatch).replace('rc-reference-expanded-dispatch','rc-reference-completion-dispatch').replace("'timeout_seconds': 120","'timeout_seconds': 180").replace('started >= 120','started >= 180')
        self.assertEqual(inspect.getsource(W.dispatch),expected)
        self.assertEqual(inspect.getsource(R.analysis),inspect.getsource(W.R.analysis))

    def test_exact32_comparison_still_rejects_omission_reorder_and_gate_fail(self):
        rows=T.fake_rows();self.assertTrue(R.analysis(T.PLAN,rows)['passed'])
        self.assertEqual([r['index'] for r in rows[:27]+rows[27:]],[*range(32)])
        for bad in (rows[:27]+rows[28:],rows[:27]+list(reversed(rows[27:])),rows[:27]+rows[27:]+rows[27:28]):
            with self.assertRaises(ValueError):R.analysis(T.PLAN,bad)
        bad=copy.deepcopy(rows);bad[-1]['kernel_row']['ground_C_F_per_m'][0]*=1.03
        self.assertFalse(R.analysis(T.PLAN,bad)['passed'])
        bad=copy.deepcopy(rows);bad[27]['numeric_passed']=False
        with self.assertRaises(ValueError):R.analysis(T.PLAN,bad)

    def test_all_same_actual_residual_energy_units_and_excitation_gates(self):
        for r in T.fake_rows()[27:]:W.validate_row(T.PLAN,r['job'],r['kernel_row'])
        r=T.fake_rows()[27]
        for key,value in [('mesh_step_um',.04),('extent_um',32.),('nodes',70000),('epsilon_layers',[]),('excitations',[])]:
            bad=copy.deepcopy(r['kernel_row']);bad[key]=value
            with self.assertRaises((ValueError,KeyError,IndexError)):W.validate_row(T.PLAN,r['job'],bad)
        bad=copy.deepcopy(r['kernel_row']);bad['excitations'][0]['true_residual_relative']=1.001e-9
        with self.assertRaises(ValueError):W.validate_row(T.PLAN,r['job'],bad)

    def test_five_job_run_has_no_cached_leaf_and_actual_work_guard(self):
        for elapsed in (1049.,1050.001):
            with tempfile.TemporaryDirectory() as temp:
                base=Path(temp);called=[]
                def dispatch(inputs,digest,index,owner):
                    called.append(index);owner.mkdir();(owner/'dispatch.json').write_text('{}')
                    return dict(numeric_passed=True,resource_feasible=True)
                with patch.object(W,'verify',return_value=T.PLAN),patch.object(W,'snapshot',return_value=T.cg()),patch.object(W,'dispatch',side_effect=dispatch),patch.object(W.time,'monotonic',side_effect=[0.]+[1.]*5+[elapsed]):
                    report=W.run(base,'pin',base/'out')
                self.assertEqual(called,W.INDICES);self.assertTrue(report['measurement_packet_completed'])
                self.assertTrue(report['all_numeric_leaves_passed']);self.assertIs(report['passed'],elapsed<=1050)
                self.assertEqual(R.work_state(report,[dict(resource_feasible=True,numeric_passed=True)]*5),(True,True,elapsed<=1050,True))
                bad=dict(report,wall_seconds=elapsed+1)
                with self.assertRaises(ValueError):R.work_state(bad,[dict(resource_feasible=True,numeric_passed=True)]*5)

    def test_resource_failure_stops_exact_suffix_no_prefix_pass(self):
        with tempfile.TemporaryDirectory() as temp:
            base=Path(temp);called=[]
            def dispatch(inputs,digest,index,owner):
                called.append(index);owner.mkdir();(owner/'dispatch.json').write_text('{}')
                return dict(numeric_passed=False,resource_feasible=False)
            with patch.object(W,'verify',return_value=T.PLAN),patch.object(W,'snapshot',return_value=T.cg()),patch.object(W,'dispatch',side_effect=dispatch),patch.object(W.time,'monotonic',side_effect=[0.,1.,2.]):
                report=W.run(base,'pin',base/'out')
            self.assertEqual(called,[27]);self.assertFalse(report['measurement_packet_completed']);self.assertFalse(report['passed'])

    def test_new_command_offline_unchanged_resources_and_no_foreign_indices(self):
        with tempfile.TemporaryDirectory() as temp:
            base=Path(temp)
            with patch.object(W,'verify',return_value=dict(producer_sha256={})),patch.object(W.X,'verify',return_value=dict(producer_sha256={})):
                row=W.proposal(base,'pin',base);self.assertEqual(row['timeout_seconds'],1110)
                self.assertEqual(row['argv'].count('--mount'),3);self.assertIn('2g',row['argv'])
                self.assertIn('/tmp:rw,nosuid,noexec,size=134217728',row['argv'])
            with patch.object(W,'verify',return_value=T.PLAN),patch.object(W,'snapshot',return_value=T.cg()):
                for index in (-1,0,26,32):
                    with self.assertRaises(ValueError):W.one(base,'pin',index,base/'leaf')
        self.assertIn("cleanup_sentinel",inspect.getsource(R.resource_join))

    def test_failed_composite_cannot_promote_or_masquerade_as_old_authority(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'dep';p.write_text('{}');binding=W.H.bound(p)
            row=dict(new_completion_plan=binding,execution_report=binding,command_proposal=binding,
                resource_cleanup_join=dict(resource_report=binding),original_failed_expanded_authority=binding,
                composite32_reference_complete_passed=False)
            authority=Path(temp)/'authority';authority.write_text(json.dumps(row))
            with patch.object(R,'readback',return_value=row):
                with self.assertRaisesRegex(ValueError,'cannot confer authority'):R.closed_authority(authority)
            self.assertNotIn('new_expanded_reference_plan',row);self.assertNotIn('new_reference_only_plan',row)


if __name__=='__main__':unittest.main()
