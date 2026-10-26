"""HOST dry-grid/source/admission tests only; no field operator, CG or Native."""
import copy
import inspect
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_8x4_rc_reference_expanded as W
import streaming_8x4_rc_reference_expanded_readback as R
B=ROOT/'build/campaigns/8x4-20261022-01'
OLD=json.loads((B/'rc-reference-only-preparation-02/plan.json').read_text())
PLAN=dict(OLD,grid_inventory=W.grid_inventory(OLD['cases']),protocol=W.protocol(OLD))


def fake_rows():
    rows=[]
    for index,job in enumerate(W.jobs(PLAN)):
        case=next(c for c in PLAN['cases'] if c['name']==job['case']);n=len(case['rectangles'])
        matrix=[[1e-10]] if n==1 else [[2e-10,-1e-10],[-1e-10,2e-10]]
        grid=next(g for g in PLAN['grid_inventory'] if (g['case'],g['step_um'],g['extent_um'])==(job['case'],job['step'],job['extent']))
        row=dict(schema='pinwheel.streaming-8x4-rc-layered-reference.v1',qualified=False,continuum_error_enclosure=False,
            names=[r['name'] for r in case['rectangles']],rectangles=[dict(name=r['name'],bounds_um=list(map(float,r['bounds_um']))) for r in case['rectangles']],
            epsilon_layers=[list(map(float,r)) for r in case['epsilon_layers']],mesh_step_um=float(job['step']),extent_um=float(job['extent']),
            matrix_F_per_m=matrix,ground_C_F_per_m=[sum(r) for r in matrix],coupling_C_F_per_m=None if n==1 else 1e-10,
            excitations=[dict(name=r['name'],true_residual_relative=1e-10,cg_iterations=40,energy_flux_relative_error=1e-9) for r in case['rectangles']],
            nodes=grid['nodes'],unknown_nodes=grid['nodes']-100,reciprocity_relative_error=0.,wall_seconds=1.)
        rows.append(dict(index=index,job=job,resource_feasible=True,numeric_passed=True,kernel_row=row))
    return rows


def cg():
    return dict(memory_current=1000,memory_peak=2000,memory_max=2147483648,memory_swap_max=0,pids_max=128,cpu_max='100000 100000',
        memory_events=dict(max=0,oom=0,oom_kill=0),memory_events_local=dict(max=0,oom=0,oom_kill=0))


class ExpandedControls(unittest.TestCase):
    def test_exact_two_admission_changes_and_axis_equation_derivation(self):
        proof=W.kernel_derivation();self.assertTrue(proof['solve_body_identical_after_domain_guard_normalization'])
        self.assertTrue(proof['axis_body_byte_identical']);self.assertTrue(proof['no_frozen_module_monkeypatch'])
        self.assertIn('extent in (32.0, 64.0)',Path(W.F.__file__).read_text())
        self.assertIn('maximum_nodes=70000',Path(W.F.__file__).read_text())
        self.assertEqual(proof['original_source_sha256'],'5a21e1a89b942e770557850319b48592ec04f5bfa420be81fd42fe8843138e03')
        self.assertEqual(proof['normalized_solve_body_sha256'],'a01b8ac269355e2e29d9f023258483ae72e312095c2a2f1d11b88996b82b3476')

    def test_equation_tolerance_or_admission_drift_fails_source_normalization(self):
        text=Path(W.F.__file__).read_text()
        for mutation in (text.replace('energy > 0','energy >= 0'),text.replace('reciprocity <= 1e-7','reciprocity <= 1e-6'),
            text.replace('maximum_nodes=70000','maximum_nodes=71000'),text.replace('extent in (32.0, 64.0)','extent in (16.0, 32.0, 64.0)')):
            with tempfile.TemporaryDirectory() as temporary:
                path=Path(temporary)/'kernel.py';path.write_text(mutation)
                with patch.object(W.F,'__file__',str(path)):
                    with self.assertRaises(ValueError):W.kernel_derivation()

    def test_exact32_new_grids_and_reviewed_storage_under_same_guard(self):
        grids=W.grid_inventory(OLD['cases']);self.assertEqual(len(grids),32)
        self.assertEqual({r['extent_um'] for r in grids},{'32','64'})
        self.assertEqual(max(r['nodes'] for r in grids),68817);self.assertEqual(sum(r['nodes'] for r in grids),1045176)
        budget=W.storage_admission(OLD);self.assertEqual(budget['conservative_total_bytes'],1549533184)
        self.assertEqual(budget['headroom_bytes'],597950464);self.assertFalse(budget['measured_RSS'])
        self.assertGreater(budget['headroom_below95percent_guard_bytes'],0)
        self.assertEqual(W.policy()['maximum_nodes'],70000)

    def test_old_kernel_parent_case_and_tolerances_stay_frozen(self):
        W.O.verify(B/'rc-reference-only-preparation-02',W.BASELINE)
        approved=json.loads((B/'rc-reference-expanded-proposal-02.json').read_text())
        self.assertEqual(approved['cases'],OLD['cases']);self.assertEqual(approved['grid_inventory'],PLAN['grid_inventory'])
        self.assertEqual(approved['superseded_proposal01_sha256'],'49b93e1a0d5225dbcb11a469d72ce2966600c418d55c4d74e40438c06c63b9a6')
        for key in ('true_residual_relative_tolerance','energy_flux_relative_tolerance','maximum_reference_mesh_change','maximum_reference_domain_change'):
            self.assertEqual(PLAN['protocol'][key],OLD['protocol'][key])

    def test_full_actual_geometry_nodes_excitation_and_residual_gates(self):
        for leaf in fake_rows():W.validate_row(PLAN,leaf['job'],leaf['kernel_row'])
        leaf=fake_rows()[-1]
        for key,value in [('nodes',65000),('extent_um',32),('epsilon_layers',[]),('ground_C_F_per_m',[1.]),('reciprocity_relative_error',float('nan'))]:
            row=copy.deepcopy(leaf['kernel_row']);row[key]=value
            with self.assertRaises((ValueError,KeyError,IndexError)):W.validate_row(PLAN,leaf['job'],row)
        for mutation in ('residual','emptyexcitation','reordered','energy'):
            row=copy.deepcopy(leaf['kernel_row'])
            if mutation=='residual':row['excitations'][0]['true_residual_relative']=1.01e-9
            elif mutation=='emptyexcitation':row['excitations']=[]
            elif mutation=='reordered':row['excitations'].reverse()
            else:row['excitations'][0]['energy_flux_relative_error']=1e-6
            with self.assertRaises(ValueError):W.validate_row(PLAN,leaf['job'],row)

    def test_complete_E64_mesh_and_E32to64_domain_all_cell_comparisons(self):
        rows=fake_rows();result=R.analysis(PLAN,rows);self.assertTrue(result['passed']);self.assertEqual(len(result['cases']),8)
        for bad in (rows[:-1],list(reversed(rows)),rows+[rows[0]]):
            with self.assertRaises(ValueError):R.analysis(PLAN,bad)
        for index in (-1,-2):
            bad=copy.deepcopy(rows);bad[index]['kernel_row']['matrix_F_per_m'][0][1]*=1.03
            self.assertFalse(R.analysis(PLAN,bad)['passed'])
        bad=copy.deepcopy(rows);bad[-1]['numeric_passed']=False
        with self.assertRaises(ValueError):R.analysis(PLAN,bad)

    def test_guard_reused_unchanged_and_workflow_has_no_numeric_prefix_promotion(self):
        self.assertIs(W.snapshot,W.O.snapshot);self.assertIs(W.resource_feasible,W.O.resource_feasible)
        for function in ('one','dispatch'):
            source=inspect.getsource(getattr(W.O,function)).replace('pinwheel.streaming-8x4-rc-reference-only-','pinwheel.streaming-8x4-rc-reference-expanded-')
            source=source.replace('maximum_nodes=65000','maximum_nodes=70000')
            self.assertEqual(inspect.getsource(getattr(W,function)),source)
        prefix=inspect.getsource(W.O.run).replace('pinwheel.streaming-8x4-rc-reference-only-','pinwheel.streaming-8x4-rc-reference-expanded-').split('    finally:')[0]
        self.assertEqual(inspect.getsource(W.run).split('    finally:')[0],prefix)
        self.assertIn("row['native_log_empty']",inspect.getsource(W.dispatch))
        self.assertIn("row['native_log_empty']",inspect.getsource(R.dispatch))
        before=cg();after=cg();row=dict(cgroup_before=before,cgroup_after=after,counter_deltas=W.deltas(before,after),
            maximum_polled_memory_current=1500,process_tree_reaped=True,timed_out=False,memory_guard_triggered=False,exit_code=0)
        self.assertTrue(W.resource_feasible(row));row['cgroup_after']['memory_events']['oom_kill']=1
        row['counter_deltas']=W.deltas(before,after);self.assertFalse(W.resource_feasible(row))

    def test_failed_closed_expanded_authority_cannot_promote_old_or_new_receipts(self):
        with tempfile.TemporaryDirectory() as temporary:
            dep=Path(temporary)/'dependency';dep.write_text('{}');binding=W.H.bound(dep)
            row=dict(new_expanded_reference_plan=binding,execution_report=binding,command_proposal=binding,
                resource_cleanup_join=dict(resource_report=binding),expanded_reference_complete_passed=False)
            path=Path(temporary)/'authority';path.write_text(json.dumps(row))
            with patch.object(R,'readback',return_value=row):
                with self.assertRaisesRegex(ValueError,'cannot confer authority'):R.closed_authority(path)
            # Original reference-only reader has a different typed plan key/schema;
            # this result deliberately cannot masquerade as that old authority.
            self.assertNotIn('new_reference_only_plan',row)

    def test_same_two_GiB120s_leaf_offline_explicit_new_command(self):
        with tempfile.TemporaryDirectory() as temporary:
            base=Path(temporary).resolve()
            with patch.object(W,'verify',return_value=dict(producer_sha256={})):
                command=W.proposal(base,'pin',base)['argv']
            self.assertIn('2g',command);self.assertEqual(command.count('--mount'),3)
            self.assertIn('/tmp:rw,nosuid,noexec,size=134217728',command)
        argv=W.dispatch_argv(Path('/rc-inputs'),'pin',0,Path('/out'))
        self.assertEqual(argv[0],W.PYTHON);self.assertEqual(argv[3],'/rc-source/'+W.NEW[0])
        self.assertEqual(W.policy()['seconds_per_leaf'],120);self.assertEqual(W.policy()['outer_seconds'],1860)
        self.assertFalse(W.policy()['model_qualified']);self.assertFalse(W.policy()['finite_BEM_passed'])

    def test_actual_work_overrun_retains_measurement_numeric_but_cannot_pass(self):
        for elapsed in (1799.9,1800.001):
            with tempfile.TemporaryDirectory() as temporary:
                output=Path(temporary)/'out'
                def dispatch(inputs,digest,index,owner):
                    owner.mkdir();(owner/'dispatch.json').write_text('{}')
                    return dict(numeric_passed=True,resource_feasible=True)
                times=[0.]+[1.]*32+[elapsed]
                with patch.object(W,'verify',return_value=PLAN),patch.object(W,'snapshot',return_value=cg()), \
                    patch.object(W,'dispatch',side_effect=dispatch),patch.object(W.time,'monotonic',side_effect=times):
                    row=W.run(Path(temporary),'pin',output)
                self.assertTrue(row['measurement_packet_completed']);self.assertTrue(row['all_numeric_leaves_passed'])
                self.assertEqual(row['actual_work_seconds'],elapsed)
                self.assertIs(row['work_budget_passed'],elapsed<=1800)
                self.assertIs(row['resource_feasible'],elapsed<=1800);self.assertIs(row['passed'],elapsed<=1800)
                observed=[dict(resource_feasible=True,numeric_passed=True) for _ in range(32)]
                self.assertEqual(R.work_state(row,observed),(True,True,elapsed<=1800,True))
                if elapsed>1800:
                    bad=dict(row,work_budget_passed=True,resource_feasible=True,passed=True)
                    with self.assertRaises(ValueError):R.work_state(bad,observed)
                for bad in (dict(row,actual_work_seconds=float('nan')),dict(row,wall_seconds=elapsed+1)):
                    with self.assertRaises(ValueError):R.work_state(bad,observed)


if __name__=='__main__':unittest.main()
