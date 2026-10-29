"""Portable controls only: no ignored captures, FVM solve, child or Docker."""
import copy
import ast
import inspect
import json
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'scripts'))
import streaming_8x4_closure48_reference_completion as W
import streaming_8x4_closure48_reference_readback as R
C=W.C


def fixture():
    cases=[dict(name='case'+str(i),rectangles=[dict(name='a',bounds_um=['-.1','.1','1','1.2'])]
        +([] if i<4 else [dict(name='b',bounds_um=['-.1','.1','2','2.2'])]),epsilon_layers=[['0','64','4.1']]) for i in range(8)]
    plan=dict(cases=cases,protocol=dict(maximum_cg_iterations=6000,true_residual_relative_tolerance='1e-9',
        energy_flux_relative_tolerance='1e-7',reciprocity_relative_tolerance='1e-7'))
    plan['grid_inventory']=[dict(case=j['case'],step_um=j['step'],extent_um=j['extent'],nodes=1000) for j in W.jobs(plan)]
    rows=[]
    for index,job in enumerate(W.jobs(plan)):
        case=cases[index//4];n=len(case['rectangles']);matrix=[[1e-10]] if n==1 else [[2e-10,-1e-10],[-1e-10,2e-10]]
        value=dict(schema='pinwheel.streaming-8x4-rc-layered-reference.v1',qualified=False,continuum_error_enclosure=False,
            names=[r['name'] for r in case['rectangles']],rectangles=[dict(name=r['name'],bounds_um=list(map(float,r['bounds_um']))) for r in case['rectangles']],
            epsilon_layers=[[0.,64.,4.1]],mesh_step_um=float(job['step']),extent_um=float(job['extent']),
            matrix_F_per_m=matrix,ground_C_F_per_m=[sum(r) for r in matrix],coupling_C_F_per_m=None if n==1 else 1e-10,
            excitations=[dict(name=r['name'],true_residual_relative=1e-10,cg_iterations=40,energy_flux_relative_error=1e-9) for r in case['rectangles']],
            nodes=1000,unknown_nodes=900,reciprocity_relative_error=0.,wall_seconds=1.)
        rows.append(dict(index=index,job=job,resource_feasible=True,numeric_passed=True,kernel_row=value))
    return plan,rows


def signature(code):
    return (code.co_code,code.co_names,code.co_varnames,tuple(signature(c) if isinstance(c,types.CodeType)
        else c.replace(C.PREFIX,C.OLD_PREFIX) if isinstance(c,str) else c for c in code.co_consts))


class Completion48(unittest.TestCase):
    def test_exact_operational_body_and_new_global_ownership(self):
        for name in ('dispatch_argv','one','dispatch','run'):
            expected={};exec(compile(C.body(W.BASE,name).replace(C.OLD_PREFIX,C.PREFIX),'<control>','exec'),expected)
            self.assertEqual(signature(getattr(W,name).__code__),signature(expected[name].__code__))
            self.assertIs(getattr(W,name).__globals__,vars(W))
            self.assertIs(getattr(W.BASE,name).__globals__,vars(W.BASE))
        for name in ('numeric_leaf','dispatch','analysis','work_state'):
            expected={};exec(compile(C.body(W.OLD_READER,name).replace(C.OLD_PREFIX,C.PREFIX),'<control>','exec'),expected)
            self.assertEqual(signature(getattr(R,name).__code__),signature(expected[name].__code__))
            self.assertIs(getattr(R,name).__globals__,vars(R))
        self.assertIs(W.BASE.one.__globals__['verify'],W.BASE.verify)
        self.assertIs(W.F,W.BASE.F);self.assertIs(W.validate_row,W.BASE.validate_row)
        expected=C.body(W.OLD_READER,'readback').replace(C.OLD_PREFIX,C.PREFIX).replace(
            'def readback(inputs, digest, directory, resource_path, proposal_path):',
            'def readback(inputs, digest, directory, resource_path, proposal_path, root_go):').replace(
            'resource_join(resource_path, proposal_path, proposal, plan, report)',
            'resource_join(resource_path, proposal_path, proposal, plan, report, root_go)')
        self.assertEqual(R._source,expected)

    def test_exact_suffix_math_resource_and_source_closure(self):
        self.assertEqual(W.INDICES,[27,28,29,30,31]);self.assertEqual(C.OLD_PLAN,'7bd27dc9a7f6e9b7f8e44189886f271a2ae8e20c5321ed662c49d26deb70abd9')
        left,right=W.policy(),W.BASE.policy()
        for key in ('schema','scope'):left.pop(key);right.pop(key)
        self.assertEqual(left.pop('campaign_id'),C.CLOCK.CAMPAIGN);self.assertEqual(left,right)
        self.assertEqual((left['seconds_per_leaf'],left['work_seconds'],left['outer_seconds']),(180,1050,1110))
        pending=list(W.NEW)+['streaming_8x4_closure48_resources.py'];names=set()
        while pending:
            name=pending.pop()
            if name in names:continue
            names.add(name)
            for node in ast.walk(ast.parse((ROOT/'scripts'/name).read_text())):
                modules=[n.name for n in node.names] if isinstance(node,ast.Import) else [node.module] if isinstance(node,ast.ImportFrom) else []
                pending += [n+'.py' for n in modules if n and n.startswith('streaming_') and '.' not in n]
        self.assertTrue(names<=set(W.sources()))
        self.assertTrue({Path(n).name for n in C.CLOCK.HISTORICAL}<=set(W.sources()))
        self.assertTrue(C.derivation(W.BASE,W.OLD_READER)['all_equations_and_numeric_gates_unchanged'])
        with patch.dict(C.PINS,{Path(W.BASE.__file__).name:'0'*64}):
            with self.assertRaisesRegex(ValueError,'Frozen'):C.body(W.BASE,'one')

    def test_complete32_no_omission_duplicate_order_or_relaxed_comparisons(self):
        plan,rows=fixture();self.assertTrue(R.analysis(plan,rows)['passed'])
        for bad in (rows[:-1],list(reversed(rows)),rows+[rows[0]]):
            with self.assertRaises(ValueError):R.analysis(plan,bad)
        for field in ('ground_C_F_per_m','matrix_F_per_m'):
            bad=copy.deepcopy(rows)
            if field=='ground_C_F_per_m':bad[-1]['kernel_row'][field][0]*=1.03
            else:bad[-1]['kernel_row'][field][0][1]*=1.03
            self.assertFalse(R.analysis(plan,bad)['passed'])
        bad=copy.deepcopy(rows);bad[27]['numeric_passed']=False
        with self.assertRaises(ValueError):R.analysis(plan,bad)

    def test_same_full_geometry_excitation_nodes_residual_and_energy_gates(self):
        plan,rows=fixture()
        for row in rows:W.validate_row(plan,row['job'],row['kernel_row'])
        for key,value in [('nodes',1001),('epsilon_layers',[]),('excitations',[]),('extent_um',16.),('ground_C_F_per_m',[1.])]:
            bad=copy.deepcopy(rows[-1]['kernel_row']);bad[key]=value
            with self.assertRaises((ValueError,KeyError)):W.validate_row(plan,rows[-1]['job'],bad)
        for key,value in [('true_residual_relative',1.001e-9),('energy_flux_relative_error',1.001e-7)]:
            bad=copy.deepcopy(rows[-1]['kernel_row']);bad['excitations'][0][key]=value
            with self.assertRaises(ValueError):W.validate_row(plan,rows[-1]['job'],bad)

    def test_original_five_call_loop_no_cache_work_overrun_and_resource_stop(self):
        plan,_=fixture()
        for elapsed,resource in ((1049.,True),(1050.001,True),(2.,False)):
            with tempfile.TemporaryDirectory() as temp:
                base=Path(temp);called=[]
                def dispatch(inputs,digest,index,owner):
                    called.append(index);owner.mkdir();(owner/'dispatch.json').write_text('{}')
                    return dict(numeric_passed=resource,resource_feasible=resource)
                times=[0.]+[1.]*(5 if resource else 1)+[elapsed]
                with patch.object(W,'verify',return_value=plan),patch.object(W,'snapshot'),patch.object(W,'dispatch',side_effect=dispatch),patch.object(W.time,'monotonic',side_effect=times):
                    report=W.run(base,'pin',base/'out')
                self.assertEqual(called,W.INDICES if resource else [27])
                self.assertIs(report['passed'],resource and elapsed<=1050)
                self.assertFalse(report['qualified']);self.assertFalse(report['model_qualified'])
                if resource:self.assertEqual(R.work_state(report,[dict(resource_feasible=True,numeric_passed=True)]*5),(True,True,elapsed<=1050,True))

    def test_exact_five_token_proposal_and_two_gib_no_swap_offline(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp).resolve();inputs=root/'build/campaigns'/C.CLOCK.CAMPAIGN/'prep';parent=inputs.parent/'native';parent.mkdir(parents=True)
            baseline=['docker','run',W.BASE.CONTAINER,'type=bind,src='+str(inputs/'historical-completion')+',dst=/rc-inputs,readonly',
                '/rc-source/'+W.BASE.NEW[0],C.OLD_PLAN,'/rc-output-parent/'+W.BASE.OUTPUT]
            with patch.object(W,'ROOT',root),patch.object(W,'verify',return_value=dict(producer_sha256={})),patch.object(W.BASE,'proposal',return_value={'argv':baseline}):
                got=W.proposal(inputs,'b'*64,parent)
            self.assertEqual(len(got['argv']),len(baseline));self.assertEqual(sum(a!=b for a,b in zip(got['argv'],baseline)),5)
            actual=inspect.getsource(W.BASE.X.proposal)
            for token in ("'--cpus','1'","'--memory','2g'","'--memory-swap','2g'",'size=134217728'):
                self.assertIn(token,actual)
            self.assertEqual(got['timeout_seconds'],1110)

    def test_failed_authority_cannot_promote_and_signal_is_durable_exception(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'dep';p.write_text('{}');pin=C.bound(p)
            row=dict(schema=C.PREFIX+'independent-readback.v1',new_completion_plan=pin,execution_report=pin,
                command_proposal=pin,resource_cleanup_join=dict(resource_report=pin,root_go=pin),
                original_failed_expanded_authority=pin,composite32_reference_complete_passed=False)
            a=Path(temp)/'authority';a.write_text(json.dumps(row))
            with patch.object(R,'readback',return_value=row):
                with self.assertRaisesRegex(ValueError,'cannot confer'):R.closed_authority(a)
            row['schema']=C.OLD_PREFIX+'independent-readback.v1';a.write_text(json.dumps(row))
            with self.assertRaisesRegex(ValueError,'Foreign'):R.closed_authority(a)
        with self.assertRaises(InterruptedError):W.interrupted(15,None)

    def test_new_plan_exact_copied_input_membership_and_failed_history(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp).resolve();baseline=root/'baseline';baseline.mkdir()
            plan,_=fixture();plan.update(schema=C.OLD_PREFIX+'plan.v1',selected_indices=W.INDICES,
                selected_jobs=[dict(index=i,**W.jobs(plan)[i]) for i in W.INDICES])
            (baseline/'plan.json').write_text('{}');(baseline/'failed-expanded-authority.json').write_text('{"failed":true}')
            failed=W.E.sha(baseline/'failed-expanded-authority.json');owner=root/'build/campaigns'/C.CLOCK.CAMPAIGN/'prep';owner.parent.mkdir(parents=True)
            with patch.object(W,'ROOT',root),patch.object(W.BASE,'verify',return_value=plan),\
                 patch.object(W.BASE,'reopen_parent',return_value={}),patch.object(W.BASE,'FAILED',failed):
                row=W.prepare(baseline,owner);digest=W.E.sha(owner/'plan.json')
                self.assertEqual(row,W.verify(owner,digest));self.assertEqual(row['schema'],C.PREFIX+'plan.v1')
                self.assertEqual((owner/'historical-completion/plan.json').read_bytes(),(baseline/'plan.json').read_bytes())
                (owner/'foreign').write_text('unlisted')
                with self.assertRaises(ValueError):W.verify(owner,digest)
                (owner/'foreign').unlink();(owner/'failed-expanded-authority.json').write_text('changed')
                with self.assertRaisesRegex(ValueError,'failed expanded'):W.verify(owner,digest)

    def test_original_native_cgroup_limits_and_counter_changes_remain_strict(self):
        sample=dict(memory_current=1000,memory_peak=2000,memory_max=2147483648,memory_swap_max=0,pids_max=128,
            cpu_max='100000 100000',memory_events=dict(max=0,oom=0,oom_kill=0),memory_events_local=dict(max=0,oom=0,oom_kill=0))
        W.validate_snapshot(sample)
        for key,value in (('memory_max',2147483649),('memory_swap_max',1),('cpu_max','200000 100000'),('pids_max',129)):
            with self.assertRaises(ValueError):W.validate_snapshot(dict(sample,**{key:value}))
        state=dict(cgroup_before=sample,cgroup_after=copy.deepcopy(sample),counter_deltas=W.deltas(sample,sample),
            maximum_polled_memory_current=1500,process_tree_reaped=True,timed_out=False,memory_guard_triggered=False,exit_code=0)
        self.assertTrue(W.resource_feasible(state));state['cgroup_after']['memory_events']['oom_kill']=1
        state['counter_deltas']=W.deltas(sample,state['cgroup_after']);self.assertFalse(W.resource_feasible(state))

    def resource_fixture(self,root):
        root=Path(root).resolve();scripts=root/'scripts';scripts.mkdir()
        names={Path(n).name for n in C.CLOCK.HISTORICAL}|set(W.NEW)|{'streaming_8x4_closure48_policy.py','streaming_8x4_closure48_resources.py'}
        for name in names:(scripts/name).write_bytes((ROOT/'scripts'/name).read_bytes())
        owner=root/'build/campaigns'/C.CLOCK.CAMPAIGN;owner.mkdir(parents=True);inputs=owner/'prep';inputs.mkdir()
        (inputs/'plan.json').write_text('{}');(inputs/'one').write_text('data')
        plan=dict(producer_sha256={n:C.CLOCK.sha(scripts/n) for n in names},files={'one':dict(kind='file',sha256=C.CLOCK.sha(inputs/'one'))})
        def save(path,value):path.write_text(json.dumps(value));return C.bound(path)
        proposal=dict(argv=['docker','run','fixed'],container_name='pinwheel-fixed',plan_path=str(inputs/'plan.json'),plan_sha256=C.CLOCK.sha(inputs/'plan.json'))
        p=owner/'proposal.json';save(p,proposal)
        seals={str(scripts/n):pin for n,pin in plan['producer_sha256'].items()}
        seals.update({str(p):C.CLOCK.sha(p),str(inputs/'plan.json'):C.CLOCK.sha(inputs/'plan.json'),str(inputs/'one'):C.CLOCK.sha(inputs/'one')})
        admitted=dict(schema='pinwheel.extraction48-root-job-proposal.v2',worker_argv=proposal['argv'],kind='reference-probe',timeout_seconds=1110,
            container_name=proposal['container_name'],parent=None,reference_admission=None,model_qualification=None,timing_failure=None,
            acceptance_claim=False,inputs=[dict(path=n,sha256=pin) for n,pin in seals.items()])
        ap=owner/'Root-proposal.json';ap_pin=save(ap,admitted)
        argv=['/declared/python3.13','-B',str(scripts/'streaming_8x4_closure48_resources.py'),'fixture']
        launch=dict(schema='pinwheel.extraction48-root-job-launch.v1',proposal=ap_pin,resource_supervisor_argv=argv,acceptance_claim=False)
        lp=owner/'launch.json';lp_pin=save(lp,launch)
        go=owner/'Root-GO.json';save(go,dict(schema='pinwheel.extraction48-Root-GO.v1',decision='GO for this exact fixed job only',
            acceptance_claim=False,numerical_tuning_forbidden=True,launch=lp_pin,proposal=ap_pin))
        seals.update({str(ap):ap_pin['sha256'],str(go):C.CLOCK.sha(go)})
        b=dict(schema='pinwheel.streaming-8x4-closure48-resource-boundary.v1',campaign_id=C.CLOCK.CAMPAIGN,campaign_directory=str(owner),
            campaign_root=str(root),schedule=C.CLOCK.SCHEDULE,shared_lease=C.CLOCK.shared_lease_paths(root),campaign_kind='rc_reference_probe',
            wrapper_path=str(scripts/'streaming_8x4_closure48_resources.py'),wrapper_sha256=C.CLOCK.sha(scripts/'streaming_8x4_closure48_resources.py'),
            policy_path=str(scripts/'streaming_8x4_closure48_policy.py'),policy_sha256=C.CLOCK.sha(scripts/'streaming_8x4_closure48_policy.py'),
            inherited_supervisor_path=str(scripts/'streaming_tt_resources.py'),inherited_supervisor_sha256=C.CLOCK.sha(scripts/'streaming_tt_resources.py'),
            historical_producer_sha256=C.CLOCK.historical_sources(root),resource_limits=C.CLOCK.resource_limits('reference-probe'),
            frozen_parent=None,reference_admission_evidence=None,model_qualification_evidence=None,timing_failure_evidence=None,
            reference_admission_verified=False,engineering_evidence_verified=False,acceptance_claim=False,
            initial_window=C.CLOCK.job_window('reference-probe',C.CLOCK.SCHEDULE,C.CLOCK.SCHEDULE['start'],1110),
            actual_wrapper_argv=['/observed/Python.app',*argv[1:]])
        row=dict(schema='pinwheel.streaming-tt-resource-job.v1',argv=proposal['argv'],timeout_seconds=1110,cleanup_confirmed=True,
            inputs_unchanged=True,containers_remaining=[],owned_processes_remaining=[],cleanup_errors=[],acceptance_claim=False,
            exit_code=0,status='completed',supervisor_sha256=b['inherited_supervisor_sha256'],campaign_boundary=b,input_sha256=seals,
            started_utc=C.CLOCK.SCHEDULE['start'],finished_utc='2026-10-25T22:40:00Z')
        resource=owner/'resource.json';save(resource,row)
        return types.SimpleNamespace(ROOT=root),resource,p,proposal,inputs,plan,dict(passed=True),go,row

    def test_actual48_resource_rootgo_current_inputs_and_interpreter_joins(self):
        with tempfile.TemporaryDirectory() as temp:
            args=self.resource_fixture(temp);result=C.resource_join(*args[:-1]);self.assertEqual(result['status'],'completed')
            self.assertFalse(result['interpreter_payload_identity_claim'])
            resource,row=args[1],args[-1]
            for key,value in (('cleanup_confirmed',False),('timeout_seconds',1111),('containers_remaining',['owned']),('exit_code',1)):
                changed=copy.deepcopy(row);changed[key]=value;resource.write_text(json.dumps(changed))
                with self.assertRaises(ValueError):C.resource_join(*args[:-1])
            for key,value in (('campaign_kind','rc_experiment'),('engineering_evidence_verified',True),('wrapper_sha256','0'*64)):
                changed=copy.deepcopy(row);changed['campaign_boundary'][key]=value;resource.write_text(json.dumps(changed))
                with self.assertRaises(ValueError):C.resource_join(*args[:-1])
            resource.write_text(json.dumps(row));(args[4]/'one').write_text('changed')
            with self.assertRaisesRegex(ValueError,'current seals'):C.resource_join(*args[:-1])


if __name__=='__main__':unittest.main()
