"""Independent HOST full-raw/source-policy/resource reopener; no Native."""
import argparse
import json
import math
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_via as W
import streaming_8x4_model24_custody as C


def checked_input_seals(inputs,plan,resource):
    required={str((inputs/n).resolve()):r['sha256']for n,r in plan['files'].items()}
    W.need(all(resource['input_sha256'].get(n)==h for n,h in required.items()),'Complete prepared resource input seals differ')
    return len(required)


def read_leaf(inputs,digest,plan,job,owner):
    need=W.need;path=C.regular(owner/'report.json');row=json.loads(path.read_text())
    need(row['schema']=='pinwheel.model24-via-arithmetic-leaf.v1'and row['plan_sha256']==digest and row['job']==job
        and row['argv'][1:]==['-no_init','-exit','run.tcl']and Path(row['argv'][0]).name=='openroad'
        and row['openroad_sha256']==W.A.OPENROAD_SHA and row['native_executed']is True and row['process_tree_reaped']is True
        and all(row[k]is True for k in ('inputs_sources_unchanged','copied_inputs_unchanged','openroad_unchanged'))
        and row['model_qualified']is row['qualified_timing']is False,'Actual leaf command/source/custody/scope differs')
    env=row['environment'];need(set(env)=={'PATH','HOME','LANG','LC_ALL','TZ','OMP_NUM_THREADS','OMP_DYNAMIC'}and env['PATH']
        and all(env[k]==v for k,v in dict(HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE').items()),'Actual environment differs')
    cg=row['cgroups'];cpu=cg['cpu_max'].split();need(len(cpu)==2 and all(v.isdigit()for v in cpu)and 0<int(cpu[0])<=int(cpu[1])
        and cg['memory_max']=='2147483648'and cg['memory_swap_max']=='0'and cg['pids_max']=='128','Actual cgroup limits differ')
    need(W.A.owned_inventory(owner)==row['output_inventory']and W.E.sha(C.regular(owner/'native.log'))==row['native_log_sha256'],'Complete output/log inventory differs')
    for dst,src in W.copied(job).items():need((owner/dst).read_bytes()==(inputs/src).read_bytes(),'Selected copied input differs')
    duration=row['actual_work_seconds'];need(type(duration)in(int,float)and math.isfinite(duration)and duration>=0 and row['work_budget_passed']is(duration<=40),'Leaf measured closeout clock differs')
    feasible=W.S.N.resource_observation(row)and row['work_budget_passed']and sum(r['bytes']for r in row['output_inventory'].values())<=W.policy()['maximum_output_bytes']
    analysis=None;failure=None
    try:
        need(row['exit_code']==0 and not row['timed_out']and not row['memory_guard_triggered']and not row['output_guard_triggered'],'Native resource/exit failed')
        analysis=W.parse_leaf(owner,plan,job)
    except (ValueError,OSError,KeyError)as e:failure=type(e).__name__+': '+str(e)
    passed=failure is None and feasible and analysis['source_policy_arithmetic_passed']
    need(row['analysis']==analysis and row['measurement_completed']is(failure is None)and row['resource_feasible']is feasible and row['passed']is passed
        and(failure is None or row['error']==failure),'Raw/reference/geometry/failure verdict differs')
    return row


def readback(inputs,digest,directory,resource,proposal_path,root_go):
    need=W.need;plan=W.verify(inputs,digest);proposal=json.loads(C.regular(proposal_path).read_text())
    need(directory.name==W.OUTPUT and proposal==W.proposal(inputs,digest,directory.parent,False),'Exact command/owner differs')
    report=json.loads(C.regular(directory/'report.json').read_text());jobs=report['jobs'];universe=W.jobs()
    need(report['schema']=='pinwheel.model24-via-arithmetic-execution.v1'and report['plan_sha256']==digest and report['policy']==W.policy()
        and report['inputs_sources_unchanged']is True and report['model_qualified']is report['qualified_timing']is False
        and len(jobs)<=6 and [r['job']for r in jobs]==universe[:len(jobs)]
        and{p.name for p in directory.iterdir()}=={'report.json'}|{r['id']for r in universe[:len(jobs)]},'Exact complete/prefix source/owner membership differs')
    rows=[]
    for i,record in enumerate(jobs):
        r=read_leaf(inputs,digest,plan,record['job'],directory/record['job']['id']);rows.append(r)
        need(record==dict(job=r['job'],report_sha256=W.E.sha(directory/r['job']['id']/'report.json'),**{k:r[k]for k in ('passed','resource_feasible','measurement_completed')}),'Exact leaf metadata join differs')
        need(i==len(jobs)-1 or(r['resource_feasible']and r['measurement_completed']),'Forbidden suffix after structural/resource failure')
    duration=report['actual_work_seconds'];need(type(duration)in(int,float)and math.isfinite(duration)and duration>=0 and report['work_budget_passed']is(duration<=210),'Actual total work budget differs')
    state=W.packet_state(rows,duration);need(all(report[k]==v for k,v in state.items()),'Full fixed six-call diagnostic gate differs')
    joined=C.resource_join(resource,proposal_path,proposal,plan,report,root_go)
    actual=json.loads(C.regular(resource).read_text());checked=checked_input_seals(inputs,plan,actual)
    return dict(schema='pinwheel.model24-via-arithmetic-independent-readback.v1',plan_sha256=digest,execution_report_sha256=W.E.sha(directory/'report.json'),
        jobs=rows,**state,resource_cleanup_join=joined,prepared_resource_seals_checked=checked,
        baseline_actual_mismatches_remain_mismatches=state['expected_baseline_mismatches_preserved'],reference_scope=W.policy()['reference'],native_executed_by_readback=False,
        physical_fit=False,SPECIALNETS_extraction_qualified=False,contact_spreading_and_independent_cut_physics_qualified=False,
        foundry_corner_correlation_qualified=False,capacitance_qualified=False,full_via_coverage_qualified=False,model_qualified=False,qualified_timing=False)


def main():
    q=argparse.ArgumentParser(description=__doc__)
    for n in ('inputs','directory','resource-report','command-proposal','root-go','output'):q.add_argument('--'+n,type=Path,required=True)
    q.add_argument('--plan-sha256',required=True);a=q.parse_args();W.need(not a.output.exists(),'Preserve prior readback')
    r=readback(a.inputs,a.plan_sha256,a.directory,a.resource_report,a.command_proposal,a.root_go);W.write(a.output,r)
    return 0 if r['source_policy_diagnostic_passed']else 2
if __name__=='__main__':raise SystemExit(main())
