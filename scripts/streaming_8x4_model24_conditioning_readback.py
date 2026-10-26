"""HOST-only full factorial/raw/resource reader; no coefficient qualification."""
import argparse
import json
import math
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_conditioning as W
import streaming_8x4_model24_custody as C


def read_leaf(inputs,digest,plan,job,directory):
    path=C.regular(directory/'report.json');r=json.loads(path.read_text());source=inputs/'smoke-inputs'/('case-'+str(job['case']).zfill(3))/'geometry';case=W.S.verify(inputs/'smoke-inputs',W.SMOKE_PLAN)['cases'][job['case']]
    W.P.need(r['schema']=='pinwheel.model24-fullstack-conditioning-leaf.v1' and r['plan_sha256']==digest and r['job']==job
        and r['argv']==W.Q.argv(job['branch']) and r['environment']==W.I.W.C.ENVIRONMENT
        and r['model_qualified'] is False and r['qualified_timing'] is False and r['native_executed'] is True
        and r['process_tree_reaped'] is True and r['inputs_sources_unchanged'] is True and r['runtime_unchanged'] is True
        and r['copied_inputs_unchanged'] is True,'Exact conditioning scope/geometry/job/command/custody differs')
    W.P.need({p.name for p in directory.iterdir()}=={'report.json','native.log','work'} and W.E.tree(directory/'work')==W.E.tree(source)
        and W.E.sha(C.regular(directory/'native.log'))==r['native_log_sha256'],'Conditioning copied geometry/log differs')
    cg=r['cgroups'];cpu=cg['cpu_max'].split();W.P.need(len(cpu)==2 and all(v.isdigit() for v in cpu) and 0<int(cpu[0])<=int(cpu[1])
        and cg['memory_max']=='6442450944' and cg['memory_swap_max']=='0' and cg['pids_max']=='128','Conditioning actual cgroup envelope differs')
    changes=W.I.counters(r['cgroup_before'],r['cgroup_after']);W.P.need(r['cgroup_counter_deltas']==changes
        and type(r['maximum_polled_memory_current']) is int and r['cgroup_before']['memory_current']<=r['maximum_polled_memory_current']<=r['cgroup_after']['memory_peak'],
        'Conditioning cgroup deltas/peak differ')
    for snapshot in (r['cgroup_before'],r['cgroup_after']):W.P.need(snapshot['memory_max']==6442450944 and snapshot['memory_swap_max']==0,'Conditioning memory/swap differs')
    W.P.need(type(r['wall_seconds']) in (int,float) and math.isfinite(r['wall_seconds']) and 0<=r['wall_seconds']<70,'Conditioning terminal leaf clock differs')
    raw=(directory/'native.log').read_text();numeric=None;failure=None
    try:numeric=W.Q.parse(raw,case['ordered_conductor_roles'],job['branch'],r['exit_code'],r['timed_out'],r['memory_guard_triggered'])
    except (ValueError,OSError) as e:failure=type(e).__name__+': '+str(e)
    actual_bytes=sum(p.stat().st_size for p in directory.rglob('*') if p.is_file() and not p.is_symlink() and p!=directory/'report.json')
    W.P.need(r['actual_output_bytes']==actual_bytes,'Conditioning actual output bytes differ')
    feasible=W.I.resource_feasible(r) and r['process_tree_reaped'] and r['output_guard_triggered'] is False and actual_bytes<=W.policy()['maximum_output_bytes']
    W.P.need(r['numeric']==numeric and r['numeric_passed'] is (failure is None) and r['resource_feasible'] is feasible
        and r['actual_f0_observed'] is W.I.mode_observed(raw) and r['passed'] is (failure is None and feasible)
        and (failure is None or r['error']==failure),'Independent conditioning raw physics/resource/failure differs')
    return dict(**job,numeric_passed=r['numeric_passed'],resource_feasible=feasible,error=failure,numeric=numeric,
        actual_leaf=r,report_sha256=W.E.sha(path))


def work_state(row,leaves):
    duration=row['actual_work_seconds'];W.P.need(type(duration) in (int,float) and math.isfinite(duration) and duration>=0
        and row['work_budget_passed'] is (duration<=540),'Conditioning actual work clock differs')
    complete=len(leaves)==8;allnumeric=complete and all(r['numeric_passed'] for r in leaves)
    resources=complete and all(r['resource_feasible'] for r in leaves) and row['work_budget_passed']
    profiles=W.Q.aggregate(leaves) if complete else None
    passed=resources and profiles is not None and any(p['both_geometries_passed'] for p in profiles)
    W.P.need(row['measurement_packet_completed'] is complete and row['all_numeric_passed'] is allnumeric
        and row['resource_feasible'] is resources and row['profile_results']==profiles and row['passed'] is passed,
        'Conditioning complete factorial/resource/profile/work state differs')
    return complete,resources,profiles,passed


def readback(inputs,digest,runtime,directory,resource,proposal_path,root_go):
    plan=W.verify(inputs,digest);proposal=json.loads(C.regular(proposal_path).read_text());W.P.need(directory.name==W.OUTPUT
        and proposal==W.proposal(inputs,digest,runtime,directory.parent,False),'Exact conditioning command/output differs')
    report=json.loads(C.regular(directory/'report.json').read_text());jobs=report['jobs'];W.P.need(report['schema']=='pinwheel.model24-fullstack-conditioning-execution.v1'
        and report['plan_sha256']==digest and report['policy']==W.policy() and report['model_qualified'] is False
        and report['qualified_timing'] is False and report['inputs_sources_runtime_unchanged'] is True and W.E.tree(runtime)==plan['runtime']
        and len(jobs)<=8 and [r['index'] for r in jobs]==list(range(len(jobs)))
        and {p.name for p in directory.iterdir()}=={'report.json'}|{'job-'+str(i).zfill(3) for i in range(len(jobs))},'Conditioning output/source/runtime/prefix scope differs')
    leaves=[]
    for index,record in enumerate(jobs):
        row=read_leaf(inputs,digest,plan,plan['jobs'][index],directory/('job-'+str(index).zfill(3)))
        W.P.need(all(record[k]==row[k] for k in ('index','case','branch','numeric_passed','resource_feasible','report_sha256')),'Conditioning exact leaf join differs')
        W.P.need(index==len(jobs)-1 or row['resource_feasible'],'Conditioning suffix after resource failure forbidden');leaves.append(row)
    complete,resources,profiles,passed=work_state(report,leaves);_,parent=W.parent_smoke(inputs/'smoke-launcher.json')
    W.P.need(parent==json.loads((inputs/'smoke-authority.json').read_text()),'Historical failed smoke authority changed')
    joined=C.resource_join(resource,proposal_path,proposal,plan,report,root_go)
    return dict(schema='pinwheel.model24-fullstack-conditioning-independent-readback.v1',plan_sha256=digest,
        execution_report_sha256=W.E.sha(directory/'report.json'),measurement_packet_completed=complete,resource_feasible=resources,
        numerical_policy_diagnostic_passed=passed,profile_results=profiles,leaves=leaves,actual_work_seconds=report['actual_work_seconds'],
        stop_further_conditioning_required=complete and profiles is not None and not any(p['both_geometries_passed'] for p in profiles),
        resource_cleanup_join=joined,native_executed_by_readback=False,model_qualified=False,qualified_timing=False,
        mesh_boundary_length_reference_heldout_qualification_passed=False)


def main():
    q=argparse.ArgumentParser(description=__doc__)
    for n in ('inputs','runtime','directory','resource-report','command-proposal','root-go','output'):q.add_argument('--'+n,type=Path,required=True)
    q.add_argument('--plan-sha256',required=True);a=q.parse_args();r=readback(a.inputs,a.plan_sha256,a.runtime,a.directory,a.resource_report,a.command_proposal,a.root_go);W.write(a.output,r)
    print(json.dumps(dict(numerical_policy_diagnostic_passed=r['numerical_policy_diagnostic_passed'],model_qualified=False)))
    return 0 if r['numerical_policy_diagnostic_passed'] else 2
if __name__=='__main__':raise SystemExit(main())
