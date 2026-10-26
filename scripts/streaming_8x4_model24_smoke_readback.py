"""Independent HOST raw six-conductor cost representatives; never Native."""
import argparse
import json
import math
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_smoke as W
import streaming_8x4_model24_custody as C


def read_leaf(inputs,digest,plan,index,directory):
    p=C.regular(directory/'report.json');row=json.loads(p.read_text());case=plan['cases'][index]
    W.P.need(row['schema']=='pinwheel.model24-fullstack-smoke-leaf.v1' and row['plan_sha256']==digest and row['index']==index
        and row['native_path']==case['native_path'] and row['argv']==W.K.solver_argv() and row['environment']==W.I.W.C.ENVIRONMENT
        and row['model_qualified'] is False and row['qualified_timing'] is False and row['native_executed'] is True
        and row['process_tree_reaped'] is True and row['inputs_sources_unchanged'] is True
        and row['runtime_unchanged'] is True and row['copied_inputs_unchanged'] is True,
        'Exact representative raw scope/role/source/command differs')
    source=inputs/('case-'+str(index).zfill(3))/'geometry'
    W.P.need({p.name for p in directory.iterdir()}=={'report.json','native.log','work'}
        and W.E.tree(directory/'work')==W.E.tree(source)
        and W.E.sha(C.regular(directory/'native.log'))==row['native_log_sha256'],'Actual copied representative/log differs')
    cg=row['cgroups'];cpu=cg['cpu_max'].split()
    W.P.need(len(cpu)==2 and all(v.isdigit() for v in cpu) and 0<int(cpu[0])<=int(cpu[1])
        and cg['memory_max']=='6442450944' and cg['memory_swap_max']=='0' and cg['pids_max']=='128',
        'Representative actual cgroup CPU/memory/swap/PID envelope differs')
    changes=W.I.counters(row['cgroup_before'],row['cgroup_after'])
    W.P.need(row['cgroup_counter_deltas']==changes and type(row['maximum_polled_memory_current']) is int
        and row['cgroup_before']['memory_current']<=row['maximum_polled_memory_current']<=row['cgroup_after']['memory_peak'],
        'Representative actual cumulative cgroup/polled peak differs')
    for snapshot in (row['cgroup_before'],row['cgroup_after']):W.P.need(snapshot['memory_max']==6442450944 and snapshot['memory_swap_max']==0,'Representative memory/swap differs')
    W.P.need(type(row['wall_seconds']) in (int,float) and math.isfinite(row['wall_seconds']) and 0<=row['wall_seconds']<130,
        'Representative observed leaf closeout clock differs')
    raw=(directory/'native.log').read_text();numeric=None;failure=None
    try:numeric=W.K.parse_terminal(raw,case['ordered_conductor_roles'],row['exit_code'],row['timed_out'],row['memory_guard_triggered'])
    except (ValueError,OSError) as error:failure=type(error).__name__+': '+str(error)
    actual_bytes=sum(p.stat().st_size for p in directory.rglob('*') if p.is_file() and not p.is_symlink() and p.name!='report.json')
    W.P.need(row['actual_output_bytes']==actual_bytes,'Representative actual terminal output bytes differ')
    feasible=W.I.resource_feasible(row) and row['process_tree_reaped'] and row['output_guard_triggered'] is False and actual_bytes<=W.policy()['maximum_output_bytes']
    W.P.need(row['numeric']==numeric and row['numeric_passed'] is (failure is None)
        and row['resource_feasible'] is feasible and row['actual_f0_observed'] is W.I.mode_observed(raw)
        and row['passed'] is (failure is None and feasible)
        and (failure is None or row['error']==failure),'Independent representative numeric/resource/failure differs')
    return dict(index=index,native_path=case['native_path'],numeric=numeric,numeric_passed=row['numeric_passed'],
        resource_feasible=feasible,error=failure,report_sha256=W.E.sha(p),actual_leaf=row)


def work_state(row,leaves):
    duration=row['actual_work_seconds']
    W.P.need(type(duration) in (int,float) and math.isfinite(duration) and duration>=0
        and row['work_budget_passed'] is (duration<=270),'Representative observed work clock/flag differs')
    complete=len(leaves)==2;numeric=complete and all(r['numeric_passed'] for r in leaves)
    resources=complete and all(r['resource_feasible'] for r in leaves) and row['work_budget_passed']
    W.P.need(row['measurement_packet_completed'] is complete and row['all_numeric_passed'] is numeric
        and row['resource_feasible'] is resources and row['passed'] is (numeric and resources),
        'Representative complete numeric/resource/work state differs')
    return complete,numeric,resources


def readback(inputs,digest,runtime,directory,resource,proposal_path,root_go):
    plan=W.verify(inputs,digest);proposal=json.loads(C.regular(proposal_path).read_text())
    W.P.need(directory.name==W.OUTPUT and proposal==W.proposal(inputs,digest,runtime,directory.parent,False),
        'Exact representative command/output differs')
    report=json.loads(C.regular(directory/'report.json').read_text());jobs=report['jobs']
    W.P.need(report['schema']=='pinwheel.model24-fullstack-smoke-execution.v1' and report['plan_sha256']==digest
        and report['policy']==W.policy() and report['model_qualified'] is False and report['qualified_timing'] is False
        and report['inputs_sources_runtime_unchanged'] is True and W.E.tree(runtime)==plan['runtime']
        and len(jobs)<=2 and [r['index'] for r in jobs]==list(range(len(jobs)))
        and {p.name for p in directory.iterdir()}=={'report.json'}|{'job-'+str(i).zfill(3) for i in range(len(jobs))},
        'Representative actual source/runtime/membership/scope differs')
    leaves=[]
    for index,record in enumerate(jobs):
        row=read_leaf(inputs,digest,plan,index,directory/('job-'+str(index).zfill(3)))
        W.P.need(all(record[k]==row[k] for k in ('index','native_path','numeric_passed','resource_feasible','report_sha256')),
            'Representative actual leaf/packet join differs')
        W.P.need(index==len(jobs)-1 or row['resource_feasible'],'Suffix after resource failure forbidden');leaves.append(row)
    complete,numeric,resources=work_state(report,leaves)
    _,parent,phash=W.parent_pattern(inputs/'pattern-launcher.json')
    W.P.need(phash==plan['pattern_authority_sha256'] and parent==json.loads((inputs/'pattern-authority.json').read_text()),
        'Historical full Native pattern source/custody observation changed')
    joined=C.resource_join(resource,proposal_path,proposal,plan,report,root_go)
    return dict(schema='pinwheel.model24-fullstack-smoke-independent-readback.v1',plan_sha256=digest,
        execution_report_sha256=W.E.sha(directory/'report.json'),measurement_packet_completed=complete,
        all_numeric_passed=numeric,resource_feasible=resources,smoke_passed=report['passed'],leaves=leaves,
        actual_work_seconds=report['actual_work_seconds'],resource_cleanup_join=joined,native_executed_by_readback=False,
        model_qualified=False,qualified_timing=False,mesh_boundary_length_reference_heldout_qualification_passed=False,
        scope='two fixed development representatives; complete raw matrices/full-stack/roles/units and runtime only')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for n in ('inputs','runtime','directory','resource-report','command-proposal','root-go','output'):p.add_argument('--'+n,type=Path,required=True)
    p.add_argument('--plan-sha256',required=True);a=p.parse_args()
    row=readback(a.inputs,a.plan_sha256,a.runtime,a.directory,a.resource_report,a.command_proposal,a.root_go)
    W.write(a.output,row);print(json.dumps(dict(smoke_passed=row['smoke_passed'],model_qualified=False)))
    return 0 if row['smoke_passed'] else 2


if __name__=='__main__':raise SystemExit(main())
