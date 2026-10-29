"""HOST source/count/raw/cgroup/scratch reopener for the two-stage OOC study."""
import argparse
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_rc_ooc as X
P,E,W=X.P,X.E,X.W


def validate_snapshot(row):
    P.need(all(type(row[k])is int and row[k]>=0 for k in ('memory_current','memory_peak','memory_max','memory_swap_max'))
        and 0<row['memory_max']<=6442450944 and row['memory_swap_max']==0
        and row['memory_peak']>=row['memory_current']
        and all({'max','oom','oom_kill'}<=set(row[k]) for k in ('memory_events','memory_events_local'))
        and all(type(v)is int and v>=0 for k in ('memory_events','memory_events_local') for v in row[k].values()),
        'OOC actual mandatory cgroup observations differ')


def validate_cleanup(row):
    clean=row['scratch_cleanup'];P.need(clean['after']==[] and clean['only_exact_owned_regular_scratch_removed'] is True,
        'OOC scratch was not reaped/cleaned')
    before=clean['before'];P.need(len({r['name'] for r in before})==len(before),'Duplicate scratch cleanup inventory')
    for item in before:
        P.need(X.re.fullmatch(r'frc[lp][0-9A-F]+\.tmp',item['name'])
            and all(type(item[k])is int and item[k]>=0 for k in ('device','inode','bytes','allocated_bytes','mode','uid'))
            and item['content_hashed'] is False and item['ephemeral_not_numerical_authority'] is True,
            'OOC cleanup contains unowned/nonregular/unsupported entry')
    measure=X.scratch_measure(before)
    P.need(row['maximum_scratch_logical_bytes']>=measure['logical_bytes']
        and row['maximum_scratch_allocated_bytes']>=measure['allocated_bytes']
        and row['maximum_scratch_files']>=measure['files'],'OOC scratch peak below retained terminal inventory')


def leaf(inputs,digest,plan,stage,owner):
    row=json.loads((owner/'report.json').read_text());raw=(owner/'native.log').read_text()
    P.need(row['schema']=='pinwheel.streaming-8x4-rc-ooc-leaf.v1' and row['plan_sha256']==digest and row['stage']==stage
        and row['argv']==X.solver_argv(plan,stage) and row['environment']==X.environment(stage) and row['timeout_seconds']==120
        and all(row[k]is False for k in ('qualified','model_qualified','full_pilot_passed','qualified_timing'))
        and row['log_sha256']==E.sha(owner/'native.log') and row['meminfo_sha256']==E.sha(owner/'meminfo.txt')
        and E.tree(owner/'work')==plan['case']['files'] and row['inputs_runtime_unchanged'] is True
        and {p.name for p in owner.iterdir()}=={'report.json','native.log','meminfo.txt','work'},'OOC actual leaf/source/raw/input authority differs')
    for key in ('cgroup_before','cgroup_after'):validate_snapshot(row[key])
    validate_cleanup(row);feasible=X.resource_pass(row)
    if stage=='solve':feasible &= row['observed_temp_prefixes']==['frcl','frcp'] and row['maximum_scratch_logical_bytes']>0
    P.need(row['resource_feasible'] is feasible,'OOC independent resource assessment differs')
    cg=row['cgroups'];cpu=cg['cpu_max'].split()
    P.need(cg['memory_max']==str(row['cgroup_before']['memory_max']) and cg['memory_swap_max']=='0'
        and len(cpu)==2 and all(x.isdigit() for x in cpu) and 0<int(cpu[0])<=int(cpu[1])
        and cg['pids_max'].isdigit() and 0<int(cg['pids_max'])<=128,'OOC actual CPU/PID/cgroup policy differs')
    count=None;numeric=None;expected=False;passed=False;error=None
    try:
        if stage=='count97':
            P.need(row['exit_code']==97,'Count probe expected97 exit missing');count=X.parse_count(raw);expected=True
        else:
            P.need(row['exit_code']==0,'OOC solve exit failure');X.header(raw,'5')
            P.need(X.re.findall(r"^Out-of-core temporary files folder: '([^']+)'$",raw,X.re.M)==['/ooc-scratch/solve'],
                'OOC actual temp path/fallback differs')
            count=X.counts(raw);numeric=X.I.X.parse(raw,dict(policy=plan['original_solver_policy']),plan['case'],X.MESH);passed=True
    except (ValueError,KeyError,TypeError) as failure:error=type(failure).__name__+': '+str(failure)
    P.need(row['counts']==count and row['numeric']==numeric and row['expected_count97_observed'] is expected
        and row['numerical_passed'] is passed and (error is None or row['error']==error),
        'OOC independently parsed count/numeric/expected-error result differs')
    return row


def resource_join(resource_path,proposal_path,proposal,plan,report):
    result=X.I.F.resource_join(resource_path,proposal_path,proposal,plan,report)
    resource=json.loads(resource_path.read_text());boundary=resource['campaign_boundary']
    P.need(boundary['shared_lease']==dict(heavy_lock=str(X.ROOT/'build/streaming-tt-resources/heavy.lock'),
        cleanup_sentinel=str(X.ROOT/'build/streaming-tt-resources/cleanup-unconfirmed.json')),
        'OOC exact shared lease/sentinel differs')
    owner=Path(plan['scratch_host_path'])/'owner.json'
    P.need(resource['input_sha256'][str(owner)]==proposal['scratch_owner_sha256']==E.sha(owner),
        'OOC scratch owner resource seal differs')
    return result


def readback(inputs,digest,directory,runtime,resource_path,proposal_path):
    plan=X.verify(inputs,digest);proposal=json.loads(proposal_path.read_text())
    P.need(proposal==X.proposal(inputs,digest,runtime,directory.parent,require_fresh=False) and directory.name==X.OUTPUT,
        'OOC exact Docker/source/runtime/scratch dispatch differs')
    report=json.loads((directory/'report.json').read_text());jobs=report['jobs'];stages=X.policy()['stages']
    P.need(report['schema']=='pinwheel.streaming-8x4-rc-ooc-execution.v1' and report['plan_sha256']==digest
        and report['policy']==X.policy() and all(report[k]is False for k in ('qualified','model_qualified','full_pilot_passed','qualified_timing'))
        and report['inputs_runtime_unchanged'] is True and len(jobs)<=2
        and [j['stage'] for j in jobs]==stages[:len(jobs)],'OOC complete/prefix policy/membership differs')
    rows=[]
    for job in jobs:
        owner=directory/job['stage'];P.need(E.sha(owner/'report.json')==job['report_sha256'],'OOC raw leaf seal differs')
        rows.append(leaf(inputs,digest,plan,job['stage'],owner))
    projection=None
    if rows and rows[0]['resource_feasible'] and rows[0]['expected_count97_observed']:
        P.need(rows[0]['scratch_cleanup']['before']==[],'Count97 created unexpected chunks')
        if (directory/'solve-admission-meminfo.txt').exists():
            total=X.memtotal((directory/'solve-admission-meminfo.txt').read_text())
            P.need(total==X.memtotal((directory/'count97/meminfo.txt').read_text()),'OOC whole VM bound changed')
            projection=X.projection(rows[0]['counts'],total,rows[0]['cgroup_after']['memory_peak'])
    P.need(report['projection']==projection,'OOC source-sized whole-VM projection differs')
    if len(rows)==2:
        P.need(report['solve_counts_match_probe'] is (rows[1]['counts']==rows[0]['counts']),'OOC stored count comparison differs')
        P.need(projection is not None and projection['admitted'] and X.memtotal((directory/'solve/meminfo.txt').read_text())==projection['whole_VM_MemTotal_bytes'],
            'OOC solve without predeclared count-derived memory/scratch admission')
    complete=len(rows)==2 and all(r['process_tree_reaped'] for r in rows)
    work=report['work_wall_seconds'];P.need(type(work)in(int,float) and X.math.isfinite(work) and work>=0
        and report['wall_seconds']==work and report['work_budget_satisfied'] is (work<=270),'OOC actual complete work budget differs')
    feasible=complete and all(r['resource_feasible'] for r in rows) and report['work_budget_satisfied']
    numerical=complete and rows[1]['numerical_passed'] and rows[1]['counts']==rows[0]['counts']
    P.need(report['measurement_packet_completed'] is complete and report['resource_feasible'] is feasible
        and report['numerical_passed'] is numerical and report['passed'] is (feasible and numerical),
        'OOC count/resource/numeric/measurement aggregate differs')
    resource=resource_join(resource_path,proposal_path,proposal,plan,report)
    root=Path(plan['scratch_host_path']);X.verify_owner(root,plan,digest)
    P.need(report['scratch_terminal_entries']==sorted(p.name for p in root.iterdir())
        and report['scratch_stage_directories_empty'] is True and all(not list(p.iterdir()) for p in root.iterdir() if p.is_dir()),
        'OOC actual owned scratch residue remains')
    allowed={'report.json'}|set(stages[:len(rows)])
    if projection is not None:allowed.add('solve-admission-meminfo.txt')
    P.need({p.name for p in directory.iterdir()}==allowed,'OOC exact output inventory differs')
    X.verify(inputs,digest);P.need(E.tree(runtime)==plan['runtime'],'OOC runtime changed during HOST readback')
    return dict(schema='pinwheel.streaming-8x4-rc-ooc-independent-readback.v1',qualified=False,model_qualified=False,
        full_pilot_passed=False,qualified_timing=False,measurement_packet_completed=complete,
        resource_feasible=feasible,numerical_passed=numerical,point_passed=feasible and numerical and resource['status']=='completed',
        plan_sha256=digest,execution_report_sha256=E.sha(directory/'report.json'),resource_cleanup_join=resource,
        projection=projection,leaves=rows,native_executed_by_readback=False,scope=X.policy()['scope'])


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for n in ('inputs','directory','runtime','resource-report','command-proposal','output'):p.add_argument('--'+n,type=Path,required=True)
    p.add_argument('--plan-sha256',required=True);a=p.parse_args()
    row=readback(a.inputs,a.plan_sha256,a.directory,a.runtime,a.resource_report,a.command_proposal);W.write(a.output,row)
    print(json.dumps({k:row[k] for k in ('measurement_packet_completed','resource_feasible','numerical_passed','point_passed','full_pilot_passed')},indent=2))
    return 0 if row['point_passed'] else 2


if __name__=='__main__':raise SystemExit(main())
