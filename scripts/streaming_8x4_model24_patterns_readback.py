"""Independent HOST pattern observation/custody readback; never launches Native."""
import argparse
import json
import math
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_patterns as W


def regular(path):
    W.P.need(path.is_file() and not path.is_symlink(),'Missing or aliased model24 evidence');return path


def resource_join(path,proposal_path,proposal,plan,report,root_go_path):
    r=json.loads(regular(path).read_text());boundary=r['campaign_boundary'];rp=W.R24
    wrapper=W.ROOT/'scripts/streaming_8x4_closure24_resources.py';policy=W.ROOT/'scripts/streaming_8x4_closure24_policy.py'
    guard=W.ROOT/'scripts/streaming_tt_resources.py'
    W.P.need(r['schema']=='pinwheel.streaming-tt-resource-job.v1'
        and r['argv']==proposal['argv'] and r['timeout_seconds']==120
        and r['exit_code']==(0 if report['passed'] else 2)
        and r['status']==('completed' if report['passed'] else 'failed')
        and r['cleanup_confirmed'] is True and r['inputs_unchanged'] is True
        and r['containers_remaining']==r['owned_processes_remaining']==r['cleanup_errors']==[],
        'Model24 pattern exact outer result/argv/cleanup differs')
    W.P.need(boundary['schema']=='pinwheel.streaming-8x4-closure24-resource-boundary.v1'
        and boundary['campaign_id']==rp.CAMPAIGN and boundary['campaign_directory']==str(W.ROOT/'build/campaigns'/rp.CAMPAIGN)
        and boundary['schedule']==rp.SCHEDULE and boundary['campaign_root']==str(W.ROOT)
        and boundary['shared_lease']==rp.shared_lease_paths(W.ROOT)
        and boundary['campaign_kind']=='rc_experiment'
        and boundary['wrapper_path']==str(wrapper) and boundary['wrapper_sha256']==W.E.sha(wrapper)
        and boundary['policy_path']==str(policy) and boundary['policy_sha256']==W.E.sha(policy)
        and boundary['inherited_supervisor_path']==str(guard)
        and boundary['inherited_supervisor_sha256']==r['supervisor_sha256']==W.E.sha(guard)
        and boundary['historical_producer_sha256']==rp.historical_sources(W.ROOT)
        and boundary['acceptance_claim'] is False and boundary['engineering_evidence_verified'] is False,
        'Model24 exact campaign/cutoff/shared-lease/wrapper/source boundary differs')
    seals=r['input_sha256']
    required={str(proposal_path.resolve()):W.E.sha(proposal_path),proposal['plan_path']:proposal['plan_sha256'],
        str(root_go_path.resolve()):W.E.sha(regular(root_go_path)),
        **{str(W.ROOT/'scripts'/n):h for n,h in plan['producer_sha256'].items()}}
    W.P.need(all(seals.get(n)==h for n,h in required.items()),'Pattern actual proposal/plan/RootGO/source seals differ')
    go=json.loads(root_go_path.read_text())
    W.P.need(go['proposal_sha256']==W.E.sha(proposal_path) and go['model_qualified'] is False,
        'Exact pattern Root GO proposal/scope differs')
    return dict(resource_report=dict(path=str(path.resolve()),sha256=W.E.sha(path)),root_go_sha256=W.E.sha(root_go_path),
        campaign_boundary=boundary,cleanup_confirmed=True,inputs_unchanged=True,containers_remaining=[],owned_processes_remaining=[])


def raw_readback(inputs,digest,directory):
    plan=W.verify(inputs,digest);p=regular(directory/'report.json');report=json.loads(p.read_text())
    W.P.need(report['schema']=='pinwheel.model24-pattern-execution.v1' and report['plan_sha256']==digest
        and report['policy']==W.policy() and report['native_executed'] is True
        and report['model_qualified'] is False and report['qualified_timing'] is False
        and report['numeric_solver_executed'] is False and report['inputs_sources_unchanged'] is True
        and report['copied_tcl_unchanged'] is True and report['openroad_unchanged'] is True
        and report['process_tree_reaped'] is True and type(report['exit_code']) is int
        and report['argv'][1:]==['-no_init','-exit','run.tcl'] and Path(report['argv'][0]).is_absolute()
        and W.E.sha(regular(directory/'run.tcl'))==plan['files_sha256']['run.tcl']
        and W.E.sha(regular(directory/'native.log'))==report['native_log_sha256'],
        'Actual pattern execution/source/scope/command/copy identity differs')
    cg=report['cgroups'];cpu=cg['cpu.max'].split()
    W.P.need(len(cpu)==2 and all(v.isdigit() for v in cpu) and 0<int(cpu[0])<=int(cpu[1])
        and cg['memory.max']=='2147483648' and cg['memory.swap.max']=='0' and cg['pids.max']=='128',
        'Pattern actual container CPU/memory/swap/PID limits differ')
    duration=report['actual_work_seconds']
    W.P.need(type(duration) in (int,float) and math.isfinite(duration) and duration>=0
        and report['work_budget_passed'] is (duration<=90),'Pattern observed work budget differs')
    feasible=W.resource_observation(report)
    W.P.need(report['resource_feasible'] is feasible,'Pattern actual resource status differs')
    terminal=inventory=None;failure=None
    try:
        terminal=W.parse_terminal((directory/'native.log').read_text(),report['exit_code'],report['timed_out'])
        inventory=W.output_inventory(directory)
    except (ValueError,OSError) as error:failure=type(error).__name__+': '+str(error)
    W.P.need(report.get('terminal')==terminal and report.get('inventory')==inventory
        and report['passed'] is (failure is None and feasible and report['work_budget_passed'])
        and (failure is None or report['error']==failure),'Independent raw pattern result/failure differs')
    return plan,report,terminal,inventory,failure


def readback(inputs,digest,directory,resource,proposal_path,root_go):
    plan,report,terminal,inventory,failure=raw_readback(inputs,digest,directory)
    proposal=json.loads(regular(proposal_path).read_text())
    W.P.need(directory.name==W.OUTPUT and proposal==W.proposal(inputs,digest,directory.parent,False),
        'Pattern exact command/output owner differs')
    joined=resource_join(resource,proposal_path,proposal,plan,report,root_go)
    return dict(schema='pinwheel.model24-pattern-independent-readback.v1',plan_sha256=digest,
        execution_report_sha256=W.E.sha(directory/'report.json'),pattern_intake_completed=report['passed'],
        terminal=terminal,inventory=inventory,error=failure,resource_cleanup_join=joined,
        actual_work_seconds=report['actual_work_seconds'],native_executed_by_readback=False,
        numeric_solver_executed=False,model_qualified=False,qualified_timing=False,
        expected_physical_case_universe_proven=False,actual_native_pattern_grammar_qualified=False)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for n in ('inputs','directory','resource-report','command-proposal','root-go','output'):p.add_argument('--'+n,type=Path,required=True)
    p.add_argument('--plan-sha256',required=True);a=p.parse_args()
    result=readback(a.inputs,a.plan_sha256,a.directory,a.resource_report,a.command_proposal,a.root_go)
    W.write(a.output,result);print(json.dumps(dict(pattern_intake_completed=result['pattern_intake_completed'],model_qualified=False)))
    return 0 if result['pattern_intake_completed'] else 2


if __name__=='__main__':raise SystemExit(main())
