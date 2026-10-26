"""HOST-only synthetic matrix/import/consumer raw and resource readback."""
import argparse
import json
import math
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_diagonal_import as W
import streaming_8x4_model24_custody as C


def cgroup_contract(cg):
    W.P.need(type(cg) is dict and set(cg)=={'cpu.max','memory.max','memory.swap.max','pids.max'},'Exact actual producer dotted kernel-key schema required')
    cpu=cg['cpu.max'].split();W.P.need(len(cpu)==2 and all(v.isdigit() for v in cpu) and 0<int(cpu[0])<=int(cpu[1])
        and cg['memory.max']=='2147483648' and cg['memory.swap.max']=='0' and cg['pids.max']=='128','Synthetic actual cgroup bounds differ')
    return True


def read_leaf(inputs,digest,plan,mode,owner):
    path=C.regular(owner/'report.json');row=json.loads(path.read_text())
    W.P.need(row['schema']=='pinwheel.model24-synthetic-diagonal-leaf.v1' and row['plan_sha256']==digest and row['mode']==mode
        and row['argv'][1:]==['-no_init','-exit','run.tcl'] and Path(row['argv'][0]).name=='openroad'
        and row['openroad_sha256']==W.OPENROAD_SHA and row['openroad_unchanged'] is True and row['inputs_sources_unchanged'] is True
        and row['copied_inputs_unchanged'] is True and row['native_executed'] is True and row['model_qualified'] is False
        and row['qualified_timing'] is False and row['process_tree_reaped'] is True,'Synthetic exact leaf scope/custody/command differs')
    env=row['environment'];W.P.need(set(env)=={'PATH','HOME','LANG','LC_ALL','TZ','OMP_NUM_THREADS','OMP_DYNAMIC'} and env['PATH']
        and all(env[k]==v for k,v in dict(HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE').items()),'Synthetic actual environment differs')
    cgroup_contract(row['cgroups'])
    W.P.need(W.owned_inventory(owner)==row['output_inventory'] and W.E.sha(C.regular(owner/'native.log'))==row['native_log_sha256'],'Synthetic full raw output inventory differs')
    for n in ('tech.lef','fixture.def','run.tcl'):W.P.need((owner/n).read_bytes()==(inputs/n).read_bytes(),'Synthetic exact copied input differs')
    W.P.need((owner/'synthetic.caps').read_bytes()==(inputs/(mode+'.caps')).read_bytes(),'Synthetic exact projected importer input differs')
    seconds=row['actual_work_seconds'];W.P.need(type(seconds) in (int,float) and math.isfinite(seconds) and 0<=seconds<45 and row['work_budget_passed'] is (seconds<=40),'Synthetic terminal leaf clock differs')
    feasible=W.S.N.resource_observation(row) and row['work_budget_passed'] and sum(r['bytes'] for r in row['output_inventory'].values())<=W.D.policy()['maximum_output_bytes'];numeric=None;failure=None
    try:
        W.P.need(row['exit_code']==0 and not row['timed_out'] and not row['memory_guard_triggered'] and not row['output_guard_triggered'],'Synthetic actual native resource/exit failed')
        numeric=W.parse_leaf(owner,mode)
    except (ValueError,OSError) as e:failure=type(e).__name__+': '+str(e)
    W.P.need(row['numeric']==numeric and row['control_passed'] is (failure is None) and row['resource_feasible'] is feasible
        and row['passed'] is (failure is None and feasible) and (failure is None or row['error']==failure),'Synthetic independent raw numeric/failure/resource differs')
    return dict(mode=mode,passed=row['passed'],resource_feasible=feasible,numeric=numeric,error=failure,report_sha256=W.E.sha(path),actual_leaf=row)


def packet_state(report,rows,delta):
    duration=report['actual_work_seconds'];W.P.need(type(duration) in (int,float) and math.isfinite(duration) and duration>=0 and report['work_budget_passed'] is (duration<=90),'Synthetic measured full work clock differs')
    complete=len(rows)==2;passed=complete and all(r['passed'] for r in rows) and report['work_budget_passed'] and delta is not None
    W.P.need(report['measurement_packet_completed'] is complete and report['deck_delta']==delta and report['passed'] is passed,'Synthetic independent complete packet/deck-delta verdict differs')
    return complete,passed


def readback(inputs,digest,directory,resource,proposal_path,root_go):
    plan=W.verify(inputs,digest);proposal=json.loads(C.regular(proposal_path).read_text());W.P.need(directory.name==W.OUTPUT and proposal==W.proposal(inputs,digest,directory.parent,False),'Exact synthetic command/output differs')
    report=json.loads(C.regular(directory/'report.json').read_text());jobs=report['jobs'];W.P.need(report['schema']=='pinwheel.model24-synthetic-diagonal-execution.v1' and report['plan_sha256']==digest and report['policy']==W.D.policy()
        and report['inputs_sources_unchanged'] is True and report['model_qualified'] is False and report['qualified_timing'] is False
        and len(jobs)<=2 and [r['mode'] for r in jobs]==list(W.D.MODES[:len(jobs)])
        and {p.name for p in directory.iterdir()}=={'report.json'}|set(W.D.MODES[:len(jobs)]),'Synthetic exact source/output/prefix/claim differs')
    rows=[]
    for record in jobs:
        row=read_leaf(inputs,digest,plan,record['mode'],directory/record['mode']);W.P.need(all(record[k]==row[k] for k in ('mode','passed','resource_feasible','report_sha256')),'Synthetic exact leaf join differs');rows.append(row)
        W.P.need(record is jobs[-1] or row['resource_feasible'],'Synthetic suffix after resource failure forbidden')
    complete=len(rows)==2;delta=None;failure=None
    if complete and all(r['passed'] for r in rows):
        try:delta=W.D.compare_decks((directory/W.D.MODES[0]/'imported.rules').read_text(),(directory/W.D.MODES[1]/'imported.rules').read_text())
        except ValueError as e:failure=type(e).__name__+': '+str(e)
    duration=report['actual_work_seconds'];complete,passed=packet_state(report,rows,delta)
    W.P.need(failure is None or report['error']==failure,'Synthetic independent failed deck-delta reason differs')
    _,parent,h=W.S.parent_pattern(inputs/'pattern-launcher.json');W.P.need(h==plan['pattern_authority_sha256'] and parent==json.loads((inputs/'pattern-authority.json').read_text()),'Historical actual pattern/source closure differs')
    joined=C.resource_join(resource,proposal_path,proposal,plan,report,root_go)
    return dict(schema='pinwheel.model24-synthetic-diagonal-independent-readback.v1',plan_sha256=digest,execution_report_sha256=W.E.sha(directory/'report.json'),
        measurement_packet_completed=complete,synthetic_projection_import_consumer_controls_passed=passed,jobs=rows,deck_delta=delta,
        actual_work_seconds=duration,resource_cleanup_join=joined,old_factor_two_prediction_failure_preserved=True,
        native_executed_by_readback=False,physical_accuracy='unmeasured',coefficient_fitted=False,model_qualified=False,qualified_timing=False)


def main():
    q=argparse.ArgumentParser(description=__doc__)
    for n in ('inputs','directory','resource-report','command-proposal','root-go','output'):q.add_argument('--'+n,type=Path,required=True)
    q.add_argument('--plan-sha256',required=True);a=q.parse_args();r=readback(a.inputs,a.plan_sha256,a.directory,a.resource_report,a.command_proposal,a.root_go);W.write(a.output,r)
    print(json.dumps(dict(synthetic_projection_import_consumer_controls_passed=r['synthetic_projection_import_consumer_controls_passed'],model_qualified=False)))
    return 0 if r['synthetic_projection_import_consumer_controls_passed'] else 2
if __name__=='__main__':raise SystemExit(main())
