"""Independent HOST geometry/R/terminal/resource reopener; no Native or fit."""
import argparse
import json
import math
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import streaming_8x4_model24_r_endpoint as W
import streaming_8x4_model24_custody as C


def read_leaf(inputs,digest,plan,corner,owner):
    path=C.regular(owner/'report.json');row=json.loads(path.read_text());need=W.P.need
    need(row['schema']=='pinwheel.model24-r-endpoint-leaf.v1' and row['plan_sha256']==digest and row['corner']==corner
        and row['argv'][1:]==['-no_init','-exit','run.tcl'] and Path(row['argv'][0]).name=='openroad'
        and row['openroad_sha256']==W.OPENROAD_SHA and row['native_executed'] is True and row['process_tree_reaped'] is True
        and row['inputs_sources_unchanged'] is True and row['copied_inputs_unchanged'] is True and row['openroad_unchanged'] is True
        and row['model_qualified'] is False and row['qualified_timing'] is False,'Endpoint actual leaf command/source/cleanup/scope differs')
    env=row['environment'];need(set(env)=={'PATH','HOME','LANG','LC_ALL','TZ','OMP_NUM_THREADS','OMP_DYNAMIC'} and env['PATH']
        and all(env[k]==v for k,v in dict(HOME='/tmp',LANG='C',LC_ALL='C',TZ='UTC',OMP_NUM_THREADS='1',OMP_DYNAMIC='FALSE').items()),'Endpoint actual environment differs')
    cg=row['cgroups'];cpu=cg['cpu_max'].split();need(len(cpu)==2 and all(v.isdigit() for v in cpu) and 0<int(cpu[0])<=int(cpu[1])
        and cg['memory_max']=='2147483648' and cg['memory_swap_max']=='0' and cg['pids_max']=='128','Endpoint actual resources differ')
    need(W.owned_inventory(owner)==row['output_inventory'] and W.E.sha(C.regular(owner/'native.log'))==row['native_log_sha256'],'Endpoint complete actual output inventory differs')
    for dst,src in W.copied(inputs,corner).items():need((owner/dst).read_bytes()==(inputs/src).read_bytes(),'Endpoint exact selected copied input differs')
    duration=row['actual_work_seconds'];need(type(duration) in (int,float) and math.isfinite(duration) and duration>=0
        and row['work_budget_passed'] is (duration<=40),'Endpoint measured leaf closeout budget differs')
    feasible=W.S.N.resource_observation(row) and row['work_budget_passed'] and sum(r['bytes'] for r in row['output_inventory'].values())<=W.policy()['maximum_output_bytes']
    analysis=None;failure=None
    try:
        need(row['exit_code']==0 and not row['timed_out'] and not row['memory_guard_triggered'] and not row['output_guard_triggered'],'Endpoint native resource/exit failed')
        analysis=W.parse_leaf(owner,plan['corner_sheet_R'][corner])
    except (ValueError,OSError) as e:failure=type(e).__name__+': '+str(e)
    passed=failure is None and feasible and analysis['ideal_endface_controls_passed']
    need(row['analysis']==analysis and row['measurement_completed'] is (failure is None) and row['resource_feasible'] is feasible
        and row['passed'] is passed and (failure is None or row['error']==failure),'Endpoint independent raw/reference/failure/resource verdict differs')
    return dict(corner=corner,passed=passed,resource_feasible=feasible,measurement_completed=failure is None,
        report_sha256=W.E.sha(path),analysis=analysis,error=failure,actual_leaf=row)


def packet_state(report,rows):
    duration=report['actual_work_seconds'];W.P.need(type(duration) in (int,float) and math.isfinite(duration) and duration>=0
        and report['work_budget_passed'] is (duration<=120),'Endpoint measured whole-work budget differs')
    complete=len(rows)==3 and all(r['measurement_completed'] for r in rows)
    passed=complete and all(r['passed'] for r in rows) and report['work_budget_passed']
    W.P.need(report['measurement_packet_completed'] is complete and report['passed'] is passed,'Endpoint complete packet/reference verdict differs')
    return complete,passed


def checked_input_seals(inputs,plan,resource):
    required={str((inputs/n).resolve()):r['sha256'] for n,r in plan['files'].items()}
    W.P.need(all(resource['input_sha256'].get(n)==h for n,h in required.items()),'Endpoint complete prepared-input resource seals omitted/differ')
    return len(required)


def readback(inputs,digest,directory,resource,proposal_path,root_go):
    plan=W.verify(inputs,digest);proposal=json.loads(C.regular(proposal_path).read_text())
    W.P.need(directory.name==W.OUTPUT and proposal==W.proposal(inputs,digest,directory.parent,False),'Exact endpoint command/owner differs')
    report=json.loads(C.regular(directory/'report.json').read_text());jobs=report['jobs']
    W.P.need(report['schema']=='pinwheel.model24-r-endpoint-execution.v1' and report['plan_sha256']==digest and report['policy']==W.policy()
        and report['inputs_sources_unchanged'] is True and report['model_qualified'] is False and report['qualified_timing'] is False
        and len(jobs)<=3 and [r['corner'] for r in jobs]==list(W.G.CORNERS[:len(jobs)])
        and {p.name for p in directory.iterdir()}=={'report.json'}|set(W.G.CORNERS[:len(jobs)]),'Endpoint exact output/prefix/source/scope differs')
    rows=[]
    for record in jobs:
        row=read_leaf(inputs,digest,plan,record['corner'],directory/record['corner'])
        W.P.need(all(record[k]==row[k] for k in ('corner','passed','resource_feasible','measurement_completed','report_sha256')),'Endpoint exact leaf join differs');rows.append(row)
        W.P.need(record is jobs[-1] or (row['resource_feasible'] and row['measurement_completed']),'Endpoint suffix after resource/geometry failure forbidden')
    complete,passed=packet_state(report,rows);joined=C.resource_join(resource,proposal_path,proposal,plan,report,root_go)
    checked=checked_input_seals(inputs,plan,json.loads(C.regular(resource).read_text()))
    audits=[a for r in rows if r['analysis'] for a in r['analysis']['absolute_audits']]
    return dict(schema='pinwheel.model24-r-endpoint-independent-readback.v1',plan_sha256=digest,execution_report_sha256=W.E.sha(directory/'report.json'),
        measurement_packet_completed=complete,ideal_uniform_sheet_endface_controls_passed=passed,absolute_controls=len(audits),absolute_failures=sum(not a['passed'] for a in audits),
        jobs=rows,resource_cleanup_join=joined,prepared_input_resource_seals_checked=checked,historical_R26_failures=W.historical(inputs),actual_work_seconds=report['actual_work_seconds'],
        reference_scope=W.policy()['reference'],no_fitted_subtraction=True,native_executed_by_readback=False,
        contact_spreading_and_via_physics_qualified=False,arbitrary_route_R_qualified=False,capacitance_qualified=False,model_qualified=False,qualified_timing=False)


def main():
    q=argparse.ArgumentParser(description=__doc__)
    for n in ('inputs','directory','resource-report','command-proposal','root-go','output'):q.add_argument('--'+n,type=Path,required=True)
    q.add_argument('--plan-sha256',required=True);a=q.parse_args();r=readback(a.inputs,a.plan_sha256,a.directory,a.resource_report,a.command_proposal,a.root_go);W.write(a.output,r)
    print(json.dumps({k:r[k] for k in ('measurement_packet_completed','ideal_uniform_sheet_endface_controls_passed','absolute_controls','absolute_failures','model_qualified')}))
    return 0 if r['ideal_uniform_sheet_endface_controls_passed'] else 2
if __name__=='__main__':raise SystemExit(main())
