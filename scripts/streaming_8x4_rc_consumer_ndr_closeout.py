"""HOST-only frozen NDR command proposal and separate resource/raw closeout.

No Native tool launches here. The original NDR preparation/readback stay sealed.
Resource cleanup can close while the six-call numeric packet remains failed or
incomplete; those outcomes are saved as separate artifacts without promotion.
"""
import argparse
import copy
import json
from pathlib import Path

import streaming_8x4_rc_consumer_ndr as N
import streaming_8x4_rc_consumer_ndr_readback as R

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'build/campaigns/8x4-20261022-01'
UNIT_PROPOSAL_SHA='921276f011cdd1bde6399786aa3c72fc914b027abe2f383cfd4e2f18deda0ce8'
PLAN_SHA='dd1cad5279255f2f7d793594c0f54d565af2b89a924c9a7701436c406e0f0cb3'
TAG='8x4-rc-consumer-ndr-01'
CONTAINER='pinwheel-'+TAG
OUTPUT='rc-consumer-ndr-01'
HOST_PYTHON='/opt/homebrew/opt/python@3.13/bin/python3.13'


def bound(path):
    path=Path(path).absolute();N.need(path.is_file() and not path.is_symlink(),'Missing/aliased NDR closeout input')
    path=path.resolve()
    return dict(path=str(path),sha256=N.C.P.sha(path))


def proposal(unit_path,inputs,require_fresh=True):
    unit_path=Path(unit_path).resolve();inputs=Path(inputs).resolve()
    N.need(N.C.P.sha(unit_path)==UNIT_PROPOSAL_SHA,'Original frozen unit command proposal changed')
    old=json.loads(unit_path.read_text());plan=N.verify(inputs,PLAN_SHA)
    N.need(old['schema']=='pinwheel.streaming-8x4-rc-consumer-units-command-proposal.v1' and
        old['plan_sha256']==N.BASELINE_SHA and old['timeout_seconds']==300 and old['work_seconds']==210 and
        old['maximum_calls']==6 and old['native_executed'] is False and old['admitted'] is False and
        all(plan['producer_sha256'].get(name)==pin for name,pin in old['producers_sha256'].items()),
        'Original command/policy/producer authority differs')
    command=copy.deepcopy(old['argv']);old_input=Path(old['plan_path']).parent
    replacements={old['container_name']:CONTAINER,
        f'type=bind,src={old_input},dst=/rc-inputs,readonly':f'type=bind,src={inputs},dst=/rc-inputs,readonly',
        '/rc-source/streaming_8x4_rc_consumer_units.py':'/rc-source/streaming_8x4_rc_consumer_ndr.py',
        N.BASELINE_SHA:PLAN_SHA,'/rc-output-parent/rc-consumer-units-01':'/rc-output-parent/'+OUTPUT}
    for before,after in replacements.items():
        N.need(command.count(before)==1,'Ambiguous old command adaptation token');command[command.index(before)]=after
    parent=next(token.split('src=',1)[1].split(',dst=',1)[0] for token in command if 'dst=/rc-output-parent' in token)
    N.need(Path(parent).resolve()==BASE/'rc-native-outputs' and
        'type=bind,src='+str(ROOT/'scripts')+',dst=/rc-source,readonly' in command,
        'Original output/producer mount owner differs')
    if require_fresh:
        N.need(not (Path(parent)/OUTPUT).exists() and not (ROOT/'build/streaming-tt-resources'/TAG).exists(),
            'NDR output/resource owner is not fresh')
    required={str((inputs/'plan.json').resolve()):PLAN_SHA,str(unit_path):UNIT_PROPOSAL_SHA,
        str(Path(__file__).resolve()):N.C.P.sha(__file__)}
    required.update({str(Path(N.__file__).with_name(name).resolve()):value for name,value in plan['producer_sha256'].items()})
    return dict(schema='pinwheel.streaming-8x4-rc-consumer-NDR-command-proposal.v1',
        root_go_required=True,admitted=False,native_executed=False,model_qualified=False,
        derived_from_unit_proposal=bound(unit_path),plan_path=str(inputs/'plan.json'),plan_sha256=PLAN_SHA,
        container_name=CONTAINER,output_directory=str(Path(parent)/OUTPUT),resource_tag=TAG,
        timeout_seconds=300,work_seconds=210,maximum_calls=6,producers_sha256=plan['producer_sha256'],
        HOST_closeout_producer=bound(__file__),input_seals_required=required,argv=command,
        command_delta='Exactly container name/input owner/Native entrypoint/plan hash/output owner; all flags/resources retained',
        resource_cleanup_and_numeric_acceptance_are_separate=True)


def checked_proposal(path):
    path=Path(path).resolve();record=json.loads(path.read_text())
    N.need(record==proposal(record['derived_from_unit_proposal']['path'],Path(record['plan_path']).parent,require_fresh=False),
        'Frozen NDR command proposal differs')
    return record


def launch_reopen(proposal_path,record):
    inputs=Path(record['plan_path']).parent;directory=Path(record['output_directory'])
    resource=ROOT/'build/streaming-tt-resources'/TAG/'report.json'
    resource_argv=[HOST_PYTHON,'-B',str(ROOT/'scripts/streaming_8x4_acceptance_resources.py'),
        '--campaign-root',str(ROOT),'--kind','solver','--tag',TAG,'--timeout-seconds','300',
        '--rss-mib','4096','--container-name',CONTAINER,'--input',str(Path(proposal_path).resolve())]
    for name in record['input_seals_required']:resource_argv+=['--input',name]
    resource_argv+=['--',*record['argv']]
    return dict(schema='pinwheel.streaming-8x4-rc-consumer-NDR-launch-reopen-proposal.v1',
        root_go_required=True,native_executed=False,model_qualified=False,native_command_proposal=bound(proposal_path),
        native_argv=record['argv'],resource_supervisor_argv=resource_argv,required_resource_report=str(resource),
        HOST_closeout_argv=[HOST_PYTHON,'-B',str(Path(__file__).resolve()),'closeout','--proposal',str(Path(proposal_path).resolve()),
            '--resource-report',str(resource),'--resource-output',str(BASE/'rc-consumer-ndr-resource-join-01.json'),
            '--raw-output',str(BASE/'rc-consumer-ndr-independent-raw-readback-01.json'),
            '--output',str(BASE/'rc-consumer-ndr-closeout-01.json')],
        HOST_raw_readback_argv=[HOST_PYTHON,'-B',str(ROOT/'scripts/streaming_8x4_rc_consumer_ndr_readback.py'),
            '--inputs',str(inputs),'--plan-sha256',PLAN_SHA,'--directory',str(directory),
            '--output',str(BASE/'rc-consumer-ndr-independent-raw-readback-01.json')],
        HOST_only_after_actual_terminal_and_Root_signal=True,
        resource_cleanup_does_not_promote_numeric_result=True)


def resource_facts(resource,record,proposal_path,worker=None):
    code=resource.get('exit_code');status=resource.get('status')
    terminal=type(code) is int and ((status=='completed' and code==0) or
        (status=='failed' and code!=0) or (status=='stopped' and code==124))
    N.need(resource.get('schema')=='pinwheel.streaming-tt-resource-job.v1' and terminal and
        resource.get('argv')==record['argv'] and resource.get('timeout_seconds')==300 and
        resource.get('cleanup_confirmed') is True and resource.get('inputs_unchanged') is True and
        resource.get('containers_remaining')==[] and resource.get('owned_processes_remaining')==[] and
        resource.get('cleanup_errors')==[],'Exact NDR resource argv/budget/terminal/cleanup differs')
    required=dict(record['input_seals_required']);required[str(Path(proposal_path).resolve())]=N.C.P.sha(proposal_path)
    N.need(all(resource.get('input_sha256',{}).get(path)==pin==N.C.P.sha(path) for path,pin in required.items()),
        'NDR resource proposal/plan/producer input seal changed or omitted')
    boundary=resource.get('campaign_boundary',{})
    N.need(boundary.get('schema')=='pinwheel.streaming-8x4-resource-boundary.v1' and
        boundary.get('campaign_root')==str(ROOT) and boundary.get('campaign_kind')=='rc_experiment' and
        boundary.get('shared_lease',{}).get('heavy_lock')==str(ROOT/'build/streaming-tt-resources/heavy.lock') and
        boundary.get('wrapper_sha256')==N.C.P.sha(ROOT/'scripts/streaming_8x4_acceptance_resources.py') and
        boundary.get('inherited_supervisor_sha256')==resource.get('supervisor_sha256')==
            N.C.P.sha(ROOT/'scripts/streaming_tt_resources.py'),
        'NDR resource is not the actual campaign/shared-lock supervisor')
    contract=False
    if worker is not None:
        N.need(worker.get('schema')=='pinwheel.streaming-8x4-rc-consumer-DEF-NDR-execution.v1' and
            worker.get('plan_sha256')==PLAN_SHA and type(worker.get('passed')) is bool and
            worker.get('qualified') is False and worker.get('model_qualified') is False,
            'NDR worker receipt scope/plan differs')
        if status in ('completed','failed'):
            N.need(code==(0 if worker['passed'] else 2),'NDR actual worker/resource numeric exit contract differs')
            contract=True
    return dict(schema='pinwheel.streaming-8x4-rc-consumer-NDR-resource-join.v1',qualified=False,model_qualified=False,
        resource_custody_closed=True,actual_status=status,actual_exit_code=code,
        exact_worker_numeric_exit_contract_checked=contract,worker_report_available=worker is not None,
        cleanup_confirmed=True,inputs_unchanged=True,containers_remaining=[],owned_processes_remaining=[],
        numeric_acceptance_claim=False,scope='Resource/process custody only; raw six-call numerical/NDR readback is separate.')


def closeout(proposal_path,resource_path,resource_output,raw_output,output):
    record=checked_proposal(proposal_path);inputs=Path(record['plan_path']).parent;directory=Path(record['output_directory'])
    N.need(all(not path.exists() for path in (resource_output,raw_output,output)),'Preserve previous NDR closeout')
    N.need(Path(resource_path).resolve()==ROOT/'build/streaming-tt-resources'/TAG/'report.json',
        'NDR closeout selects another Root resource owner')
    worker_path=directory/'report.json';worker=json.loads(worker_path.read_text()) if worker_path.is_file() else None
    resource=json.loads(Path(resource_path).read_text());facts=resource_facts(resource,record,proposal_path,worker)
    facts.update(resource_report=bound(resource_path),command_proposal=bound(proposal_path))
    if worker is not None:facts['worker_report']=bound(worker_path)
    N.write(resource_output,facts)
    try:raw=R.readback(inputs,PLAN_SHA,directory)
    except BaseException as error:
        raw=dict(schema='pinwheel.streaming-8x4-rc-consumer-NDR-raw-readback-failure.v1',qualified=False,model_qualified=False,
            workflow_passed=False,all_six_native_calls_closed=False,error=type(error).__name__+': '+str(error),
            command_proposal=bound(proposal_path),retained_report=None if worker is None else bound(worker_path),
            scope='Failed/incomplete raw readback is preserved; no numeric or model pass.')
    N.write(raw_output,raw)
    result=dict(schema='pinwheel.streaming-8x4-rc-consumer-NDR-closeout.v1',qualified=False,model_qualified=False,
        native_executed_by_closeout=False,resource_join=bound(resource_output),raw_readback=bound(raw_output),
        resource_custody_closed=True,all_six_native_calls_closed=raw.get('all_six_native_calls_closed') is True,
        numeric_passed=raw.get('workflow_passed') is True,
        scope='Actual raw R/NDR outcomes and independent Root resource closeout; no model qualification.')
    N.write(output,result);return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    p=sub.add_parser('proposal')
    for name in ('unit-proposal','inputs','output','launch-reopen'):p.add_argument('--'+name,type=Path,required=True)
    p=sub.add_parser('closeout')
    for name in ('proposal','resource-report','resource-output','raw-output','output'):p.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args()
    if args.mode=='proposal':
        value=proposal(args.unit_proposal,args.inputs);N.write(args.output,value)
        N.write(args.launch_reopen,launch_reopen(args.output,value))
    else:value=closeout(args.proposal,args.resource_report,args.resource_output,args.raw_output,args.output)
    print(json.dumps(value,indent=2))


if __name__=='__main__':main()
