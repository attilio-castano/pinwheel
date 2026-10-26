"""ONE exact failed module with immutable prefix imports, diagnostic only.

This producer cannot resume a positive proof. Its object is a fresh sibling,
never an import root; every full-M/private/correspondence flag stays false.
"""
import argparse
import hashlib
import json
from pathlib import Path
import signal
import sys
import time

import streaming_8x4_closure24_m_isolation as I
import streaming_8x4_closure24_scope_m as M

ROOT=I.ROOT
OWN=I.DIAGNOSTIC
MODULE='PhysicalCoreAssignment'
OUTPUT='final24-CoreAssignment-memory-diagnostic-01'
FAILED='80f94dac2e5c8413bdf323bcd81adca485d033452ac89fd4eff1f66757c77e45'
JOURNAL='3b12487c693ca8ebde464e12d902e83b260f32b8f0af0c923db7a42e228a0222'
GUARD='ec426afa03bb573a6bf28b8e9b13fe1885930f6098fc0351be2e8cd13b5d604b'
SOURCE='f4f53b3c4a4cbef147e118d3cb288c828da52eadaf84948f433f5e442da0c1c8'
need=I.need
R=I.R


def policy():
    return dict(schema='pinwheel.closure24-CoreAssignment-diagnostic-policy.v1',module=MODULE,maximum_attempts=1,
        leaf_seconds=180,supervisor_seconds=240,aggregate_rss_mib=4096,threads=1,lean_heap_flag='-M4096',
        rederivation_or_complete_M_claim=False,prefix_reuse_scope='Exact failed-module diagnostic only',
        object_may_enter_any_acceptance_import_root=False,final_correspondence_proved=False,physical_acceptance=False)


def context(failed_path,guard_path):
    failed_path=R.regular(failed_path);guard_path=R.regular(guard_path)
    need(R.digest(failed_path)==FAILED and R.digest(guard_path)==GUARD,'Exact failed M memory-stop receipts differ')
    failed=R.read(failed_path);guard=R.read(guard_path);journal=failed_path.parent/'native.jsonl'
    need(R.digest(journal)==JOURNAL,'Exact failed canonical M journal changed')
    events=[json.loads(line,object_pairs_hook=I.PRIOR.F.pairs)for line in journal.read_text().splitlines()]
    need(failed['passed']is False and failed['status']=='failed-or-interrupted' and len(failed['commands'])==1315 and
        failed['required_actual_modules']==3966 and failed['error']=='KeyboardInterrupt: Root termination signal 15' and
        guard['status']=='stopped' and guard['exit_code']==124 and guard['stop_reason']=='ValueError: Owned host process tree exceeded RSS limit' and
        guard['rss_mib']==4096 and guard['cleanup_confirmed']is True and guard['inputs_unchanged']is True and
        guard['owned_processes_remaining']==guard['cleanup_errors']==[],'Old incomplete RSS stop/cleanup changed')
    need(len(events)==2632 and events[-2]['event']=='intent' and events[-1]['event']=='result','Old failure event membership differs')
    attempted=events[-1];intent=events[-2]
    need(attempted['module']==intent['module']==MODULE and attempted['index']==intent['index']==1315 and
        attempted['exit_code']is None and attempted['timed_out']is False and attempted['native_process_group_closed']is True and
        attempted['object_sha256']is None and attempted['timeout_seconds']==180 and attempted['source_sha256_before']==SOURCE and
        all(attempted.get(k)==v for k,v in intent.items()if k!='event'),'Exact interrupted module boundary differs')
    prepared,manifest=M.verify(failed['prepared']['path'],rederive=False)
    need(I.bound(failed['prepared']['path'])==failed['prepared'] and len(manifest['m_rows'])==3966 and
        manifest['m_rows'][1315]['module']==MODULE and R.digest(attempted['source'])==SOURCE,'Failed actual module/source authority differs')
    prefix={};logs={}
    for index,row in enumerate(failed['commands']):
        need(row['index']==index and row['exit_code']==0 and row['timed_out']is False and row['native_process_group_closed']is True and
            row['module']==manifest['m_rows'][index]['module'] and events[2*index+1]==dict(event='result',**row),
            'Old prefix contains an incomplete/reordered raw command')
        for name,pin in ((row['source'],row['source_sha256_before']),(row['log'],row['log_sha256'])):
            need(R.digest(name)==pin,'Old prefix raw source/log changed')
        obj=Path(manifest['m_rows'][index]['target_olean']);need(R.digest(obj)==row['object_sha256'],'Old diagnostic import object changed')
        prefix[str(obj)]=row['object_sha256'];logs[row['log']]=row['log_sha256']
    need(failed['commands'][-1]['module']=='PhysicalCoreNetwork' and
        I.PRIOR.imports(attempted['source'],failed['roots'])==attempted['resolved_imports'] and len(attempted['resolved_imports'])==218,
        'Exact failed-module import resolution changed')
    for stage in manifest['stages']:
        root=Path(stage['out']);expected={name+'.lean'for name in stage['modules']}|{'modules.json'}
        expected|={str(Path(name).relative_to(root))for name in prefix if Path(name).is_relative_to(root)}
        need(not any(p.is_symlink()for p in root.rglob('*')) and {str(p.relative_to(root))for p in root.rglob('*')if p.is_file()}==expected,
            'Old prefix stage membership changed or gained diagnostic objects')
    seals={**guard['input_sha256'],**failed['input_sha256'],**prefix,**logs,
        str(failed_path):FAILED,str(guard_path):GUARD,str(journal):JOURNAL,str(failed_path.parent/(MODULE+'.log')):R.digest(failed_path.parent/(MODULE+'.log'))}
    need(all(R.digest(name)==pin for name,pin in seals.items()),'Exact diagnostic input/prefix/failure seal changed')
    dep=I.PRIOR.D.verify(prepared['source_N']['path']);actual_runtime=I.current_runtime_binding(prepared)
    return dict(failed_report=I.bound(failed_path),resource_report=I.bound(guard_path),failed_journal=I.bound(journal),
        prepared=failed['prepared'],generation_manifest=prepared['generation_manifest'],target=prepared['actual_odb'],
        source_N=prepared['source_N'],foundation_report=dep['foundation_report'],runtime_report=dep['runtime_report'],
        complete_runtime=actual_runtime,
        physical_candidate=prepared['physical_candidate'],source=I.bound(attempted['source']),compiler=I.bound(attempted['argv'][0]),
        roots=failed['roots'],environment=attempted['environment'],original_argv=attempted['argv'],
        resolved_imports=attempted['resolved_imports'],prefix_objects=prefix,input_sha256=seals,
        prior_per_process_RSS_and_birth_unknown=True)


def command(plan):
    result=list(plan['context']['original_argv']);result[result.index('-o')+1]=str(Path(plan['output'])/(MODULE+'.olean'))
    need(result.count('-M4096')==result.count('-j1')==1 and
        str(Path(plan['output']))not in plan['context']['roots'] and
        all(not Path(plan['output']).is_relative_to(root)for root in plan['context']['roots']),
        'Diagnostic resources/output import isolation changed')
    return result


def prepare(failed,guard,output):
    output=I.M.A.C.owned(output,ROOT);need(not output.exists(),'Preserve earlier diagnostic plan')
    row=dict(schema='pinwheel.closure24-CoreAssignment-diagnostic-plan.v1',context=context(failed,guard),policy=policy(),
        output=str(output.parent/OUTPUT),producer=I.sources(),Native_executed=False,Root_GO_required=True,
        complete_M_proved=False,final_correspondence_proved=False,physical_acceptance=False)
    output.mkdir(parents=True);I.PRIOR.save(output/'plan.json',row);verify(output/'plan.json');return row


def verify(path):
    path=R.regular(path);plan=R.read(path);expected=context(plan['context']['failed_report']['path'],plan['context']['resource_report']['path'])
    need(plan['schema']=='pinwheel.closure24-CoreAssignment-diagnostic-plan.v1' and plan['context']==expected and plan['policy']==policy() and
        Path(plan['output'])==path.parent.parent/OUTPUT and plan['producer']==I.sources(commit=plan['producer']['commit']) and
        plan['Native_executed']is False and plan['Root_GO_required']is True and plan['complete_M_proved']is False and
        plan['final_correspondence_proved']is False and plan['physical_acceptance']is False,'Exact diagnostic plan/source/scope differs')
    need({p.name for p in path.parent.iterdir()}=={'plan.json'},'Diagnostic preparation membership differs');command(plan);return plan


def proposal(path):
    plan=verify(path)
    custody=plan['context']
    # The exact plan contains all 7,568 leaf seals, reopened before/after by
    # worker and independent reader. Flattening their paths exceeds Darwin's
    # ARG_MAX. Seal the complete authority roots and plan directly instead.
    roots=[custody[name]for name in ('failed_report','resource_report','failed_journal','prepared','generation_manifest','source','compiler',
        'source_N','foundation_report','runtime_report')]+[custody['complete_runtime']['foundation']['identity_map']]
    interpreter=I.python_identity()
    direct={row['path']:row['sha256']for row in roots}
    direct.update({str(Path(path).resolve()):R.digest(path),interpreter['resolved']:interpreter['sha256'],
        **{str(ROOT/name):pin for name,pin in plan['producer']['sha256'].items()}})
    direct.update(I.CLOCK.historical_sources(ROOT))
    for name in ('scripts/streaming_8x4_closure24_resources.py','tools/hardware-toolchain.json'):
        direct[str(ROOT/name)]=R.digest(ROOT/name)
    return dict(schema='pinwheel.closure24-CoreAssignment-diagnostic-command.v1',plan=I.bound(path),policy=policy(),
        argv=[sys.executable,'-B',str(ROOT/OWN),'run','--plan',str(Path(path).resolve())],
        Native_argv=command(plan),frozen_parent=plan['context']['failed_report'],output=plan['output'],
        input_sha256=direct,all_leaf_input_seals_retained_in_plan=len(custody['input_sha256']),
        complete_leaf_custody_reopened_before_and_after=True,
        Root_GO_required=True,Native_executed=False,complete_M_proved=False,final_correspondence_proved=False,physical_acceptance=False)


def run(path):
    plan=verify(path);I.sources(committed=True,commit=plan['producer']['commit']);output=Path(plan['output']);need(not output.exists(),'Only one fresh diagnostic attempt')
    output.mkdir(parents=True);record,manifest=M.verify(plan['context']['prepared']['path'],rederive=False)
    before=I.runtime(record);started=time.monotonic();report=dict(schema='pinwheel.closure24-CoreAssignment-diagnostic.v1',
        plan=I.bound(path),policy=policy(),measurement_complete=False,module_exit_code=None,
        complete_M_proved=False,separate_private_controls_closed=False,final_correspondence_proved=False,physical_acceptance=False,
        acceptance_prefix_reuse_allowed=False,old_failure_remains_incomplete=True)
    I.PRIOR.save(output/'report.json',report)
    try:
        namespace=dict(vars(I.PRIOR.ORIGINAL),PROCESS=I.PROCESS)
        exec(compile(I.compile_source(),'<diagnostic-observed-canonical-M-compile>','exec'),namespace)
        actual=namespace['compile_one'](plan['context']['compiler']['path'],Path(plan['context']['source']['path']),
            output/(MODULE+'.olean'),output/(MODULE+'.log'),output/'native.jsonl',1315,MODULE,
            plan['context']['environment'],plan['context']['roots'])
        report.update(native=actual,module_exit_code=actual['exit_code'],runtime_before=before,runtime_after=I.runtime(record))
        need(actual['argv']==command(plan) and report['runtime_after']==before and verify(path)==plan,'Diagnostic command/old bytes/runtime changed')
        memory=I.PROCESS.verify(output/'process-memory.jsonl',[(MODULE,command(plan))],require_child_observed=True)
        report.update(measurement_complete=True,process_memory=I.bound(output/'process-memory.jsonl'),memory=memory,
            native_journal=I.bound(output/'native.jsonl'),
            sampled_parent_child_within_limit=memory['observations'][0]['maximum_observed_parent_and_child_rss_kib']<=4096*1024,
            aggregate_resource_acceptance_requires_outer_guard=True)
    except BaseException as error:report['error']=type(error).__name__+': '+str(error);raise
    finally:
        report['seconds']=round(time.monotonic()-started,6);I.PRIOR.save(output/'report.json',report)
    return report


def verify_report(plan_path,report_path):
    plan=verify(plan_path);report=R.read(report_path);actual=report['native'];out=Path(plan['output'])
    need(Path(report_path).resolve()==out/'report.json' and report['schema']=='pinwheel.closure24-CoreAssignment-diagnostic.v1' and
        report['plan']==I.bound(plan_path) and report['policy']==policy() and report['measurement_complete']is True and
        all(report[key]is False for key in ('complete_M_proved','separate_private_controls_closed','final_correspondence_proved','physical_acceptance','acceptance_prefix_reuse_allowed')) and
        report['old_failure_remains_incomplete']is True,'Diagnostic cannot promote incomplete full M')
    need(actual['argv']==command(plan) and actual['module']==MODULE and actual['index']==1315 and actual['timeout_seconds']==180 and
        actual['source_sha256_before']==actual['source_sha256_after']==SOURCE and actual['resolved_imports']==plan['context']['resolved_imports'] and
        actual['environment']==plan['context']['environment'] and actual['native_process_group_closed']is True and
        actual['log_sha256']==R.digest(out/(MODULE+'.log')) and actual['compiler_sha256_before']==actual['compiler_sha256_after']==plan['context']['compiler']['sha256'],
        'Exact diagnostic Native source/import/resource/log boundary differs')
    events=[json.loads(line,object_pairs_hook=I.PRIOR.F.pairs)for line in(out/'native.jsonl').read_text().splitlines()]
    need(len(events)==2 and events[1]==dict(event='result',**actual) and all(actual.get(k)==v for k,v in events[0].items()if k!='event') and
        events[0]['event']=='intent' and report['native_journal']==I.bound(out/'native.jsonl') and
        report['process_memory']==I.bound(out/'process-memory.jsonl') and report['module_exit_code']==actual['exit_code'],
        'Exact diagnostic two-event journal/result differs')
    need(report['memory']==I.PROCESS.verify(out/'process-memory.jsonl',[(MODULE,command(plan))],require_child_observed=True),
        'Diagnostic actual process observations differ')
    need(report['sampled_parent_child_within_limit']==(report['memory']['observations'][0]['maximum_observed_parent_and_child_rss_kib']<=4096*1024) and
        report['aggregate_resource_acceptance_requires_outer_guard']is True,'Diagnostic sampled memory is not whole-guard authority')
    record,_=M.verify(plan['context']['prepared']['path'],rederive=False)
    need(report['runtime_before']==report['runtime_after']==I.current_runtime_binding(record),'Diagnostic runtime differs')
    obj=out/(MODULE+'.olean');need(actual['object_sha256']==(R.digest(obj)if obj.is_file()else None),'Diagnostic object changed')
    return report


def main():
    q=argparse.ArgumentParser(description=__doc__);m=q.add_subparsers(dest='mode',required=True)
    p=m.add_parser('prepare');p.add_argument('--failed-report',type=Path,required=True);p.add_argument('--resource-report',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    for name in ('verify','proposal','run'):
        p=m.add_parser(name);p.add_argument('--plan',type=Path,required=True)
        if name=='proposal':p.add_argument('--output',type=Path,required=True)
    p=m.add_parser('readback');p.add_argument('--plan',type=Path,required=True);p.add_argument('--report',type=Path,required=True)
    a=q.parse_args()
    if a.mode=='prepare':prepare(a.failed_report,a.resource_report,a.output)
    elif a.mode=='verify':verify(a.plan)
    elif a.mode=='proposal':
        need(not a.output.exists(),'Preserve earlier diagnostic proposal');I.PRIOR.save(a.output,proposal(a.plan))
    elif a.mode=='readback':verify_report(a.plan,a.report)
    else:
        previous=signal.getsignal(signal.SIGTERM)
        def interrupted(signum,frame):raise KeyboardInterrupt('Root termination signal '+str(signum))
        signal.signal(signal.SIGTERM,interrupted)
        try:row=run(a.plan)
        finally:signal.signal(signal.SIGTERM,previous)
        return 0 if row['measurement_complete']and row['module_exit_code']==0 else 2
    return 0


if __name__=='__main__':raise SystemExit(main())
