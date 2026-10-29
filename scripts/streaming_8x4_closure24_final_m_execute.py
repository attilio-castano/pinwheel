"""New24 Root-guarded complete actual-M execution and separate private controls.

No prefix/count/stop-at option exists. The positive run rederives the whole
GEN04 plan, compiles every actual module in order, audits every N+M owner, and
freezes the exact target/import/runtime boundary. Its receipt explicitly leaves
the separate two-command private control pending. Root grants each Native GO.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
import streaming_8x4_final_runtime as R
import streaming_8x4_final_dependency as D
import streaming_8x4_closure24_final_m as M
import streaming_8x4_final_m_execute as ORIGINAL
import streaming_tt_fresh_foundation as F
from streaming_mapped_campaign import audit_source

ROOT=Path(__file__).resolve().parents[1]
BAD='PhysicalGRTExactPrivateAxiom'
AUDIT='PhysicalGRTExactPrivateAudit'
REQUIRED='PhysicalGRTFinalRequired'
LONG_MODULES=frozenset(('PhysicalStateCodec','ActualGRTClockDAGProof',
    'PhysicalGRTOriginalProof','PhysicalGRTActualProof','PhysicalGRTFinalAudit',AUDIT))


budget_policy = ORIGINAL.budget_policy


command_timeout = ORIGINAL.command_timeout


verify_command_timeout = ORIGINAL.verify_command_timeout


bound = ORIGINAL.bound


save = ORIGINAL.save


event = ORIGINAL.event


def source_seal():
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True,timeout=30).strip()
    own=Path(__file__).resolve();name=str(own.relative_to(ROOT))
    payload=subprocess.check_output(['git','show',commit+':'+name],cwd=ROOT,timeout=30)
    F.require(hashlib.sha256(payload).hexdigest()==R.digest(own),'Commit actual-M Native controller before execution')
    F.require(not sys.flags.optimize,'Refuse optimized Native actual-M controller')
    shared=Path(ORIGINAL.__file__).resolve();shared_name=str(shared.relative_to(ROOT))
    payload=subprocess.check_output(['git','show',commit+':'+shared_name],cwd=ROOT,timeout=30)
    F.require(hashlib.sha256(payload).hexdigest()==R.digest(shared),'Shared unchanged Native helper differs from committed source')
    F.check_native_environment();return commit,bound(own)


observe_foundation_runtime = ORIGINAL.observe_foundation_runtime


native_argv = ORIGINAL.native_argv


imports = ORIGINAL.imports


verify_imports = ORIGINAL.verify_imports


compile_one = ORIGINAL.compile_one


environment = ORIGINAL.environment


def input_seal(prepared,manifest,record,controller):
    before={**manifest['input_sha256'],**manifest['producer_sha256'],**record['producer_sha256']}
    before.update({str(Path(prepared).resolve()):R.digest(prepared),controller['path']:controller['sha256'],
        str(Path(ORIGINAL.__file__).resolve()):R.digest(ORIGINAL.__file__)})
    for key in ('generation_request','generation_manifest','generator','original_generator','adaptation_diff'):
        before[record[key]['path']]=record[key]['sha256']
    F.require(all(R.digest(path)==pin for path,pin in before.items()),'Complete actual-M frozen input changed')
    return before


runtime_identity = ORIGINAL.runtime_identity


stage_membership = ORIGINAL.stage_membership


artifacts = ORIGINAL.artifacts


def generated_roots_owned(source_n, stages):
    """Old N is immutable reuse; actual M is fresh, with one combined namespace."""
    source_n = Path(source_n); stages = list(map(Path, stages))
    F.generated_paths_owned([source_n], ROOT / 'build/campaigns/8x4-20261022-01')
    F.generated_paths_owned(stages, ROOT / M.A.C.CAMPAIGN)
    # Keep the original cross-root duplicate/shadow rejection after enforcing
    # each tighter owner separately. The common root grants no extra owner.
    F.generated_paths_owned([source_n, *stages], ROOT / 'build/campaigns')


def positive(prepared,output):
    commit,controller=source_seal();output=M.A.C.owned(output,ROOT)
    F.require(not output.exists(),'Preserve prior actual-M Native attempt')
    output.mkdir(parents=True);path=output/'report.json';start=time.monotonic()
    report=dict(schema='pinwheel.closure24-actual-M-positive.v1',passed=False,qualified=False,status='host-admission',
        producer_commit=commit,controller=controller,prepared=bound(prepared),commands=[],separate_private_controls_closed=False,
        native_budget_policy=budget_policy(),
        final_correspondence_proved=False,physical_acceptance=False,started_utc=datetime.now(timezone.utc).isoformat())
    save(path,report)
    try:
        record,manifest=M.verify(prepared,rederive=True);dep=D.verify(record['source_N']['path'])
        f03=D.foundation(dep['foundation_report']['path']);runtime=R.closed_report(dep['runtime_report']['path'])
        full_runtime=observe_foundation_runtime(f03);identity=runtime_identity(runtime)
        before=input_seal(prepared,manifest,record,controller)
        rows=manifest['m_rows'];names=[row['module'] for row in rows]
        F.require(names and len(names)==len(set(names)) and names[-1]=='PhysicalGRTFinalAudit',
            'Complete final-M namespace/full final audit required')
        stage_membership(manifest,completed=False)
        stage_roots=[Path(stage['out']) for stage in manifest['stages']]
        F.require(not any(p.suffix=='.olean' or '.olean.' in p.name for root in stage_roots for p in root.rglob('*')),
            'Fresh actual-M cannot reuse an existing object/prefix')
        lean=f03['tools']['lean'];stdlib=Path(lean).parent.parent/'lib/lean'
        roots=[Path(f03['positive_library']['path']),stdlib,Path(dep['positive_library']['path']),*stage_roots]
        generated_roots_owned(roots[2], roots[3:])
        env=environment(roots,lean);journal=output/'native.jsonl'
        report.update(status='native',required_actual_modules=len(rows),external_source_modules=395,
            target=record['actual_odb'],physical_candidate=record['physical_candidate'],
            full_foundation_runtime_before=full_runtime,tool_identity_before=identity,
            input_sha256=before,roots=list(map(str,roots)),environment=env);save(path,report)
        for index,row in enumerate(rows):
            source=Path(row['source']);obj=Path(row['target_olean']);log=output/(row['module']+'.log')
            F.require(R.digest(source)==row['source_sha256'],'Generated actual-M source changed before use')
            native=compile_one(lean,source,obj,log,journal,index,row['module'],env,roots)
            report['commands'].append(native);save(path,report)
            F.require(type(native['exit_code']) is int and native['exit_code']==0 and native['object_sha256'] is not None,
                'Actual-M module failed; a prefix cannot pass')
        final_log=Path(report['commands'][-1]['log']).read_text()
        F.require(len(re.findall(r'Mapped audit: [1-9][0-9]* declarations, [1-9][0-9]* theorems; standard axioms only\.',final_log))==1,
            'Actual-M complete positive private-declaration audit did not close')
        F.require([row['module'] for row in report['commands']]==names and
            all(R.digest(file)==pin for file,pin in before.items()),'Actual-M complete command/input closeout differs')
        after_runtime=observe_foundation_runtime(f03);after_identity=runtime_identity(runtime)
        F.require(after_runtime==full_runtime and after_identity==identity,'Actual-M runtime changed during Native')
        M.verify(prepared,rederive=False)
        stage_membership(manifest,completed=True)
        report.update(passed=True,status='completed-positive-private-pending',native_actual_checks=len(rows),
            full_foundation_runtime_after=after_runtime,tool_identity_after=after_identity,native_journal=bound(journal),
            generated_object_sha256={str(Path(row['target_olean'])):R.digest(row['target_olean']) for row in rows},
            whole_positive_private_axiom_audit_closed=True,inputs_unchanged=True,artifact_sha256=artifacts(output))
    except BaseException as error:
        report.update(passed=False,status='failed-or-interrupted',error=type(error).__name__+': '+str(error));raise
    finally:
        report.update(elapsed_seconds=round(time.monotonic()-start,3),finished_utc=datetime.now(timezone.utc).isoformat());save(path,report)
    return path


def verify_positive(path):
    path=R.regular(path).resolve();M.A.C.owned(path.parent,ROOT);record=R.read(path)
    F.require(record.get('schema')=='pinwheel.closure24-actual-M-positive.v1' and record.get('passed') is True and
        record.get('qualified') is False and record.get('status')=='completed-positive-private-pending' and
        record.get('final_correspondence_proved') is False and record.get('separate_private_controls_closed') is False and
        record.get('whole_positive_private_axiom_audit_closed') is True and record.get('inputs_unchanged') is True,
        'Complete original positive actual-M receipt required')
    F.require(record.get('native_budget_policy')==budget_policy(),'Actual-M positive execution budget policy changed')
    F.require(R.digest(record['prepared']['path'])==record['prepared']['sha256'],'Actual-M preparation changed')
    prepared,manifest=M.verify(record['prepared']['path']);rows=manifest['m_rows'];commands=record['commands']
    F.require(record.get('target')==prepared['actual_odb'] and
        record.get('physical_candidate')==prepared['physical_candidate'],'Actual-M positive selected another physical candidate')
    dep=D.verify(prepared['source_N']['path']);f03=D.foundation(dep['foundation_report']['path'])
    expected_roots=[Path(f03['positive_library']['path']),Path(f03['tools']['lean']).parent.parent/'lib/lean',
        Path(dep['positive_library']['path']),*[Path(stage['out']) for stage in manifest['stages']]]
    generated_roots_owned(expected_roots[2], expected_roots[3:])
    F.require(record['roots']==list(map(str,expected_roots)) and record['environment']['LEAN_PATH']==os.pathsep.join(map(str,expected_roots)) and
        record['environment']['LEAN_SYSROOT']==str(Path(f03['tools']['lean']).parent.parent),'Actual-M declared import roots changed')
    stage_membership(manifest,completed=True)
    F.require(record['native_actual_checks']==record['required_actual_modules']==len(rows)==len(commands) and
        [row['module'] for row in commands]==[row['module'] for row in rows] and
        record['full_foundation_runtime_before']==record['full_foundation_runtime_after'] and
        record['tool_identity_before']==record['tool_identity_after'],'Actual-M positive is a prefix or changed runtime')
    F.require(all(R.digest(file)==pin for file,pin in record['input_sha256'].items()) and
        all(R.digest(file)==pin for file,pin in record['generated_object_sha256'].items()) and
        artifacts(path.parent)==record['artifact_sha256'],'Actual-M positive inputs/objects/artifacts changed')
    journal=R.regular(record['native_journal']['path']);F.require(R.digest(journal)==record['native_journal']['sha256'],'Actual-M original native journal changed')
    events=[json.loads(line,object_pairs_hook=F.pairs) for line in journal.read_text().splitlines()]
    F.require(len(events)==2*len(commands),'Missing/extra actual-M native command events')
    for index,(native,row) in enumerate(zip(commands,rows)):
        verify_command_timeout(native)
        verify_imports(row['source'],expected_roots,native['resolved_imports'])
        intent,result=events[2*index:2*index+2]
        F.require(result==dict(event='result',**native) and intent.get('event')=='intent' and
            all(native.get(k)==v for k,v in intent.items() if k!='event') and
            native.get('index')==index and native.get('negative_control') is False and
            type(native.get('exit_code')) is int and native['exit_code']==0 and native.get('timed_out') is False and
            native.get('native_process_group_closed') is True and native['source']==row['source'] and
            native['argv']==native_argv(R.HOST_TOOLS['lean'],row['source'],row['target_olean']) and
            native['cwd']==str(ROOT) and native['environment']==record['environment'] and
            native['lean_path']==record['environment']['LEAN_PATH'] and
            native['compiler_sha256_before']==native['compiler_sha256_after']==R.HOST_PINS['lean'] and
            native['source_sha256_before']==native['source_sha256_after']==row['source_sha256']==R.digest(row['source']) and
            native['object_sha256']==record['generated_object_sha256'][row['target_olean']]==R.digest(row['target_olean']) and
            R.digest(native['log'])==native['log_sha256'],'Actual-M original Native source/object/log/intent differs')
    return record,prepared,manifest


verify_private_import_inventory = ORIGINAL.verify_private_import_inventory


private_texts = ORIGINAL.private_texts


def private(positive_report,output):
    commit,controller=source_seal();positive_record,prepared,manifest=verify_positive(positive_report)
    dep=D.verify(prepared['source_N']['path']);f03=D.foundation(dep['foundation_report']['path'])
    runtime=R.closed_report(dep['runtime_report']['path']);output=M.A.C.owned(output,ROOT)
    positive_roots=[Path(root).resolve() for root in positive_record['roots']]
    F.require(not output.exists() and output.is_relative_to(ROOT/M.A.C.CAMPAIGN) and
        not any(output.is_relative_to(root) for root in positive_roots),'Private controls require a separate fresh sibling root')
    output.mkdir(parents=True);owners=[row['module'] for row in dep['positive_import_rows']+manifest['m_rows']]
    texts=private_texts(owners)
    for name,text in texts.items():(output/(name+'.lean')).write_text(text)
    verify_private_import_inventory({name:(output/(name+'.lean')).read_text() for name in texts},owners)
    roots=[*positive_roots[:2],output,*positive_roots[2:]];env=environment(roots,f03['tools']['lean'])
    journal=output/'native.jsonl';path=output/'report.json';start=time.monotonic()
    report=dict(schema='pinwheel.closure24-actual-M-private.v1',passed=False,qualified=False,producer_commit=commit,
        controller=controller,positive_report=bound(positive_report),commands=[],target=prepared['actual_odb'],
        native_budget_policy=budget_policy(),
        physical_candidate=prepared['physical_candidate'],
        final_correspondence_proved=False,physical_acceptance=False,owners=owners,environment=env,
        roots=list(map(str,roots)),source_sha256={name:R.digest(output/(name+'.lean')) for name in texts})
    save(path,report)
    try:
        before_runtime=observe_foundation_runtime(f03);before_identity=runtime_identity(runtime)
        for index,name in enumerate((BAD,AUDIT)):
            source=output/(name+'.lean');obj=output/(name+'.olean');log=output/(name+'.log')
            row=compile_one(f03['tools']['lean'],source,obj,log,journal,index,name,env,roots,negative=True)
            report['commands'].append(row);save(path,report)
            F.require(type(row['exit_code']) is int and row['exit_code']==index and
                (row['object_sha256'] is not None if index==0 else not obj.exists()),'Actual-M separate private outcome differs')
        message=(output/(AUDIT+'.log')).read_text()
        F.require('Unapproved axioms in _private.'+BAD in message and '.forbiddenUnused' in message,
            'Actual-M private audit rejected for an unrelated reason')
        verify_positive(positive_report)
        after_runtime=observe_foundation_runtime(f03);after_identity=runtime_identity(runtime)
        F.require(before_runtime==after_runtime and before_identity==after_identity,'Actual-M private runtime changed')
        F.require(R.digest(controller['path'])==controller['sha256'],'Actual-M private controller changed')
        report.update(passed=True,unused_private_axiom_rejected=True,separate_private_controls_closed=True,
            full_foundation_runtime_before=before_runtime,full_foundation_runtime_after=after_runtime,
            tool_identity_before=before_identity,tool_identity_after=after_identity,native_journal=bound(journal),
            final_correspondence_proved=True,status='closed',artifact_sha256=artifacts(output),
            boundary='Complete actual-M+whole-owner audit+separate private control on the exact final Boolean ODB. Physical/RC/timing and finite public wire remain independent gates.')
    except BaseException as error:
        report.update(passed=False,status='failed-or-interrupted',error=type(error).__name__+': '+str(error));raise
    finally:
        report.update(elapsed_seconds=round(time.monotonic()-start,3));save(path,report)
    return path


def verify_private(path):
    path=R.regular(path).resolve();M.A.C.owned(path.parent,ROOT);record=R.read(path)
    F.require(record.get('schema')=='pinwheel.closure24-actual-M-private.v1' and record.get('passed') is True and
        record.get('qualified') is False and record.get('unused_private_axiom_rejected') is True and
        record.get('separate_private_controls_closed') is True and record.get('final_correspondence_proved') is True and
        record.get('physical_acceptance') is False and record.get('status')=='closed','Complete separate actual-M private closure required')
    F.require(record.get('native_budget_policy')==budget_policy(),'Actual-M private execution budget policy changed')
    F.require(R.digest(record['positive_report']['path'])==record['positive_report']['sha256'] and
        R.digest(record['controller']['path'])==record['controller']['sha256'],'Actual-M private consumed producer/positive changed')
    positive_record,prepared,manifest=verify_positive(record['positive_report']['path'])
    dep=D.verify(prepared['source_N']['path']);owners=[row['module'] for row in dep['positive_import_rows']+manifest['m_rows']]
    expected_roots=[*positive_record['roots'][:2],str(path.parent),*positive_record['roots'][2:]]
    F.require(record['owners']==owners and record['target']==prepared['actual_odb'] and
        record.get('physical_candidate')==prepared['physical_candidate'] and
        record['roots']==expected_roots and record['environment']['LEAN_PATH']==os.pathsep.join(expected_roots) and
        record['environment']['LEAN_SYSROOT']==positive_record['environment']['LEAN_SYSROOT'] and
        record['full_foundation_runtime_before']==record['full_foundation_runtime_after'] and
        record['tool_identity_before']==record['tool_identity_after'] and artifacts(path.parent)==record['artifact_sha256'],
        'Actual-M private complete ownership/runtime/artifacts changed')
    for name,text in private_texts(owners).items():
        F.require((path.parent/(name+'.lean')).read_text()==text and
            R.digest(path.parent/(name+'.lean'))==record['source_sha256'][name],'Private exact unused-axiom source changed')
    verify_private_import_inventory({name:(path.parent/(name+'.lean')).read_text() for name in (BAD,AUDIT)},owners)
    journal=R.regular(record['native_journal']['path']);F.require(R.digest(journal)==record['native_journal']['sha256'],'Private journal changed')
    events=[json.loads(line,object_pairs_hook=F.pairs) for line in journal.read_text().splitlines()]
    F.require(len(events)==4 and [row['module'] for row in record['commands']]==[BAD,AUDIT],'Private command pair omitted/duplicated')
    for index,row in enumerate(record['commands']):
        verify_command_timeout(row)
        intent,result=events[2*index:2*index+2];source=path.parent/(row['module']+'.lean');obj=source.with_suffix('.olean')
        verify_imports(source,expected_roots,row['resolved_imports'])
        F.require(intent.get('event')=='intent' and result==dict(event='result',**row) and
            all(row.get(k)==v for k,v in intent.items() if k!='event') and row.get('index')==index and
            row.get('negative_control') is True and type(row.get('exit_code')) is int and row['exit_code']==index and
            row.get('timed_out') is False and row.get('native_process_group_closed') is True and
            row['argv']==native_argv(R.HOST_TOOLS['lean'],source,obj) and row['environment']==record['environment'] and
            row['compiler_sha256_before']==row['compiler_sha256_after']==R.HOST_PINS['lean'] and
            row['source_sha256_before']==row['source_sha256_after']==record['source_sha256'][row['module']] and
            R.digest(row['log'])==row['log_sha256'] and
            (obj.is_file() and R.digest(obj)==row['object_sha256'] if index==0 else not obj.exists() and row['object_sha256'] is None),
            'Private original command/source/object/log/intent differs')
    message=(path.parent/(AUDIT+'.log')).read_text()
    F.require('Unapproved axioms in _private.'+BAD in message and '.forbiddenUnused' in message,
        'Private audit rejection was unrelated')
    return record


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    positive_parser=sub.add_parser('positive');positive_parser.add_argument('--prepared',required=True,type=Path)
    private_parser=sub.add_parser('private');private_parser.add_argument('--positive-report',required=True,type=Path)
    for child in (positive_parser,private_parser):child.add_argument('--output',required=True,type=Path)
    verify_parser=sub.add_parser('verify-private');verify_parser.add_argument('--report',required=True,type=Path)
    args=parser.parse_args()
    previous=signal.getsignal(signal.SIGTERM)
    def interrupted(signum,frame):raise KeyboardInterrupt('Root termination signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupted)
    try:
        if args.mode=='verify-private':print(json.dumps({'final_correspondence_proved':verify_private(args.report)['final_correspondence_proved']}))
        else:print(positive(args.prepared,args.output) if args.mode=='positive' else private(args.positive_report,args.output))
    finally:signal.signal(signal.SIGTERM,previous)


if __name__=='__main__':main()
