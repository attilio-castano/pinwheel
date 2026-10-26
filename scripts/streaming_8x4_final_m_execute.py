"""Root-guarded complete actual-M execution and separate private controls.

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
import streaming_8x4_final_m as M
import streaming_tt_fresh_foundation as F
from streaming_mapped_campaign import audit_source

ROOT=Path(__file__).resolve().parents[1]
BAD='PhysicalGRTExactPrivateAxiom'
AUDIT='PhysicalGRTExactPrivateAudit'
REQUIRED='PhysicalGRTFinalRequired'
LONG_MODULES=frozenset(('PhysicalStateCodec','ActualGRTClockDAGProof',
    'PhysicalGRTOriginalProof','PhysicalGRTActualProof','PhysicalGRTFinalAudit',AUDIT))


def budget_policy():
    return dict(schema='pinwheel.streaming-8x4-actual-M-native-budget.v1',
        default_module_seconds=180,exact_long_module_seconds=600,exact_long_modules=sorted(LONG_MODULES),
        mathematical_sources_unchanged=True,outer_four_hour_limit_unchanged=True,
        outer_positive_cutoff_and_private_wire_reserve_required=True)


def command_timeout(module):
    F.require(type(module) is str and re.fullmatch('[A-Za-z_][A-Za-z0-9_]*',module),
        'Native budget requires an exact generated module name')
    return 600 if module in LONG_MODULES else 180


def verify_command_timeout(row):
    F.require(type(row.get('timeout_seconds')) is int and
        row['timeout_seconds']==command_timeout(row['module']),
        'Actual-M command timeout differs from the reviewed exact-name policy')


def bound(path):return dict(path=str(R.regular(path).resolve()),sha256=R.digest(path))


def save(path,value):
    path=Path(path);temporary=path.with_name(path.name+'.tmp')
    with temporary.open('w') as stream:
        stream.write(json.dumps(value,indent=2,allow_nan=False)+'\n');stream.flush();os.fsync(stream.fileno())
    temporary.replace(path)


def event(path,value):
    with Path(path).open('a') as stream:stream.write(json.dumps(value,allow_nan=False)+'\n');stream.flush();os.fsync(stream.fileno())


def source_seal():
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True,timeout=30).strip()
    own=Path(__file__).resolve();name=str(own.relative_to(ROOT))
    payload=subprocess.check_output(['git','show',commit+':'+name],cwd=ROOT,timeout=30)
    F.require(hashlib.sha256(payload).hexdigest()==R.digest(own),'Commit actual-M Native controller before execution')
    F.require(not sys.flags.optimize,'Refuse optimized Native actual-M controller')
    F.check_native_environment();return commit,bound(own)


def observe_foundation_runtime(f03):
    """Fresh complete14923-file observation, not the old audit's success flag."""
    original=R.read(f03['original_runtime_report']['path'])
    marker=original['runtime_before']
    pairs=[row for row in f03['explicit_runtime_relocations'] if row['original_path']==marker['path'] and row['sha256']==marker['sha256']]
    F.require(len(pairs)==1 and R.digest(pairs[0]['path'])==marker['sha256'],'Exact complete foundation runtime map missing')
    runtime=R.read(pairs[0]['path']);F.require(len(runtime)==14923,'Complete foundation runtime selection changed')
    for name,value in runtime.items():
        path=Path(name)
        F.require(path.is_absolute() and path.is_file() and str(path.resolve())==value['resolved'] and
            path.stat().st_size==value['bytes'] and F.sha(path)==value['sha256'],'Actual complete foundation runtime changed: '+name)
    prefix=Path(f03['tools']['lean']).parent.parent;stdlib=prefix/'lib/lean'
    F.require(not any(path.is_symlink() and path.is_dir() for path in stdlib.rglob('*')) and
        {str(path) for path in stdlib.rglob('*') if path.is_file()}==
        {name for name in runtime if Path(name).is_relative_to(stdlib)},'Complete compiled Lean runtime membership changed')
    return dict(files=len(runtime),identity_map=bound(pairs[0]['path']),all_current_bytes_match=True)


def native_argv(lean,source,obj):
    source,obj=Path(source),Path(obj)
    return [str(lean),'-M4096','-j1','-DElab.async=false','--root='+str(source.parent),
        '-DwarningAsError=true','-DmaxErrors=1','-o',str(obj),str(source)]


def imports(source,roots):
    required=[]
    for line in Path(source).read_text().splitlines():
        match=re.fullmatch(r'\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)\s*',line)
        if match:required.append(match[1])
        elif re.match(r'\s*(?:public\s+)?import\b',line):raise ValueError('Unsupported generated import syntax')
    found={}
    for name in required:
        relative=name.replace('.','/')+'.olean';paths=[Path(root)/relative for root in roots if (Path(root)/relative).exists()]
        F.require(len(paths)==1 and not paths[0].is_symlink(),'Import missing or multiply resolved: '+name)
        found[name]=bound(paths[0])
    return found


def verify_imports(source,roots,expected):
    F.require(imports(source,roots)==expected,'Stored per-command actual import resolution changed')


def compile_one(lean,source,obj,log,journal,index,module,environment,roots,*,negative=False):
    F.require(not obj.exists() and not log.exists(),'Preserve prior Native module attempt')
    resolution=imports(source,roots);argv=native_argv(lean,source,obj)
    row=dict(index=index,module=module,source=str(source),source_sha256_before=R.digest(source),argv=argv,
        cwd=str(ROOT),environment=environment,lean_path=environment['LEAN_PATH'],resolved_imports=resolution,
        compiler_sha256_before=R.digest(lean),negative_control=negative,timeout_seconds=command_timeout(module))
    event(journal,dict(event='intent',**row));start=time.monotonic();child=None;timed_out=False;code=None
    try:
        with log.open('xb') as stream:
            child=subprocess.Popen(argv,cwd=ROOT,env=environment,stdin=subprocess.DEVNULL,stdout=stream,
                stderr=subprocess.STDOUT,start_new_session=True)
            try:code=child.wait(timeout=row['timeout_seconds'])
            except subprocess.TimeoutExpired:
                timed_out=True;F.terminate_group(child.pid);child.wait(timeout=3);code=124
    finally:
        if child is not None:
            if child.poll() is None:F.terminate_group(child.pid);child.wait(timeout=3)
            closed=F.closed_group(child.pid)
            if not closed:closed=F.terminate_group(child.pid)
        else:closed=False
        row.update(exit_code=code,timed_out=timed_out,native_process_group_closed=closed,
            source_sha256_after=R.digest(source),compiler_sha256_after=R.digest(lean),
            log=str(log),log_sha256=R.digest(log) if log.is_file() else None,
            object_sha256=R.digest(obj) if obj.is_file() else None,elapsed_seconds=round(time.monotonic()-start,3))
        event(journal,dict(event='result',**row))
    F.require(not timed_out and closed and row['source_sha256_before']==row['source_sha256_after'] and
        row['compiler_sha256_before']==row['compiler_sha256_after'] and imports(source,roots)==resolution,
        'Actual-M native source/compiler/import/process boundary changed')
    return row


def environment(roots,lean):
    env={key:os.environ[key] for key in ('HOME','PATH','TMPDIR','LANG','LC_ALL') if key in os.environ}
    env.update(LEAN_PATH=os.pathsep.join(map(str,roots)),LEAN_SYSROOT=str(Path(lean).parent.parent));return env


def input_seal(prepared,manifest,record,controller):
    before={**manifest['input_sha256'],**manifest['producer_sha256'],**record['producer_sha256']}
    before.update({str(Path(prepared).resolve()):R.digest(prepared),controller['path']:controller['sha256']})
    for key in ('generation_request','generation_manifest','generator','original_generator','adaptation_diff'):
        before[record[key]['path']]=record[key]['sha256']
    F.require(all(R.digest(path)==pin for path,pin in before.items()),'Complete actual-M frozen input changed')
    return before


def runtime_identity(runtime):
    raw=R.load('_streaming8_M_native_identity',ROOT/'scripts/check-streaming-uart.py')
    helper=raw.helpers();raw.check_environment(helper)
    identity=raw.tool_identity(helper,runtime['tools'],R.read(ROOT/'tools/hardware-toolchain.json'))
    F.require(identity==runtime['tool_identity_after'],'Actual selected Native runtime differs from admitted runtime')
    return identity


def stage_membership(manifest, *, completed):
    for stage in manifest['stages']:
        root=Path(stage['out']);names=stage['modules']
        expected={name+'.lean' for name in names}|{'modules.json'}
        if completed:expected|={name+'.olean' for name in names}
        F.require(not any(path.is_symlink() for path in root.rglob('*')) and
            {str(path.relative_to(root)) for path in root.rglob('*') if path.is_file()}==expected,
            'Actual-M stage contains missing/extra source, cached or unowned objects')


def artifacts(root):return {str(path.relative_to(root)):R.digest(path) for path in sorted(Path(root).rglob('*'))
    if path.is_file() and path!=Path(root)/'report.json'}


def positive(prepared,output):
    commit,controller=source_seal();output=Path(output).absolute()
    F.require(not output.exists(),'Preserve prior actual-M Native attempt')
    output.mkdir(parents=True);path=output/'report.json';start=time.monotonic()
    report=dict(schema='pinwheel.streaming-8x4-actual-M-positive.v1',passed=False,qualified=False,status='host-admission',
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
        F.generated_paths_owned(roots[2:],ROOT/'build/campaigns/8x4-20261022-01')
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
    path=R.regular(path).resolve();record=R.read(path)
    F.require(record.get('schema')=='pinwheel.streaming-8x4-actual-M-positive.v1' and record.get('passed') is True and
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


def verify_private_import_inventory(texts,owners):
    F.require(set(texts)=={BAD,AUDIT},'Private controls have an undeclared module owner')
    expected={BAD:[REQUIRED],AUDIT:['Lean',*owners,BAD]}
    for name,text in texts.items():
        lines=[line for line in text.splitlines() if re.match(r'\s*(?:public\s+)?import\b',line)]
        F.require(lines==['import '+owner for owner in expected[name]],
            'Private positive import is outside the exact actual manifest N+M namespace or ordered inventory')


def private_texts(owners):
    F.require(owners and len(set(owners))==len(owners) and BAD not in owners and AUDIT not in owners,'Complete unique N+M owners required')
    F.require(REQUIRED in owners,'Complete actual-M required owner is missing from private controls')
    texts={BAD:'import '+REQUIRED+'\nnamespace Pinwheel.Artifact.StreamingPhysicalGRT.ExactNegativeControl\n'
        'private axiom forbiddenUnused : False\nend Pinwheel.Artifact.StreamingPhysicalGRT.ExactNegativeControl\n',
        AUDIT:audit_source([*owners,BAD])}
    verify_private_import_inventory(texts,owners)
    return texts


def private(positive_report,output):
    commit,controller=source_seal();positive_record,prepared,manifest=verify_positive(positive_report)
    dep=D.verify(prepared['source_N']['path']);f03=D.foundation(dep['foundation_report']['path'])
    runtime=R.closed_report(dep['runtime_report']['path']);output=Path(output).absolute()
    positive_roots=[Path(root).resolve() for root in positive_record['roots']]
    F.require(not output.exists() and output.is_relative_to(ROOT/'build/campaigns/8x4-20261022-01') and
        not any(output.is_relative_to(root) for root in positive_roots),'Private controls require a separate fresh sibling root')
    output.mkdir(parents=True);owners=[row['module'] for row in dep['positive_import_rows']+manifest['m_rows']]
    texts=private_texts(owners)
    for name,text in texts.items():(output/(name+'.lean')).write_text(text)
    verify_private_import_inventory({name:(output/(name+'.lean')).read_text() for name in texts},owners)
    roots=[*positive_roots[:2],output,*positive_roots[2:]];env=environment(roots,f03['tools']['lean'])
    journal=output/'native.jsonl';path=output/'report.json';start=time.monotonic()
    report=dict(schema='pinwheel.streaming-8x4-actual-M-private.v1',passed=False,qualified=False,producer_commit=commit,
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
    path=R.regular(path).resolve();record=R.read(path)
    F.require(record.get('schema')=='pinwheel.streaming-8x4-actual-M-private.v1' and record.get('passed') is True and
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
