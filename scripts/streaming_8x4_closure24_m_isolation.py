"""Fresh-process full rederivation barrier; unchanged complete M mathematics.

This is an execution-memory hypothesis, not a claim about the old RSS split or
Lean feasibility. Existing generators, failed receipts and prefix objects stay
immutable. Complete acceptance requires a fresh source-only M owner.
"""
import ast
from datetime import datetime,timezone
import difflib
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import types

import streaming_8x4_closure24_m_scope as SCOPE
import streaming_8x4_closure24_scope_m as M
import streaming_8x4_closure24_scope_m_execute as PRIOR
import streaming_8x4_closure24_m_process as PROCESS
import streaming_8x4_closure24_policy as CLOCK

ROOT=SCOPE.ROOT
OWN='scripts/streaming_8x4_closure24_m_isolation.py'
ENTRY='scripts/streaming_8x4_closure24_isolated_m_execute.py'
OBSERVER='scripts/streaming_8x4_closure24_m_process.py'
DIAGNOSTIC='scripts/streaming_8x4_closure24_m_assignment_diagnostic.py'
REDERIVE_SECONDS=600
need=PRIOR.F.require
R=PRIOR.R
replace_once=SCOPE.replace_once


def bound(path):return PRIOR.bound(path)


def python_identity():
    actual=Path(sys.executable).resolve(strict=True)
    return dict(path=sys.executable,resolved=str(actual),sha256=R.digest(actual),version=sys.version,optimize=sys.flags.optimize)


def sources(*,committed=False,commit=None):
    # These four files import only stdlib and the explicit immutable M/runtime
    # adapters below. The historical generator's complete transitive/dynamic
    # project closure is independently present in manifest.producer_sha256 and
    # rechecked by M.verify/input_seal; do not reinterpret historical dynamic
    # archive loaders with a new generic AST resolver.
    names=sorted(set((*M.SOURCES,OWN,ENTRY,OBSERVER,DIAGNOSTIC,
        str(Path(PRIOR.ORIGINAL.__file__).relative_to(ROOT)),
        str(Path(R.__file__).relative_to(ROOT)),str(Path(PRIOR.F.__file__).relative_to(ROOT)),
        str(Path(CLOCK.__file__).relative_to(ROOT)))))
    files={name:R.digest(ROOT/name)for name in names}
    commit=commit or subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True,timeout=30).strip()
    need(len(commit)==40 and all(c in '0123456789abcdef'for c in commit),'Exact immutable process producer commit required')
    if committed:
        need(not sys.flags.optimize,'Refuse optimized M process admission')
        for name,pin in files.items():
            payload=subprocess.check_output(['git','show',commit+':'+name],cwd=ROOT,timeout=30)
            need(hashlib.sha256(payload).hexdigest()==pin,'Commit new M process producer before execution: '+name)
    return dict(commit=commit,source_projection=dict(files=names,
        boundary='New process producers plus immutable M context/runtime adapters; complete generator/helper closure remains separately bound by the actual M manifest'),sha256=files)


def input_seal(prepared,record,manifest,*,producer=None):
    producer=producer or sources()
    result=PRIOR.input_seal(prepared,manifest,record,bound(ROOT/ENTRY))
    result.update({str(ROOT/name):pin for name,pin in producer['sha256'].items()})
    result.update({row['source']:row['source_sha256']for row in manifest['m_rows']})
    result.update({stage['schedule']['path']:stage['schedule']['sha256']for stage in manifest['stages']})
    interpreter=python_identity();result[interpreter['resolved']]=interpreter['sha256']
    need(all(R.digest(name)==pin for name,pin in result.items()),'Full isolated M current input changed')
    return result


def runtime(record):
    dep=PRIOR.D.verify(record['source_N']['path']);f03=PRIOR.D.foundation(dep['foundation_report']['path'])
    report=R.closed_report(dep['runtime_report']['path'])
    return dict(foundation=PRIOR.observe_foundation_runtime(f03),tools=PRIOR.runtime_identity(report))


def current_runtime_binding(record):
    """Pure file reobservation for reopeners; does not run tool executables."""
    dep=PRIOR.D.verify(record['source_N']['path']);f03=PRIOR.D.foundation(dep['foundation_report']['path'])
    report=R.closed_report(dep['runtime_report']['path'])
    return dict(foundation=PRIOR.observe_foundation_runtime(f03),tools=report['tool_identity_after'])


def rederive_argv(prepared,output):
    return [sys.executable,'-B',str(ROOT/ENTRY),'rederive','--prepared',str(Path(prepared).resolve()),'--output',str(Path(output).resolve())]


def rederive(prepared,output):
    """Child-only full unmodified independent derivation; never invokes Lean."""
    producer=sources(committed=True);output=M.A.C.owned(output,ROOT)
    need(not output.exists(),'Preserve earlier rederivation child');output.mkdir(parents=True)
    path=output/'report.json';started=time.monotonic()
    report=dict(schema='pinwheel.closure24-M-rederivation-child.v1',passed=False,prepared=bound(prepared),
        producer=producer,python=python_identity(),
        pid=os.getpid(),pgid=os.getpgrp(),argv=rederive_argv(prepared,output),
        self_process=PROCESS.snapshot((os.getpid(),))[os.getpid()],
        full_positive_proved=False,physical_acceptance=False,Native_Lean_executed=False)
    PRIOR.save(path,report)
    try:
        record,manifest=M.verify(prepared,rederive=False);PRIOR.stage_membership(manifest,completed=False)
        before=input_seal(prepared,record,manifest,producer=producer);before_runtime=runtime(record)
        # The exact complete original verifier runs here, in this process only.
        checked,expected=M.verify(prepared,rederive=True)
        need(checked==record and expected==manifest,'Full child rederivation returned a different complete plan')
        after_runtime=runtime(record);need(after_runtime==before_runtime,'Child full runtime identity changed')
        need(input_seal(prepared,record,manifest,producer=producer)==before and sources(committed=True,commit=producer['commit'])==producer,
            'Child inputs or committed producer changed')
        report.update(passed=True,complete_independent_rederivation=True,all_actual_modules=len(manifest['m_rows']),
            actual_odb=record['actual_odb'],physical_candidate=record['physical_candidate'],generation_manifest=record['generation_manifest'],
            source_worker_context=record['source_worker_context'],input_sha256=before,
            runtime_before=before_runtime,runtime_after=after_runtime)
    except BaseException as error:report['error']=type(error).__name__+': '+str(error);raise
    finally:
        report['seconds']=round(time.monotonic()-started,6);PRIOR.save(path,report)
    return path


def run_rederive(prepared,output):
    output=Path(output).resolve();need(not output.exists(),'Preserve earlier rederivation barrier')
    # Reject cached/prefix objects before spending time on independent replay.
    record,manifest=M.verify(prepared,rederive=False);PRIOR.stage_membership(manifest,completed=False)
    argv=rederive_argv(prepared,output);log=output.parent/'rederivation.log';memory=output.parent/'rederivation-memory.jsonl'
    need(not log.exists() and not memory.exists(),'Preserve prior rederivation observations')
    started=time.monotonic();child=None;watch=None;code=None;timed_out=False;closed=False
    try:
        with log.open('xb') as stream:
            child=subprocess.Popen(argv,cwd=ROOT,stdin=subprocess.DEVNULL,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
            watch=PROCESS.start(child.pid,argv,memory,label='complete-independent-rederivation')
            try:code=child.wait(timeout=REDERIVE_SECONDS)
            except subprocess.TimeoutExpired:
                timed_out=True;PRIOR.F.terminate_group(child.pid);child.wait(timeout=3);code=124
    finally:
        if child is not None:
            if child.poll()is None:PRIOR.F.terminate_group(child.pid);child.wait(timeout=3)
            closed=PRIOR.F.closed_group(child.pid)
            if not closed:closed=PRIOR.F.terminate_group(child.pid)
        observer_error=None
        try:PROCESS.finish(watch)
        except BaseException as error:observer_error=type(error).__name__+': '+str(error)
        row=dict(schema='pinwheel.closure24-M-rederivation-process.v1',argv=argv,cwd=str(ROOT),pid=child.pid if child else None,
            exit_code=code,timed_out=timed_out,process_group_closed=closed,timeout_seconds=REDERIVE_SECONDS,
            seconds=round(time.monotonic()-started,6),log=bound(log),memory_journal=bound(memory)if memory.exists()else None,
            observer_error=observer_error)
        PRIOR.save(output.parent/'rederivation-process.json',row)
    need(code==0 and closed and not timed_out and observer_error is None,'Complete independent rederivation child failed or remained owned')
    return verify_rederive(output/'report.json',prepared)


def verify_rederive(path,prepared):
    path=R.regular(path);child=R.read(path);record,manifest=M.verify(prepared,rederive=False)
    producer=sources(committed=True,commit=child['producer']['commit']);process_path=path.parent.parent/'rederivation-process.json';process=R.read(process_path)
    argv=rederive_argv(prepared,path.parent)
    need(child['schema']=='pinwheel.closure24-M-rederivation-child.v1' and child.get('passed')is True and
        child.get('complete_independent_rederivation')is True and child['prepared']==bound(prepared) and child['producer']==producer and
        child['all_actual_modules']==len(manifest['m_rows']) and child['actual_odb']==record['actual_odb'] and
        child['physical_candidate']==record['physical_candidate'] and child['generation_manifest']==record['generation_manifest'] and
        child['source_worker_context']==record['source_worker_context'] and child['input_sha256']==input_seal(prepared,record,manifest,producer=producer) and
        child['runtime_before']==child['runtime_after']==current_runtime_binding(record) and child['Native_Lean_executed']is False and
        child['full_positive_proved']is False and child['physical_acceptance']is False,'Complete isolated rederivation identity differs')
    need(child['python']==python_identity() and child['python']['optimize']==0 and child['argv']==argv and
        child['pid']==child['pgid']==process['pid'],'Rederivation interpreter/owned process identity differs')
    need(process['schema']=='pinwheel.closure24-M-rederivation-process.v1' and process['argv']==argv and process['cwd']==str(ROOT) and
        process['exit_code']==0 and process['timed_out']is False and process['process_group_closed']is True and process['observer_error']is None and
        process['timeout_seconds']==REDERIVE_SECONDS and process['log']==bound(path.parent.parent/'rederivation.log') and
        process['memory_journal']==bound(path.parent.parent/'rederivation-memory.jsonl'),'Rederivation command/timeout/cleanup differs')
    observation=PROCESS.verify(process['memory_journal']['path'],[('complete-independent-rederivation',argv)],require_child_observed=True)
    need(observation['parent_pid']!=child['pid'] and child['runtime_before']['foundation']['files']==14923,
        'Rederivation was not a separate process or complete runtime')
    own=child['self_process'];need(own['pid']==own['pgid']==child['pid'] and own['ppid']==observation['parent_pid'] and
        PROCESS.argv_matches(own['command'],argv) and own['observed_executable']==PROCESS.executable_identity(own['command']),
        'Child self-process/actual executable differs from declared launch')
    need(PROCESS.lifetime(own)==observation['observations'][0]['child_lifetime'],'Child self-process birth/executable differs from outer observation')
    return dict(report=bound(path),process=bound(process_path),memory=process['memory_journal'],
        complete_independent_rederivation=True,child_closed_before_Lean=True)


def verify_memory(report):
    row=report['process_memory'];path=Path(row['path']);need(bound(path)==row,'Complete M process memory journal changed')
    commands=[(item['module'],item['argv'])for item in report['commands']]
    summary=PROCESS.verify(path,commands)
    need(PROCESS.lifetime(report['driver_process'])==summary['parent_lifetime'],'Driver actual startup identity differs from observations')
    return summary


def compile_source():
    """Exact canonical compiler body plus separate observational side journal."""
    original=Path(PRIOR.ORIGINAL.__file__).read_text();node=next(n for n in ast.parse(original).body if isinstance(n,ast.FunctionDef)and n.name=='compile_one')
    text=''.join(original.splitlines(True)[node.lineno-1:node.end_lineno])
    text=replace_once(text,'child=None;timed_out=False;code=None','child=None;timed_out=False;code=None;memory_watch=None')
    text=replace_once(text,'            try:code=child.wait(timeout=row[\'timeout_seconds\'])',
        "            memory_watch=PROCESS.start(child.pid,argv,journal.parent/'process-memory.jsonl',label=module)\n            try:code=child.wait(timeout=row['timeout_seconds'])")
    text=replace_once(text,'        row.update(exit_code=code,','        PROCESS.finish(memory_watch)\n        row.update(exit_code=code,')
    return text


def controller_source():
    original,_=SCOPE.controller_source('execution');text=original
    text=replace_once(text,'import streaming_8x4_closure24_m_scope as SCOPE',
        'import streaming_8x4_closure24_m_scope as SCOPE\nimport streaming_8x4_closure24_m_isolation as ISOLATION')
    text=replace_once(text,'    SCOPE.controller_source("execution")','    SCOPE.controller_source("execution")\n    ISOLATION.sources(committed=True)')
    text=replace_once(text,'compile_one = ORIGINAL.compile_one',
        "_compile_namespace=dict(vars(ORIGINAL),PROCESS=ISOLATION.PROCESS)\nexec(compile(ISOLATION.compile_source(),'<observed-canonical-M-compile>','exec'),_compile_namespace)\ncompile_one=_compile_namespace['compile_one']")
    text=replace_once(text,"    for key in ('generation_request','generation_manifest','generator','original_generator','adaptation_diff'):",
        "    before.update({str(ROOT/name):pin for name,pin in ISOLATION.sources(committed=True)['sha256'].items()})\n    for key in ('generation_request','generation_manifest','generator','original_generator','adaptation_diff'):")
    text=replace_once(text,"        record,manifest=M.verify(prepared,rederive=True);dep=D.verify(record['source_N']['path'])",
        "        report['driver_process']=ISOLATION.PROCESS.snapshot((os.getpid(),))[os.getpid()];save(path,report)\n        admission=ISOLATION.run_rederive(prepared,output/'rederivation')\n        report['rederivation_admission']=admission;save(path,report)\n        record,manifest=M.verify(prepared,rederive=False);dep=D.verify(record['source_N']['path'])")
    text=replace_once(text,'        stage_membership(manifest,completed=True)\n        report.update(passed=True,',
        "        stage_membership(manifest,completed=True)\n        ISOLATION.verify_rederive(admission['report']['path'],prepared)\n        report['process_memory']=bound(output/'process-memory.jsonl');ISOLATION.verify_memory(report)\n        report.update(passed=True,")
    text=replace_once(text,"    prepared,manifest=M.verify(record['prepared']['path']);rows=manifest['m_rows'];commands=record['commands']",
        "    F.require(ISOLATION.verify_rederive(record['rederivation_admission']['report']['path'],record['prepared']['path'])==record['rederivation_admission'],'Complete isolated rederivation admission changed')\n    ISOLATION.verify_memory(record)\n    prepared,manifest=M.verify(record['prepared']['path']);rows=manifest['m_rows'];commands=record['commands']")
    text=replace_once(text,'        report.update(passed=True,unused_private_axiom_rejected=True,',
        "        report['process_memory']=bound(output/'process-memory.jsonl');ISOLATION.verify_memory(report)\n        report.update(passed=True,unused_private_axiom_rejected=True,")
    text=replace_once(text,"    positive_record,prepared,manifest=verify_positive(record['positive_report']['path'])",
        "    ISOLATION.verify_memory(record)\n    positive_record,prepared,manifest=verify_positive(record['positive_report']['path'])")
    text=replace_once(text,"    save(path,report)\n    try:\n        before_runtime=observe_foundation_runtime(f03);before_identity=runtime_identity(runtime)",
        "    report['driver_process']=ISOLATION.PROCESS.snapshot((os.getpid(),))[os.getpid()]\n    save(path,report)\n    try:\n        before_runtime=observe_foundation_runtime(f03);before_identity=runtime_identity(runtime)")
    for old,new in (('pinwheel.closure24-scope-actual-M-positive.v1','pinwheel.closure24-isolated-actual-M-positive.v1'),
        ('pinwheel.closure24-scope-actual-M-private.v1','pinwheel.closure24-isolated-actual-M-private.v1')):
        need(old in text,'Missing frozen complete M receipt schema');text=text.replace(old,new)
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-scope/execution',tofile='isolated-rederivation/execution'))


def load_controller(name,path):
    text,diff=controller_source();module=types.ModuleType(name+'.isolated_rederivation_body');module.__file__=str(Path(path).resolve())
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::isolated-rederivation-body','exec'),module.__dict__)
    module.ISOLATION_ADAPTATION_DIFF=diff;return module
