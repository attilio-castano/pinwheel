"""Derive fresh replay cardinality from independently regenerated parent sources."""
from pathlib import Path
from contextlib import contextmanager
from contextvars import ContextVar
from copy import deepcopy
import json
import os
import re
import signal
import subprocess
import time
import threading
import uuid

import streaming_tt_fresh_foundation as F

ROOT=Path(__file__).resolve().parents[1]
_LOADED_SOURCE_SHA256=F.sha(Path(__file__).resolve())
_LOADED_FOUNDATION_SHA256=F.sha(Path(F.__file__).resolve())
_HOST_BOUNDARY=ContextVar('streaming_tt_exact_inventory_host_boundary',default=None)
PROFILE='pinwheel.streaming-tt-exact-parent-replay.v1'
CHECKS={'fresh_raw_source_gate','archive_membership','worker_kernel_join','private_axiom_audit',
    'tool_identity','input_closeout','semantic_ff_bijection','independent_proof_source_regeneration','physical_sv_reimport'}
STAGES=('frontend-proof','core-d2-proof','device-proof')
HOST_TIMEOUT=60
HOST_OUTPUT_LIMIT=8388608
HOST_ENV_KEYS=('HOME','PATH','TMPDIR','LANG','LC_ALL')
CHILD=r'''
import json, os, subprocess, sys, sysconfig
from pathlib import Path
scripts=Path(sys.argv[1]).resolve()
sys.path.insert(0,str(scripts))
def forbidden(*args,**kwargs):raise RuntimeError('Native/tool execution forbidden during host regeneration')
# These are the reviewed generator's known tool entrypoints, not a security sandbox.
for name in ('Popen','run','call','check_call','check_output'):setattr(subprocess,name,forbidden)
os.system=forbidden
import streaming_tt_opt_intake as generator
cfg=json.loads(Path(sys.argv[2]).read_text());worker=json.loads(Path(sys.argv[3]).read_text())
modules,identities=generator.regenerated_sources(cfg,worker,Path(sys.argv[4]))
stdlib=Path(sysconfig.get_path('stdlib')).resolve();project={}
for name,module in sorted(sys.modules.items()):
 value=getattr(module,'__file__',None)
 if not value:continue
 path=Path(value).resolve()
 if path.is_relative_to(scripts):project[str(path)]=name
 elif not path.is_relative_to(stdlib) or {'site-packages','dist-packages'}&set(path.parts):
  raise RuntimeError('Imported Python source outside selected scripts/stdlib: '+str(path))
if str(scripts/'streaming_tt_opt_intake.py') not in project:raise RuntimeError('Wrong regeneration module owner')
print(json.dumps(dict(modules=modules,identities=identities,project_imports=project,
 python=str(Path(sys.executable).resolve())),sort_keys=True,separators=(',',':')))
'''


def validator_context(workspace):
    """Keep canonical receipt identities distinct from the executed source paths."""
    workspace=Path(workspace).resolve()
    canonical={name:F.regular(workspace/'scripts'/name) for name in
        ('streaming_tt_replay_inventory.py','streaming_tt_fresh_foundation.py',
         'streaming_tt_fresh_replay.py','streaming_tt_replay_intake.py')}
    executed={'streaming_tt_replay_inventory.py':F.regular(Path(__file__).resolve()),
        'streaming_tt_fresh_foundation.py':F.regular(Path(F.__file__).resolve())}
    F.require(F.sha(executed['streaming_tt_replay_inventory.py'])==_LOADED_SOURCE_SHA256 and
        F.sha(executed['streaming_tt_fresh_foundation.py'])==_LOADED_FOUNDATION_SHA256 and
        all(F.sha(path)==F.sha(canonical[name]) for name,path in executed.items()),
        'Executed staged inventory/foundation producer differs from canonical validator')
    return canonical,{str(path):F.sha(path) for path in executed.values()}


@contextmanager
def _host_boundary(parent_path,*,validator_workspace=None):
    """Private pure-host validation scope; no Native execution belongs inside it.

    Entry performs a real isolated regeneration. Repeated derives retain every
    input/receipt/membership check and reuse only that deterministic child value.
    Exit revalidates the whole boundary; no payload survives this invocation.
    """
    F.require(_HOST_BOUNDARY.get() is None,'Nested host inventory boundary refused')
    workspace=Path(validator_workspace).resolve() if validator_workspace is not None else ROOT
    state=dict(parent=str(Path(parent_path).resolve()),workspace=str(workspace),
        owner=(os.getpid(),threading.get_ident()),key=None,payload=None,children=0,failed=False)
    token=_HOST_BOUNDARY.set(state)
    try:
        value=derive(parent_path,validator_workspace=workspace)
        yield value
        F.require(not state['failed'] and state['children']==1,
            'Host inventory boundary did not retain one successful isolated regeneration')
        derive(parent_path,validator_workspace=workspace)
    finally:
        state.clear()
        _HOST_BOUNDARY.reset(token)


def _regeneration_payload(context,request):
    """Memoize the child result only, after the caller's complete live checks."""
    state=_HOST_BOUNDARY.get()
    if state is None:return regenerate(**request)
    F.require(state and not state['failed'] and
        state['owner']==(os.getpid(),threading.get_ident()) and
        (state['parent'],state['workspace'])==(context['parent'],context['workspace']),
        'Host inventory boundary identity or prior validation failed')
    key=json.dumps(context,sort_keys=True,separators=(',',':'))
    if state['key'] is not None:
        F.require(state['key']==key,'Host inventory inputs changed within a validation boundary')
    else:
        payload=regenerate(**request)
        state.update(key=key,payload=deepcopy(payload),children=state['children']+1)
    return deepcopy(state['payload'])


def regenerate(config_path,worker_path,config,worker,*,observation_base=None,execution_producers=None,canonical_producers=None):
    """Bounded pure Python in the selected archive; no inherited project imports."""
    F.check_native_environment();python=F.regular(Path(config['tools']['python']).resolve())
    argv=[str(python),'-I','-S','-B','-c',CHILD,str(Path(config['root'])/'scripts'),
        str(config_path),str(worker_path),str(worker_path.parent)]
    base=Path(observation_base) if observation_base is not None else ROOT/'build/streaming-tt-replay-inventory'
    out=base/('observation-'+uuid.uuid4().hex);out.mkdir(parents=True)
    log=out/'stdout.log';receipt=out/'report.json'
    row=dict(schema='pinwheel.streaming-tt-host-regeneration.v1',qualified=False,status='intent',
        argv=argv,python_sha256=F.sha(python),producer=F.bound(Path(__file__).resolve()),
        executed_producer_sha256=execution_producers or {str(Path(__file__).resolve()):F.sha(__file__)},
        canonical_producer_sha256=canonical_producers or {},
        timeout_seconds=HOST_TIMEOUT,output_limit_bytes=HOST_OUTPUT_LIMIT)
    def write():receipt.write_text(json.dumps(row,indent=2)+'\n')
    write();start=time.monotonic();reason=None
    env={key:os.environ[key] for key in HOST_ENV_KEYS if key in os.environ}
    with log.open('wb') as stream:
        child=subprocess.Popen(argv,stdout=stream,stderr=subprocess.STDOUT,env=env,start_new_session=True)
        while child.poll() is None:
            if time.monotonic()-start>HOST_TIMEOUT:reason='timeout';break
            if log.stat().st_size>HOST_OUTPUT_LIMIT:reason='output_limit';break
            time.sleep(.02)
        if reason:
            try:os.killpg(child.pid,signal.SIGTERM)
            except ProcessLookupError:pass
            try:child.wait(timeout=3)
            except subprocess.TimeoutExpired:
                try:os.killpg(child.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                child.wait(timeout=3)
        if log.stat().st_size>HOST_OUTPUT_LIMIT:reason='output_limit'
        closed=F.closed_group(child.pid)
        if not closed:closed=F.terminate_group(child.pid)
        code=child.wait(timeout=5)
    unchanged=F.sha(python)==row['python_sha256'] and all(F.sha(F.regular(path))==value
        for path,value in {**row['executed_producer_sha256'],**row['canonical_producer_sha256']}.items())
    row.update(status='completed' if code==0 and reason is None and closed and unchanged else 'failed',exit_code=code,
        timed_out=reason=='timeout',stop_reason=reason,process_group_closed=closed,
        producer_inputs_unchanged=unchanged,
        stdout_sha256=F.sha(log),stdout_bytes=log.stat().st_size,elapsed_seconds=time.monotonic()-start)
    write()
    F.require(code==0 and reason is None and closed and unchanged and
        0<log.stat().st_size<=HOST_OUTPUT_LIMIT,
        'Isolated selected-source regeneration failed: '+str(receipt))
    value=F.read(log);F.require(value.get('python')==str(python),'Regeneration Python identity differs')
    execution={key:row[key] for key in ('argv','python_sha256','exit_code','timed_out','process_group_closed','stdout_sha256','stdout_bytes')}
    execution['project_imports']={path:dict(module=name,sha256=F.sha(F.regular(path)))
        for path,name in value['project_imports'].items()}
    return value['modules'],value['identities'],value['project_imports'],execution


def derive(parent_path,*,validator_workspace=None):
    """Public calls remain cold outside the private invocation-local scope."""
    try:return _derive(parent_path,validator_workspace=validator_workspace)
    except BaseException:
        state=_HOST_BOUNDARY.get()
        if state is not None:
            state.update(failed=True,payload=None)
        raise


def _derive(parent_path,*,validator_workspace=None):
    """No caller-selected count: regenerate every actual positive source first."""
    F.check_native_environment()
    workspace=Path(validator_workspace).resolve() if validator_workspace is not None else ROOT
    canonical,executed=validator_context(workspace)
    parent_path=F.regular(Path(parent_path).resolve());parent=F.read(parent_path)
    F.require(parent.get('schema')=='pinwheel.streaming-tt-optimized-intake.v1' and
        parent.get('passed') is True and parent.get('qualified') is False and
        parent.get('source_commit')==parent.get('producer_commit') and
        re.fullmatch('[0-9a-f]{40}',parent.get('source_commit','')) and
        set(parent.get('checked',{}))==CHECKS and all(value is True for value in parent['checked'].values()),
        'Closed independently regenerated parent intake required')
    config_path=F.verify_bound(parent['worker_config']);config=F.read(config_path)
    worker_path=F.verify_bound(parent['worker_report']);worker=F.read(worker_path)
    raw_path=F.verify_bound(parent['raw_gate_report']);raw=F.read(raw_path)
    marker=config['fresh_foundation'];binding=F.read(F.verify_bound(marker))
    F.require(worker.get('fresh_foundation')==marker and binding['candidate_commit']==
        config['source_commit']==config['producer_commit']==parent['source_commit'] and
        Path(binding['candidate_root'])==Path(config['root']) and raw.get('passed') is True and
        raw.get('stage')=='components' and raw.get('source_commit')==raw.get('producer_commit')==parent['source_commit'],
        'Fresh replay source/binding/raw parent differs')
    F.verify_binding(binding);F.verify_staged(binding)
    source=Path(config['root']);source_map=raw['source_sha256']
    positive={'.lake/build/lib/lean/'+name:value for name,value in binding['positive_library_artifact_sha256'].items()}
    F.require(not source_map.keys()&positive.keys(),'Raw source archive overlaps retained positive library')
    expected_source={**source_map,**positive}
    F.require(F.manifest(source)==expected_source,'Complete selected source/library membership or bytes changed')
    scripts={str(source/name):value for name,value in source_map.items() if name.startswith('scripts/') and name.endswith('.py')}
    F.require(scripts and {str(path):F.sha(path) for path in (source/'scripts').rglob('*.py')}==scripts,
        'Complete selected Python script membership differs from raw archive')
    F.require(F.sha(F.__file__)==source_map.get('scripts/streaming_tt_fresh_foundation.py') and
        F.sha(F.regular(config['tools']['python']))==F.sha(F.regular(binding['python'])),
        'Actual validator foundation/Python producer differs')
    artifacts={str(worker_path.parent/name):value for name,value in F.manifest(worker_path.parent).items()
        if name!=worker_path.name}
    F.require(artifacts==worker['artifact_sha256'],'Closed parent worker artifact membership or bytes changed')
    plan_path=F.regular(parent_path.parent/'native-replay-plan.json')
    inputs={str(path):F.sha(path) for path in (parent_path,config_path,worker_path,raw_path,
        F.verify_bound(marker),plan_path,*canonical.values(),F.regular(config['tools']['python']))}
    inputs.update({str(source/name):value for name,value in expected_source.items()});inputs.update(artifacts)
    for path in [config['library'],worker['outer']['restored_json'],*(p for cfg in config['components'].values()
            for p in (cfg['raw_json'],cfg['sv'],*cfg['raw_sources'].values()))]:
        inputs[str(F.regular(path))]=F.sha(path)
    observation_base=workspace/'build/streaming-tt-replay-inventory'
    execution_root=Path(__file__).resolve().parents[1]
    F.require(not observation_base.is_relative_to(source) and not observation_base.is_relative_to(worker_path.parent) and
        (execution_root==workspace or not observation_base.is_relative_to(execution_root)),
        'Host regeneration observations would modify immutable producer/parent inputs')
    context=dict(parent=str(parent_path),workspace=str(workspace),input_sha256=inputs,
        executed_producer_sha256=executed,selected_source_sha256=expected_source,
        selected_script_sha256=scripts,worker_artifact_sha256=artifacts,
        host_environment={key:os.environ[key] for key in HOST_ENV_KEYS if key in os.environ})
    modules,identities,imports,execution=_regeneration_payload(context,
        dict(config_path=config_path,worker_path=worker_path,config=config,worker=worker,
            observation_base=observation_base,execution_producers=executed,
            canonical_producers={str(path):F.sha(path) for path in canonical.values()}))
    F.require(imports and all(path in scripts and F.sha(F.regular(path))==scripts[path] for path in imports),
        'Actual imported project source escaped the complete selected script closure')
    F.require(modules and len({row['module'] for row in modules})==len(modules) and
        all(set(row)=={'module','path','sha256'} and re.fullmatch('[A-Za-z_][A-Za-z0-9_]*',row['module'])
            for row in modules),'Regeneration omitted or duplicated module owners')
    stages=[]
    for row in modules:
        path=F.regular(row['path'])
        F.require(path.parent.parent==worker_path.parent and path.parent.name in STAGES and
            path.name==row['module']+'.lean' and F.sha(path)==row['sha256'],
            'Regenerated module source/stage/identity differs')
        stages.append(path.parent.name)
    F.require(stages==sorted(stages,key=STAGES.index) and set(stages)==set(STAGES),
        'Exact frontend/core/device source membership and order required')
    expected={row['path']:row['sha256'] for row in modules};plan=F.read(plan_path)
    F.require(identities==expected==parent.get('generated_sources_sha256') and
        type(parent.get('generated_module_count')) is int and parent['generated_module_count']==len(modules) and
        plan==dict(source_commit=parent['source_commit'],modules=modules),
        'Parent count/plan/source map differs from complete independent regeneration')
    F.verify_binding(binding);F.verify_staged(binding)
    F.require(F.manifest(source)==expected_source and
        {str(worker_path.parent/name):value for name,value in F.manifest(worker_path.parent).items()
            if name!=worker_path.name}==worker['artifact_sha256'] and
        all(F.sha(F.regular(path))==value for path,value in {**inputs,**expected,**executed}.items()),
        'Parent/regeneration inputs changed during exact inventory derivation')
    return dict(schema=PROFILE,parent_intake=F.bound(parent_path),source_commit=parent['source_commit'],
        native_replay_plan=F.bound(plan_path),module_count=len(modules),modules=modules,
        generated_sources_sha256=expected,input_sha256=inputs,validator_producer=F.bound(canonical['streaming_tt_replay_inventory.py']),
        regeneration_execution=execution)


def validate(replay,parent_path=None,modules=None,*,validator_workspace=None):
    """Keep the original392 profile strict; new cardinality requires regeneration."""
    profile=replay.get('replay_inventory_profile')
    if profile is None:
        F.require('exact_parent_inventory' not in replay,'Unmarked exact replay inventory')
        count=392
    else:
        F.require(profile==PROFILE and parent_path is not None,'Unknown/unbound fresh replay inventory profile')
        workspace=Path(validator_workspace).resolve() if validator_workspace is not None else ROOT
        F.require(replay.get('exact_parent_inventory',{}).get('validator_producer')==
            F.bound(workspace/'scripts/streaming_tt_replay_inventory.py'),
            'Replay canonical validator workspace/identity differs')
        expected=derive(parent_path,validator_workspace=workspace)
        F.require(replay.get('exact_parent_inventory')==expected,'Replay inventory differs from independent actual parent')
        if modules is None:
            modules=F.read(F.verify_bound(replay['regeneration_manifest']))['modules']
        F.require([(row['module'],row['sha256']) for row in modules]==
            [(row['module'],row['sha256']) for row in expected['modules']],
            'Replay module membership/order/source differs from independent parent')
        count=expected['module_count']
    keys=('module_count','regenerated_modules','positive_native_checks') if profile is not None else ('positive_native_checks',)
    F.require(all(type(replay.get(key)) is int and replay[key]==count for key in keys),
        'Native replay count differs from independently required inventory')
    return count
