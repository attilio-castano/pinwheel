"""New typed observer-state correction around immutable M isolation sources.

All operational barrier/compiler/private/readback functions are compiled into
a new namespace with the new PROCESS module. No old function globals mutate.
Historical Z attribution is inference: the old failed raw row was not retained.
"""
import ast
import difflib
import hashlib
from pathlib import Path
import sys
import types

import streaming_8x4_closure24_m_isolation as PREVIOUS
import streaming_8x4_closure24_m_process_state as PROCESS

ROOT=PREVIOUS.ROOT
OWN='scripts/streaming_8x4_closure24_m_state_isolation.py'
ENTRY='scripts/streaming_8x4_closure24_state_m_execute.py'
OBSERVER='scripts/streaming_8x4_closure24_m_process_state.py'
FROZEN_PROCESS_SOURCES={PREVIOUS.OWN:'e4ceeba1fe8a226ce09fa0edecef7264cbd2fb0b4095d1e84c6b3d26439443df',
    PREVIOUS.OBSERVER:'a91660cc21b3ef5f50c6e50aba4e58918d9bb9de7cafd97724f9f5a0d367bbad',
    PREVIOUS.ENTRY:'444a1f068157545e01c8728a504f948557c1214b2a0801e2cd2ce9f38dd10b47'}
need=PREVIOUS.need
replace_once=PREVIOUS.replace_once


def prior_sources():
    for name,pin in FROZEN_PROCESS_SOURCES.items():need(PREVIOUS.R.digest(ROOT/name)==pin,'Frozen previous M process producer changed')


def failure_binding():
    """Pure HOST custody; never turns the unreported object into proof."""
    b=ROOT/'build/campaigns/8x4-20261024-01';out=b/'final24-M-isolated-positive-01'
    resource=ROOT/'build/streaming-tt-resources/8x4-24-final-M-isolated-positive-01/report.json'
    report=PREVIOUS.R.read(out/'report.json');guard=PREVIOUS.R.read(resource)
    need(PREVIOUS.R.digest(out/'report.json')=='9d98e3e9c0b8e4ad80eae416fc10576f61b188f47b6c4cd7ba05656fa0ec36ef'and
        PREVIOUS.R.digest(resource)=='487f17560c9bbd67c081d75479f0562dbf7f8456f573256fabaa175a41d74c2e',
        'Exact failed observer attempt identities differ')
    need(report['passed']is False and report['status']=='failed-or-interrupted'and len(report['commands'])==25 and
        report['error']=='ValueError: Memory observer failed: ValueError: Observed executable path is not absolute'and
        guard['status']=='failed'and guard['exit_code']==1 and guard['cleanup_confirmed']is True and guard['inputs_unchanged']is True and
        guard['owned_processes_remaining']==guard['cleanup_errors']==[],'Old observer failure/cleanup scope differs')
    for path,pin in ((out/'native.jsonl','8df2fee8ef92696b22b1968b5cf948906b17bba6534ee28c843aefc2cbcfab55'),
        (out/'process-memory.jsonl','1c6e637f7025cdb1383f2d30b4c7bc023b550e083d0af05c6bc0cf72990d260e'),
        (resource.parent/'native.log','bb1f9e4a31c32bb170d9d9ee898190713d5082f981f6a8de293ce6ad7bdd6725')):
        need(PREVIOUS.R.digest(path)==pin,'Exact failed observer raw journal/log changed')
    rows=[PREVIOUS.R.json.loads(line)for line in(out/'native.jsonl').read_text().splitlines()]
    need(len(rows)==51 and rows[-1]['event']=='intent'and rows[-1]['index']==25 and rows[-1]['module']=='PhysicalFrontendWord25Values',
        'Original missing-result failure boundary changed')
    need(all(PREVIOUS.R.digest(p)==h for p,h in report['input_sha256'].items())and
        all(PREVIOUS.R.digest(p)==h for p,h in guard['input_sha256'].items()),'Old observer execution inputs changed')
    # Reopen the original completed derivation with its ORIGINAL code/PROCESS,
    # rather than reinterpret an old receipt through the new state schema.
    need(PREVIOUS.verify_rederive(report['rederivation_admission']['report']['path'],report['prepared']['path'])==report['rederivation_admission'],
        'Old completed derivation admission changed')
    receipts={name:PREVIOUS.bound(path)for name,path in dict(failed_report=out/'report.json',failed_resource=resource,
        native_journal=out/'native.jsonl',memory_journal=out/'process-memory.jsonl',
        child_report=out/'rederivation/report.json',child_process=out/'rederivation-process.json',
        child_memory=out/'rederivation-memory.jsonl').items()}
    unaccepted=Path(rows[-1]['argv'][rows[-1]['argv'].index('-o')+1])
    need(PREVIOUS.R.digest(unaccepted)=='f2ec2dd61f345ffe283077e702b29798c1a93509ff5365a6424c3237f6eac51e',
        'Retained unreported object changed; its existence is not a kernel verdict')
    receipts['unaccepted_last_intent_object']=PREVIOUS.bound(unaccepted)
    receipts['failed_resource_log']=PREVIOUS.bound(resource.parent/'native.log')
    return dict(schema='pinwheel.closure24-M-observer-state-failure-context.v1',receipts=receipts,
        original_failed_raw_ps_row_available=False,historical_Z_attribution_proven=False,
        old_successful_command_prefix=25,old_last_intent_index=25,old_last_intent_has_kernel_verdict=False,
        old_prefix_or_unreported_object_acceptance_reuse_allowed=False,physical_acceptance=False)


def compile_source():
    text=PREVIOUS.compile_source()
    # Keep the canonical Native result even when observational validation fails.
    # The observer error still fails the overall proof after that raw outcome is
    # durably recorded; no mathematical/compiler/resource requirement changes.
    text=replace_once(text,'        PROCESS.finish(memory_watch)\n        row.update(exit_code=code,',
        '        observer_error=None\n        try:PROCESS.finish(memory_watch)\n        except BaseException as error:observer_error=error\n        row.update(exit_code=code,')
    text=replace_once(text,"        'Actual-M native source/compiler/import/process boundary changed')\n    return row",
        "        'Actual-M native source/compiler/import/process boundary changed')\n    if observer_error is not None:raise observer_error\n    return row")
    return text


def body_source():
    prior_sources();original=(ROOT/PREVIOUS.OWN).read_text();text=original
    text=replace_once(text,'import streaming_8x4_closure24_m_process as PROCESS',
        'import streaming_8x4_closure24_m_process_state as PROCESS\nimport streaming_8x4_closure24_m_state_isolation as STATE')
    for old,new in (("OWN='"+PREVIOUS.OWN+"'","OWN='"+OWN+"'"),
        ("ENTRY='"+PREVIOUS.ENTRY+"'","ENTRY='"+ENTRY+"'"),
        ("OBSERVER='"+PREVIOUS.OBSERVER+"'","OBSERVER='"+OBSERVER+"'")):
        text=replace_once(text,old,new)
    text=replace_once(text,'def sources(*,committed=False,commit=None):','def sources(*,committed=False,commit=None):\n    STATE.prior_sources()')
    text=replace_once(text,'names=sorted(set((*M.SOURCES,OWN,ENTRY,OBSERVER,DIAGNOSTIC,',
        'names=sorted(set((*M.SOURCES,*STATE.FROZEN_PROCESS_SOURCES,OWN,ENTRY,OBSERVER,DIAGNOSTIC,')
    text=replace_once(text,'    result.update({row[\'source\']:row[\'source_sha256\']for row in manifest[\'m_rows\']})',
        "    result.update({item['path']:item['sha256']for item in STATE.failure_binding()['receipts'].values()})\n    result.update({row['source']:row['source_sha256']for row in manifest['m_rows']})")
    text=replace_once(text,'producer=producer,python=python_identity(),',
        'producer=producer,python=python_identity(),observer_correction_context=STATE.failure_binding(),')
    text=replace_once(text,'self_process=PROCESS.snapshot((os.getpid(),))[os.getpid()],',
        "self_process=PROCESS.snapshot((os.getpid(),),raw_path=output/'self-process-raw.jsonl',label='child-self')[os.getpid()],\n        self_process_raw=bound(output/'self-process-raw.jsonl'),")
    text=replace_once(text,"        child['source_worker_context']==record['source_worker_context'] and child['input_sha256']==input_seal(prepared,record,manifest,producer=producer) and",
        "        child['source_worker_context']==record['source_worker_context'] and child['input_sha256']==input_seal(prepared,record,manifest,producer=producer) and\n        child['observer_correction_context']==STATE.failure_binding() and")
    text=replace_once(text,"    need(PROCESS.lifetime(own)==observation['observations'][0]['child_lifetime'],'Child self-process birth/executable differs from outer observation')",
        "    need(child['self_process_raw']==bound(path.parent/'self-process-raw.jsonl'),'Child startup raw bytes changed')\n    PROCESS.verify_startup(child['self_process_raw']['path'],own,label='child-self')\n    need(PROCESS.lifetime(own)==observation['observations'][0]['child_lifetime'] and PROCESS.active_identity(own)==observation['observations'][0]['child_active_identity'],'Child self-process birth/executable differs from outer observation')")
    text=replace_once(text,"    need(PROCESS.lifetime(report['driver_process'])==summary['parent_lifetime'],'Driver actual startup identity differs from observations')",
        "    need(bound(report['driver_process_raw']['path'])==report['driver_process_raw'],'Driver startup raw bytes changed')\n    PROCESS.verify_startup(report['driver_process_raw']['path'],report['driver_process'],label='driver-startup')\n    need(PROCESS.lifetime(report['driver_process'])==summary['parent_lifetime'] and PROCESS.active_identity(report['driver_process'])==summary['parent_active_identity'],'Driver actual startup identity differs from observations')")
    need(text.count("ISOLATION.PROCESS.snapshot((os.getpid(),))[os.getpid()]")==2,'Exact positive/private startup anchors differ')
    text=text.replace("report['driver_process']=ISOLATION.PROCESS.snapshot((os.getpid(),))[os.getpid()]",
        "report['driver_process']=ISOLATION.PROCESS.snapshot((os.getpid(),),raw_path=output/'driver-process-raw.jsonl',label='driver-startup')[os.getpid()];report['driver_process_raw']=bound(output/'driver-process-raw.jsonl')")
    text=replace_once(text,'import streaming_8x4_closure24_m_isolation as ISOLATION',
        'import streaming_8x4_closure24_m_state_isolation as ISOLATION')
    for old,new in (('pinwheel.closure24-M-rederivation-child.v1','pinwheel.closure24-state-M-rederivation-child.v1'),
        ('pinwheel.closure24-M-rederivation-process.v1','pinwheel.closure24-state-M-rederivation-process.v1')):
        need(text.count(old)==2,'Exact old process schema anchors differ');text=text.replace(old,new)
    for old,new in (('pinwheel.closure24-isolated-actual-M-positive.v1','pinwheel.closure24-state-isolated-actual-M-positive.v1'),
        ('pinwheel.closure24-isolated-actual-M-private.v1','pinwheel.closure24-state-isolated-actual-M-private.v1')):
        text=replace_once(text,old,new)
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-isolation/helper',tofile='state-observer/helper'))


def load_body(name,path):
    text,diff=body_source();module=types.ModuleType(name+'.state_observer_body');module.__file__=str(Path(path).resolve())
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::state-observer-context','exec'),module.__dict__)
    module.compile_source=compile_source;module.STATE_ADAPTATION_DIFF=diff;return module


_body=load_body(__name__,__file__)
globals().update({name:value for name,value in vars(_body).items()if not name.startswith('__')})
