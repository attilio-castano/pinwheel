"""New complete-M execution context for index-only Codec proof chunking."""
import difflib
from pathlib import Path
import sys
import types

import streaming_8x4_closure24_m_finite_isolation as PREVIOUS
import streaming_8x4_closure24_m_codec_index as CODEC_INDEX
import streaming_8x4_closure24_codec_m as M

ROOT=PREVIOUS.ROOT
OWN=CODEC_INDEX.ISOLATION
ENTRY=CODEC_INDEX.EXECUTION
OBSERVER=PREVIOUS.OBSERVER
FROZEN_PROCESS_SOURCES={**PREVIOUS.FROZEN_PROCESS_SOURCES,
    PREVIOUS.OWN:'759bbe6c2d83424ffab29821785c472da860a877e6101abcded96fc47fef8a09',
    PREVIOUS.ENTRY:'6bdddebd9d64a623cbf9363744623a2b65c5a94f2e692bf1b3061acb9a387958',
    PREVIOUS.OBSERVER:'f23e47ac0b4089fdf98c5778cc34920597efcb3eb7aa65d4e2e753b97266b1d0'}
need=PREVIOUS.need
replace_once=PREVIOUS.replace_once


def prior_sources():
    for name,pin in FROZEN_PROCESS_SOURCES.items():need(PREVIOUS.R.digest(ROOT/name)==pin,'Frozen finite execution producer changed')


def failure_binding():
    previous=PREVIOUS.failure_binding();b=ROOT/'build/campaigns/8x4-20261024-01'
    out=b/'final24-M-finite-transport-positive-01';guard=ROOT/'build/streaming-tt-resources/8x4-24-final-M-finite-transport-positive-01/report.json'
    pins={out/'report.json':'0c182758fb47d062ecd25ebcee4d3cf9008c07d06fee4e745cae18a86c430c2f',
        guard:'2f52a78048e984446794e0dd4277a9cd79c3cdd0765569b9a10e30a5fe2b7f4f',
        out/'PhysicalStateCodec.log':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'}
    for path,pin in pins.items():need(PREVIOUS.R.digest(path)==pin,'Original Codec memory failure bytes changed')
    # Large Native report stays hash-only in the compiler parent. No historical
    # proof prefix, old verifier, or regenerated graph is an acceptance input.
    resource=PREVIOUS.R.read(guard)
    need(resource['status']=='stopped'and resource['exit_code']==124 and resource['cleanup_confirmed']is True and
        resource['inputs_unchanged']is True and resource['owned_processes_remaining']==resource['cleanup_errors']==[],
        'Original Codec memory stop/cleanup differs')
    need(all(PREVIOUS.R.digest(path)==pin for path,pin in resource['input_sha256'].items()),'Codec memory-failure input changed')
    receipts=dict(previous['receipts']);receipts.update({'codec_memory_failure_'+str(i):PREVIOUS.bound(path)for i,path in enumerate(sorted(pins))})
    return dict(schema='pinwheel.closure24-M-codec-memory-failure-context.v1',receipts=receipts,
        failed_module='PhysicalStateCodec',failed_index=3466,old_stop='aggregate_owned_RSS_exceeded_4GiB',
        old_prefix_acceptance_reuse_allowed=False,old_full_proof_passed=False,physical_acceptance=False)


def budget_policy():
    policy=dict(PREVIOUS.budget_policy())
    policy.update(schema='pinwheel.closure24-codec-index-M-native-budget.v1',mathematical_statements_domains_chunks_unchanged=False,
        mathematical_statements_domains_unchanged=True,original_seven_finite_chunk_domains_unchanged=True,
        codec_index_proof_chunked=True)
    return policy


def compile_source():return PREVIOUS.compile_source()


def controller_source():
    original,_=PREVIOUS.controller_source();text=original
    text=replace_once(text,'import streaming_8x4_closure24_finite_m as M','import streaming_8x4_closure24_codec_m as M')
    text=replace_once(text,'import streaming_8x4_closure24_m_finite_isolation as ISOLATION',
        'import streaming_8x4_closure24_m_codec_isolation as ISOLATION')
    text=text.replace('pinwheel.closure24-finite-isolated-actual-M-','pinwheel.closure24-codec-index-isolated-actual-M-')
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-finite/execution',tofile='codec-index/execution'))


def body_source():
    prior_sources();original,_=PREVIOUS.body_source();text=original
    text=replace_once(text,'import streaming_8x4_closure24_finite_m as M','import streaming_8x4_closure24_codec_m as M')
    text=replace_once(text,'import streaming_8x4_closure24_m_finite_isolation as FINITE_CONTEXT',
        'import streaming_8x4_closure24_m_codec_isolation as CODEC_CONTEXT')
    text=text.replace('FINITE_CONTEXT.prior_sources()','CODEC_CONTEXT.prior_sources()').replace('FINITE_CONTEXT.FROZEN_PROCESS_SOURCES','CODEC_CONTEXT.FROZEN_PROCESS_SOURCES')
    text=text.replace('FINITE_CONTEXT.failure_binding()','CODEC_CONTEXT.failure_binding()')
    for old,new in ((PREVIOUS.OWN,OWN),(PREVIOUS.ENTRY,ENTRY)):text=replace_once(text,"'"+old+"'","'"+new+"'")
    text=text.replace('pinwheel.closure24-finite-M-','pinwheel.closure24-codec-index-M-')
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-finite/process',tofile='codec-index/process'))


def load_body(name,path):
    text,diff=body_source();module=types.ModuleType(name+'.codec_index_isolation');module.__file__=str(Path(path).resolve())
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::codec-index-context','exec'),module.__dict__)
    module.compile_source=compile_source;module.controller_source=controller_source;module.CODEC_PROCESS_DIFF=diff
    return module


_body=load_body(__name__,__file__)
globals().update({name:value for name,value in vars(_body).items()if not name.startswith('__')})
