"""Fresh complete-M execution, typed joins and isolated private audit factory."""
import difflib
from pathlib import Path
import sys
import types

import streaming_8x4_closure24_m_codec_isolation as PREVIOUS
import streaming_8x4_closure24_m_typed_join as TYPED_JOIN
import streaming_8x4_closure24_join_m as M

ROOT=PREVIOUS.ROOT
OWN=TYPED_JOIN.ISOLATION
ENTRY=TYPED_JOIN.EXECUTION
OBSERVER=PREVIOUS.OBSERVER
FROZEN_PROCESS_SOURCES={**PREVIOUS.FROZEN_PROCESS_SOURCES,
    PREVIOUS.OWN:'089f36b8b3eeb51b29457f439d1b77a63f4e6126aa0164440495148cc9fbfd81',
    PREVIOUS.ENTRY:'9bb15efbd5fb6471af61a9431c5926baba6ccb9f1e28d90d1e31c487fb23b658'}
need=PREVIOUS.need
replace_once=PREVIOUS.replace_once


def prior_sources():
    TYPED_JOIN.prior_sources()
    for name,pin in FROZEN_PROCESS_SOURCES.items():need(PREVIOUS.R.digest(ROOT/name)==pin,'Frozen Codec execution producer changed')


def failure_binding():
    # Provenance is hash-only. Real acceptance never loads old Native graphs or
    # diagnostic objects, and only the fresh actual3966 owner enters LEAN_PATH.
    previous=PREVIOUS.failure_binding();b=ROOT/'build/campaigns/8x4-20261024-01';g=ROOT/'build/streaming-tt-resources'
    pins={b/'typed-join-tail-diagnostic-08/report.json':'e706cedcf950ea54ef6978e20a1f0ac18b0a81788fc89ac2bff4074ff7bb3708',
        g/'8x4-24-typed-join-tail-diagnostic-08/report.json':'fc0254f535cdc064ba1a9cb5e75d232d7e913d4afdc8f1e2d26d023a16ab268b',
        b/'typed-join-tail-diagnostic-09/report.json':'f6a80436eff0ee289bb0ee613594c0e460a17ec8244c15972cc071cbeca6962b',
        g/'8x4-24-typed-join-tail-diagnostic-09/report.json':'65417dbf69758dc99cc49593e6be52090b7c8dca94b4700012ff0cbc53ce870e',
        b/'audit-owner-chunk-control-01/report.json':'69bf5e631853b9cd209b7e1f82f559ddb61b0aa0154ec04dd43a5353b30d5b02',
        g/'8x4-24-audit-owner-chunk-control-01/report.json':'fe612b9cd0ac17e741a3e970146b516d5f4c137688d7e3989531005185fb2d68'}
    for path,pin in pins.items():need(PREVIOUS.R.digest(path)==pin,'Typed-join/audit diagnostic provenance changed')
    receipts=dict(previous['receipts']);receipts.update({'typed_join_diagnostic_'+str(i):PREVIOUS.bound(path)for i,path in enumerate(sorted(pins))})
    return dict(schema='pinwheel.closure24-M-typed-join-diagnostic-context.v1',receipts=receipts,
        old_prefix_acceptance_reuse_allowed=False,diagnostic_objects_as_acceptance_imports=False,
        full_fresh_positive_and_real_private_controls_required=True,old_full_proof_passed=False,physical_acceptance=False)


def budget_policy():
    policy=dict(PREVIOUS.budget_policy())
    policy.update(schema='pinwheel.closure24-typed-join-M-native-budget.v1',mathematical_statements_domains_unchanged=False,
        original_TypedJoin_public_header_text_unchanged=False,full_state_and_input_domains_unchanged=True,
        full_function_width_polymorphism=True,all_other_public_statements_unchanged=True,
        typed_join_observe_proofs_changed=True,actual_pad_proof_parentheses_changed=True,
        positive_and_private_audit_data_representation_changed=True,audit_predicate_owners_axioms_unchanged=True)
    return policy


def compile_source():return PREVIOUS.compile_source()


def controller_source():
    original,_=PREVIOUS.controller_source();text=original
    text=replace_once(text,'import streaming_8x4_closure24_codec_m as M','import streaming_8x4_closure24_join_m as M')
    text=replace_once(text,'import streaming_8x4_closure24_m_codec_isolation as ISOLATION',
        'import streaming_8x4_closure24_m_join_isolation as ISOLATION')
    text=replace_once(text,'from streaming_mapped_campaign import audit_source',
        'import streaming_8x4_closure24_m_typed_join as TYPED_JOIN\naudit_source = TYPED_JOIN.audit_source')
    text=replace_once(text,'private_texts = ORIGINAL.private_texts',
        'private_texts = TYPED_JOIN.private_factory(ORIGINAL.private_texts, audit_source)')
    text=text.replace('pinwheel.closure24-codec-index-isolated-actual-M-','pinwheel.closure24-typed-join-isolated-actual-M-')
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-Codec/execution',tofile='typed-join/execution'))


def body_source():
    prior_sources();original,_=PREVIOUS.body_source();text=original
    text=replace_once(text,'import streaming_8x4_closure24_codec_m as M','import streaming_8x4_closure24_join_m as M')
    text=replace_once(text,'import streaming_8x4_closure24_m_codec_isolation as CODEC_CONTEXT',
        'import streaming_8x4_closure24_m_join_isolation as JOIN_CONTEXT')
    text=text.replace('CODEC_CONTEXT.prior_sources()','JOIN_CONTEXT.prior_sources()').replace('CODEC_CONTEXT.FROZEN_PROCESS_SOURCES','JOIN_CONTEXT.FROZEN_PROCESS_SOURCES')
    text=text.replace('CODEC_CONTEXT.failure_binding()','JOIN_CONTEXT.failure_binding()')
    for old,new in ((PREVIOUS.OWN,OWN),(PREVIOUS.ENTRY,ENTRY)):text=replace_once(text,"'"+old+"'","'"+new+"'")
    text=text.replace('pinwheel.closure24-codec-index-M-','pinwheel.closure24-typed-join-M-')
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-Codec/process',tofile='typed-join/process'))


def load_body(name,path):
    text,diff=body_source();module=types.ModuleType(name+'.typed_join_isolation');module.__file__=str(Path(path).resolve())
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::typed-join-context','exec'),module.__dict__)
    module.compile_source=compile_source;module.controller_source=controller_source;module.TYPED_JOIN_PROCESS_DIFF=diff
    return module


_body=load_body(__name__,__file__)
globals().update({name:value for name,value in vars(_body).items()if not name.startswith('__')})
