"""New typed opaque-observer full-M execution around finite transport repair."""
import difflib
from pathlib import Path
import sys
import types

import streaming_8x4_closure24_m_ps_isolation as PREVIOUS
import streaming_8x4_closure24_m_finite_transport as TRANSPORT
import streaming_8x4_closure24_finite_m as M

ROOT=PREVIOUS.ROOT
OWN=TRANSPORT.ISOLATION
ENTRY=TRANSPORT.EXECUTION
OBSERVER=PREVIOUS.OBSERVER
FROZEN_PROCESS_SOURCES={**PREVIOUS.FROZEN_PROCESS_SOURCES,
    PREVIOUS.OWN:'4957895590a89c498985be507f67006970b6f5ff790f5b510c9c6d6ad1c43957',
    PREVIOUS.ENTRY:'15512e05c14970fbc345beba5dee27675d0b5f3fd119dee05a5f36b2218e48a7',
    PREVIOUS.OBSERVER:'f23e47ac0b4089fdf98c5778cc34920597efcb3eb7aa65d4e2e753b97266b1d0'}
need=PREVIOUS.need
replace_once=PREVIOUS.replace_once


def prior_sources():
    for name,pin in FROZEN_PROCESS_SOURCES.items():need(PREVIOUS.R.digest(ROOT/name)==pin,'Frozen opaque producer changed')


def failure_binding():
    """Hash-only custody of the large failed proof, never parent graph reuse."""
    previous=PREVIOUS.failure_binding();b=ROOT/'build/campaigns/8x4-20261024-01'
    out=b/'final24-M-opaque-state-positive-01';guard=ROOT/'build/streaming-tt-resources/8x4-24-final-M-opaque-state-positive-01/report.json'
    pins={out/'report.json':'66b1910b8c9e96955febfd6040650af0fd05b0f6afe39b8797811bf2b352a8a1',
        out/'PhysicalGRTCanonicalDevice.log':'bda288e00beef0b3247d90e5a6f64164abcfc19672cfe19f41f8142334e0fc2a',
        out/'native.jsonl':'08e64cd7528c3130bcbcf3c3bb493f2e9fa4d8203b02953b06bd32922bd9a196',
        guard:'69bb242ef14d7ca1754d6637200687e0f929aabd90128e54b74e1f62ad1a723b'}
    for path,pin in pins.items():need(PREVIOUS.R.digest(path)==pin,'Original finite transport failure changed')
    resource=PREVIOUS.R.read(guard)
    need(resource['status']=='failed'and resource['exit_code']==1 and resource['cleanup_confirmed']is True and
        resource['inputs_unchanged']is True and resource['owned_processes_remaining']==resource['cleanup_errors']==[],
        'Finite transport failure resource scope differs')
    need(all(PREVIOUS.R.digest(path)==pin for path,pin in resource['input_sha256'].items()),'Finite failure current source inputs changed')
    receipts=dict(previous['receipts']);receipts.update({'finite_failure_'+str(i):PREVIOUS.bound(path)for i,path in enumerate(sorted(pins))})
    return dict(schema='pinwheel.closure24-M-finite-failure-context.v1',receipts=receipts,
        failed_module='PhysicalGRTCanonicalDevice',failed_index=3463,failed_exit_code=1,
        old_prefix_acceptance_reuse_allowed=False,old_full_proof_passed=False,physical_acceptance=False)


def budget_policy():
    policy=dict(PREVIOUS.PRIOR.budget_policy())
    policy.update(schema='pinwheel.closure24-finite-M-native-budget.v1',mathematical_sources_unchanged=False,
        mathematical_statements_domains_chunks_unchanged=True,proof_transport_tactics_changed=True)
    return policy


def compile_source():return PREVIOUS.compile_source()


def controller_source():
    original,_=PREVIOUS.controller_source();text=original
    text=replace_once(text,'import streaming_8x4_closure24_scope_m as M','import streaming_8x4_closure24_finite_m as M')
    text=replace_once(text,'import streaming_8x4_closure24_m_ps_isolation as ISOLATION',
        'import streaming_8x4_closure24_m_finite_isolation as ISOLATION')
    text=replace_once(text,'budget_policy = ORIGINAL.budget_policy','budget_policy = ISOLATION.budget_policy')
    text=text.replace('pinwheel.closure24-opaque-isolated-actual-M-','pinwheel.closure24-finite-isolated-actual-M-')
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-opaque/execution',tofile='finite-transport/execution'))


def body_source():
    prior_sources();original,_=PREVIOUS.body_source();text=original
    text=replace_once(text,'import streaming_8x4_closure24_scope_m as M','import streaming_8x4_closure24_finite_m as M')
    text=replace_once(text,'import streaming_8x4_closure24_m_ps_isolation as OPAQUE',
        'import streaming_8x4_closure24_m_finite_isolation as FINITE_CONTEXT')
    text=text.replace('OPAQUE.prior_sources()','FINITE_CONTEXT.prior_sources()').replace('OPAQUE.FROZEN_PROCESS_SOURCES','FINITE_CONTEXT.FROZEN_PROCESS_SOURCES')
    text=text.replace('OPAQUE.failure_binding()','FINITE_CONTEXT.failure_binding()')
    for old,new in ((PREVIOUS.OWN,OWN),(PREVIOUS.ENTRY,ENTRY)):text=replace_once(text,"'"+old+"'","'"+new+"'")
    text=text.replace('pinwheel.closure24-opaque-M-','pinwheel.closure24-finite-M-')
    # The complete old load_controller function resolves this module's NEW
    # controller_source at invocation, not the original helper's globals.
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-opaque/process',tofile='finite-transport/process'))


def load_body(name,path):
    text,diff=body_source();module=types.ModuleType(name+'.finite_isolation_body');module.__file__=str(Path(path).resolve())
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::finite-context','exec'),module.__dict__)
    module.compile_source=compile_source;module.controller_source=controller_source;module.FINITE_PROCESS_DIFF=diff
    return module


_body=load_body(__name__,__file__)
globals().update({name:value for name,value in vars(_body).items()if not name.startswith('__')})
