"""Fresh typed M execution context for missing Darwin ps argument metadata.

The immutable state-aware operational body is compiled into this namespace.
Historical failure custody is lightweight: it never recursively regenerates or
reopens previous logical admissions inside the compiler parent.
"""
import difflib
from pathlib import Path
import sys
import types

import streaming_8x4_closure24_m_state_isolation as DERIVATION
import streaming_8x4_closure24_m_process_comm as PROCESS

ROOT=DERIVATION.ROOT
OWN='scripts/streaming_8x4_closure24_m_comm_isolation.py'
ENTRY='scripts/streaming_8x4_closure24_comm_m_execute.py'
OBSERVER='scripts/streaming_8x4_closure24_m_process_comm.py'
FROZEN_PROCESS_SOURCES={**DERIVATION.FROZEN_PROCESS_SOURCES,
    DERIVATION.OWN:'f0e38bcc05859a64d3070990efcd90e8c5857a24285adad4e487a2bcbb477f9d',
    DERIVATION.ENTRY:'f79caf829d52b0cb10cecaceeb41f82a0427db1e96d8c33201428ff5b617176f',
    DERIVATION.OBSERVER:'d232c9a84d56a084946695b5f40477c64682e6114f04e9f4f4faf4a65f5edde4'}
need=DERIVATION.need
replace_once=DERIVATION.replace_once


def prior_sources():
    for name,pin in FROZEN_PROCESS_SOURCES.items():
        need(DERIVATION.R.digest(ROOT/name)==pin,'Frozen previous M process producer changed')


def failure_binding():
    """Exact historical custody only; no old verifier callbacks or proof reuse."""
    r=DERIVATION.R;b=ROOT/'build/campaigns/8x4-20261024-01';out=b/'final24-M-lifecycle-positive-01'
    resource=ROOT/'build/streaming-tt-resources/8x4-24-final-M-lifecycle-positive-01/report.json'
    pins={out/'report.json':'d34d8e7567db1b52dea8fdc39d963bb4df204cb9a40c0892cf7c347ec24e39b1',
        resource:'5d723e43fc326ec032f25900efd9356e21d6e881ed93a9d0c893bac1aa6f6fed',
        out/'native.jsonl':'8f0b3b377198c93878816e1609a9aa2a982f6929d3edb0121023f719959f206d',
        out/'process-memory.jsonl':'4813b218e139c33f2a6f8ff65ccb80ad061d1f835c45d1b1bcb55d80a206e1b2',
        out/'rederivation/report.json':'7e613ff9d2064b57a44867005d86736afe837f7b7c78fffb17c3d2df6bce466a',
        out/'rederivation-process.json':'3701201e9444ee049dd576743ec8df1363264113bcd04519503865ed1cf0397f',
        out/'rederivation-memory.jsonl':'a420446d22c2c811e257e220c19626e86a0dd51be677c274ad46a266bb3da491',
        resource.parent/'native.log':'07fe4a3127e24f84934d5bba1cf987eab959f1304d3c262c00844fef46677c82',
        b/'m-observer-comm-source-02/manifest.json':'287d39fa650a25d39fc696488f0516a692efd7bd3343ad8b3781ba6cccf16a35'}
    for path,pin in pins.items():need(r.digest(path)==pin,'Historical comm failure/primary source bytes changed')
    report=r.read(out/'report.json');guard=r.read(resource);child=r.read(out/'rederivation/report.json')
    need(report['passed']is False and report['status']=='failed-or-interrupted'and len(report['commands'])==25 and
        report['error']=='ValueError: State memory observer failed: ValueError: Observed LIVE executable path is not absolute'and
        guard['status']=='failed'and guard['exit_code']==1 and guard['cleanup_confirmed']is True and guard['inputs_unchanged']is True and
        guard['owned_processes_remaining']==guard['cleanup_errors']==[] and child['passed']is True,
        'Historical comm failure/cleanup scope changed')
    # Exact original maps preserve source/input custody without retaining prior
    # M.verify(False) graphs or calling any old verify_rederive recursively.
    for receipt in (report,guard,child):
        need(bool(receipt['input_sha256'])and all(r.digest(p)==h for p,h in receipt['input_sha256'].items()),
            'Historical comm failure inputs changed')
    rows=[r.json.loads(line)for line in(out/'native.jsonl').read_text().splitlines()]
    need(len(rows)==52 and rows[-2]['event']=='intent'and rows[-1]['event']=='result'and
        rows[-1]['index']==25 and rows[-1]['module']=='PhysicalFrontendWord25Values'and
        rows[-1]['exit_code']==0 and rows[-1]['native_process_group_closed']is True,
        'Retained canonical exit-zero boundary changed')
    memory=[r.json.loads(line)for line in(out/'process-memory.jsonl').read_text().splitlines()]
    raw=[v for v in memory if v['event']=='ps-raw'][-1]
    need(raw['returncode']==0 and raw['stderr']==''and raw['stdout'].splitlines()[-1].split()[9:]==['Rs','(lean)'],
        'Actual LIVE comm-fallback witness changed')
    primary=r.read(b/'m-observer-comm-source-02/manifest.json')
    need(primary['source_to_installed_binary_equivalence_proven']is False and len(primary['files'])==3,
        'Primary source scope changed')
    need(r.digest('/bin/ps')==primary['host_ps_sha256'],'Actual ps executable changed')
    pins[Path('/bin/ps')]=primary['host_ps_sha256']
    for name,row in primary['files'].items():
        path=b/'m-observer-comm-source-02'/name
        need(r.digest(path)==row['sha256']and row['computed_git_blob']==row['observed_git_blob'],'Primary source identity changed')
        pins[path]=row['sha256']
    return dict(schema='pinwheel.closure24-M-comm-failure-context.v1',
        receipts={str(i):DERIVATION.bound(path)for i,path in enumerate(sorted(pins))},
        actual_live_comm_fallback_observed=True,actual_last_native_exit_code=0,
        historical_missing_raw_Z_cause_proven=False,source_to_installed_ps_equivalence_proven=False,
        old_prefix_acceptance_reuse_allowed=False,old_full_proof_passed=False,physical_acceptance=False)


def compile_source():return DERIVATION.compile_source()


def body_source():
    prior_sources();original,_=DERIVATION.body_source();text=original
    text=replace_once(text,'import streaming_8x4_closure24_m_process_state as PROCESS',
        'import streaming_8x4_closure24_m_process_comm as PROCESS')
    text=replace_once(text,'import streaming_8x4_closure24_m_state_isolation as STATE',
        'import streaming_8x4_closure24_m_comm_isolation as COMM')
    text=text.replace('STATE.prior_sources()','COMM.prior_sources()').replace('STATE.FROZEN_PROCESS_SOURCES','COMM.FROZEN_PROCESS_SOURCES')
    text=text.replace('STATE.failure_binding()','COMM.failure_binding()')
    for old,new in ((DERIVATION.OWN,OWN),(DERIVATION.ENTRY,ENTRY),(DERIVATION.OBSERVER,OBSERVER)):
        text=replace_once(text,"'"+old+"'","'"+new+"'")
    text=replace_once(text,'import streaming_8x4_closure24_m_state_isolation as ISOLATION',
        'import streaming_8x4_closure24_m_comm_isolation as ISOLATION')
    text=text.replace('pinwheel.closure24-state-M-rederivation-child.v1','pinwheel.closure24-comm-M-rederivation-child.v1')
    text=text.replace('pinwheel.closure24-state-M-rederivation-process.v1','pinwheel.closure24-comm-M-rederivation-process.v1')
    text=text.replace('pinwheel.closure24-state-isolated-actual-M-positive.v1','pinwheel.closure24-comm-isolated-actual-M-positive.v1')
    text=text.replace('pinwheel.closure24-state-isolated-actual-M-private.v1','pinwheel.closure24-comm-isolated-actual-M-private.v1')
    need('STATE.'not in text,'Old state callback context leaked')
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-state/helper',tofile='comm-metadata/helper'))


def load_body(name,path):
    text,diff=body_source();module=types.ModuleType(name+'.comm_observer_body');module.__file__=str(Path(path).resolve())
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::comm-observer-context','exec'),module.__dict__)
    module.compile_source=compile_source;module.COMM_ADAPTATION_DIFF=diff;return module


_body=load_body(__name__,__file__)
globals().update({name:value for name,value in vars(_body).items()if not name.startswith('__')})
