"""Fresh typed M execution context for opaque Darwin ps scheduling state.

The immutable state-aware operational body is compiled into this namespace.
Historical failure custody is lightweight: it never recursively regenerates or
reopens previous logical admissions inside the compiler parent.
"""
import difflib
from pathlib import Path
import sys
import types

import streaming_8x4_closure24_m_comm_isolation as DERIVATION
import streaming_8x4_closure24_m_process_ps as PROCESS

ROOT=DERIVATION.ROOT
OWN='scripts/streaming_8x4_closure24_m_ps_isolation.py'
ENTRY='scripts/streaming_8x4_closure24_ps_m_execute.py'
OBSERVER='scripts/streaming_8x4_closure24_m_process_ps.py'
FROZEN_PROCESS_SOURCES={**DERIVATION.FROZEN_PROCESS_SOURCES,
    DERIVATION.OWN:'cb9c8c7c3167678c88e43b77460c3ff83a38dab23fb8a058045747bbc57eb5cc',
    DERIVATION.ENTRY:'63018f5390fc4b8cc90b24f1b77e4c86cd4434d950286249725366c13f615e2c',
    DERIVATION.OBSERVER:'b000aea7520bdd704c8cb95d923caf9541029478a49d693ac622ade5f6573138'}
need=DERIVATION.need
replace_once=DERIVATION.replace_once


def prior_sources():
    for name,pin in FROZEN_PROCESS_SOURCES.items():
        need(DERIVATION.R.digest(ROOT/name)==pin,'Frozen previous M process producer changed')


def failure_binding():
    """Exact historical custody only; no old verifier callbacks or proof reuse."""
    r=DERIVATION.R;b=ROOT/'build/campaigns/8x4-20261024-01';out=b/'final24-M-ps-argv-positive-01'
    resource=ROOT/'build/streaming-tt-resources/8x4-24-final-M-ps-argv-positive-01/report.json'
    pins={out/'report.json':'21b5562c474dcb146c587527bbe81bd85591935e3e9355123db5d7b4d80dfbfb',
        resource:'1ff419e6f80549ce5e2765a606a3b0fc5b6ff16cd6764f786159d2025c9e7a44',
        out/'native.jsonl':'602c1517c02bf9af4d65dd3007e499b86df858cd700d3c4c60b0439a63c5f146',
        out/'process-memory.jsonl':'79bdd251c0d63a51b2f69751995d99ded497f280cac65a563e6267108d9a3602',
        out/'rederivation/report.json':'511f859f000977cf2ee1cf8b01a1a821102c7435a59a0129590ea3f1d01a8820',
        out/'rederivation-process.json':'b0ae23c7ea9f2e5486852f3e4d127b671e6e34ae75c50f7d2278d81b08a5dcaf',
        out/'rederivation-memory.jsonl':'ce61136531ac7dcd135dabacb0e6cc66c8970a9e03c106aee6c23ff188025599',
        resource.parent/'native.log':'56334effabb3731c64b1cce5e090de78b8568744964a2c7bd9110b33b0481ac9',
        b/'m-observer-comm-source-02/manifest.json':'287d39fa650a25d39fc696488f0516a692efd7bd3343ad8b3781ba6cccf16a35',
        b/'m-observer-comm-source-03/manifest.json':'4fa092b43ab6465347ad1feef9d7f3651f69032a7847b310dfdb06979bde9a56'}
    for path,pin in pins.items():need(r.digest(path)==pin,'Historical comm failure/primary source bytes changed')
    report=r.read(out/'report.json');guard=r.read(resource);child=r.read(out/'rederivation/report.json')
    need(report['passed']is False and report['status']=='failed-or-interrupted'and len(report['commands'])==2 and
        report['error']=='ValueError: Command-metadata memory observer failed: ValueError: Unexpected PID/RSS/state observation'and
        guard['status']=='failed'and guard['exit_code']==1 and guard['cleanup_confirmed']is True and guard['inputs_unchanged']is True and
        guard['owned_processes_remaining']==guard['cleanup_errors']==[] and child['passed']is True,
        'Historical comm failure/cleanup scope changed')
    # Exact original maps preserve source/input custody without retaining prior
    # M.verify(False) graphs or calling any old verify_rederive recursively.
    for receipt in (report,guard,child):
        need(bool(receipt['input_sha256'])and all(r.digest(p)==h for p,h in receipt['input_sha256'].items()),
            'Historical comm failure inputs changed')
    rows=[r.json.loads(line)for line in(out/'native.jsonl').read_text().splitlines()]
    need(len(rows)==6 and rows[-2]['event']=='intent'and rows[-1]['event']=='result'and
        rows[-1]['index']==2 and rows[-1]['module']=='PhysicalFrontendWord2Values'and
        rows[-1]['exit_code']==0 and rows[-1]['native_process_group_closed']is True,
        'Retained canonical exit-zero boundary changed')
    memory=[r.json.loads(line)for line in(out/'process-memory.jsonl').read_text().splitlines()]
    raw=[v for v in memory if v['event']=='ps-raw'][-1]
    need(raw['returncode']==0 and raw['stderr']==''and raw['stdout'].splitlines()[-1].split()[9:]==['?Es','(lean)'],
        'Actual LIVE comm-fallback witness changed')
    primary=r.read(b/'m-observer-comm-source-03/manifest.json')
    need(primary['source_to_installed_binary_equivalence_proven']is False and len(primary['files'])==4,
        'Primary source scope changed')
    need(r.digest('/bin/ps')==primary['host_ps_sha256'],'Actual ps executable changed')
    pins[Path('/bin/ps')]=primary['host_ps_sha256']
    for name,row in primary['files'].items():
        path=b/'m-observer-comm-source-03'/name
        need(r.digest(path)==row['sha256']and row['computed_git_blob']==row['observed_git_blob'],'Primary source identity changed')
        pins[path]=row['sha256']
    return dict(schema='pinwheel.closure24-M-opaque-state-failure-context.v1',
        receipts={str(i):DERIVATION.bound(path)for i,path in enumerate(sorted(pins))},
        actual_opaque_state_comm_fallback_observed=True,actual_last_native_exit_code=0,
        historical_missing_raw_Z_cause_proven=False,source_to_installed_ps_equivalence_proven=False,
        old_prefix_acceptance_reuse_allowed=False,old_full_proof_passed=False,physical_acceptance=False)


def compile_source():return DERIVATION.compile_source()


def body_source():
    prior_sources();original,_=DERIVATION.body_source();text=original
    text=replace_once(text,'import streaming_8x4_closure24_m_process_comm as PROCESS',
        'import streaming_8x4_closure24_m_process_ps as PROCESS')
    text=replace_once(text,'import streaming_8x4_closure24_m_comm_isolation as COMM',
        'import streaming_8x4_closure24_m_ps_isolation as OPAQUE')
    text=text.replace('COMM.prior_sources()','OPAQUE.prior_sources()').replace('COMM.FROZEN_PROCESS_SOURCES','OPAQUE.FROZEN_PROCESS_SOURCES')
    text=text.replace('COMM.failure_binding()','OPAQUE.failure_binding()')
    for old,new in ((DERIVATION.OWN,OWN),(DERIVATION.ENTRY,ENTRY),(DERIVATION.OBSERVER,OBSERVER)):
        text=replace_once(text,"'"+old+"'","'"+new+"'")
    text=replace_once(text,'import streaming_8x4_closure24_m_comm_isolation as ISOLATION',
        'import streaming_8x4_closure24_m_ps_isolation as ISOLATION')
    text=text.replace('pinwheel.closure24-comm-M-','pinwheel.closure24-opaque-M-')
    text=text.replace('pinwheel.closure24-comm-isolated-','pinwheel.closure24-opaque-isolated-')
    need('COMM.'not in text,'Old comm callback context leaked')
    return text,''.join(difflib.unified_diff(original.splitlines(True),text.splitlines(True),fromfile='immutable-comm/helper',tofile='opaque-state/helper'))


def load_body(name,path):
    text,diff=body_source();module=types.ModuleType(name+'.opaque_observer_body');module.__file__=str(Path(path).resolve())
    sys.modules[module.__name__]=module;exec(compile(text,module.__file__+'::opaque-observer-context','exec'),module.__dict__)
    module.compile_source=compile_source;module.OPAQUE_ADAPTATION_DIFF=diff;return module


_body=load_body(__name__,__file__)
globals().update({name:value for name,value in vars(_body).items()if not name.startswith('__')})
