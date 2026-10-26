"""Fixed-target canonical RCX/STA diagnostic; draft models never qualify timing.

This separate adapter neither edits a PDK nor defines a physical candidate.
Preparation needs a closed fresh final-views packet. Root GO and an independent
1200-second outer guard are mandatory before the bounded 1080-second leaf.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import threading
import time
import uuid

sys.dont_write_bytecode = True
import streaming_8x4_prepare as P
import streaming_8x4_run as R
import streaming_8x4_signoff_execute as V
import streaming_8x4_draft_rc_timing_observe as O
from streaming_8x4_geometry import regular, require, sha
from streaming_tt_intake import dependency_closure
from streaming_tt_physical import inspect_runtime
from streaming_tt_quality import timing_quality
from physical_timing_acceptance import assess_timing

OWN = 'scripts/streaming_8x4_draft_rc_timing.py'
ENTRIES = (OWN, 'scripts/streaming_8x4_draft_rc_timing_observe.py',
    'physical/streaming_8x4/librelane_plugin_streaming_8x4.py', 'tools/physical-toolchain.json')
MODELS = ('MIN', 'TYP', 'MAX')
CORNERS = ('nom_fast_1p32V_m40C', 'nom_slow_1p08V_125C', 'nom_typ_1p20V_25C')
PLAN_SHA = '51a58576fe349c88b6900185db8c7134172564d1ffcda40e46595747e3c1378a'
RULE_SHA = dict(MIN='320dea7c8ae3c64a53efb378450ead0d65c28a136de9ac83365f2ff0ff907705',
    TYP='bf2af2235b102d7bb58fe782d8d8b41a64cb3efde46593562314a499e9c4a612',
    MAX='803c38162f0745a3cd8579634290764786e5492939b17e75933eec4b6b7de672')
SDC_SHA = 'bcfd5a3ee86ccf13d6a8851e4b8d05b02584926862b922efa00204b3f628d0e5'
TECH_SHA = '3edd5a1ad31e8307be537d0d1b85c3258fefeb21aac04aaa476e4f72de4cffd5'
PACKAGE_PINS = {
    'steps/openroad.py': 'e74a7d61680e4ec700a1ae6b9ca2c6148b97d3f8c6d670db4b12c57ec65b04db',
    'steps/tclstep.py': '9c10b3b2ef4d590e248ce7eb5f9139bdad6f3a8f1423c9e29b1498e85fd1beae',
    'scripts/openroad/rcx.tcl': '932121962e2c1853048fe1def545d90c66f44e6c65c3b77a8990fbb7a69d531f',
    'scripts/openroad/sta/corner.tcl': 'e0096884c1929ed80506366ecc3e809c78c8493180e366fc095e2b09f5c36f53',
    'scripts/openroad/common/io.tcl': 'c7b28322f0853c7c6ebe6076a454c0baf3d97cc6194c0931eae7bf17a442b80f',
    'scripts/odbpy/filter_unannotated.py': '1af71a8ff58dafa4cf88793edfa9e432ee1b7ad347668d60da50f751c03d8434',
    'flows/classic.py': 'db887038493b0b33def8f6317548c7a47ef292ca6fcdcfb43f5f4598a9a2caed'}


def bound(path):
    return dict(path=str(regular(path).resolve()), sha256=sha(path))


def policy():
    return dict(models=list(MODELS), cell_corners=list(CORNERS), cases=9,
        executed_steps=['OpenROAD.RCX', 'OpenROAD.STAPostPNR'], direct_native_calls=21,
        jobs=1, openlane_max_cores=1, canonical_corner_workers=1,
        cpus=4, memory_gib=6, leaf_seconds=1080, outer_seconds=1200,
        seconds_per_model=300, root_go_required=True, model_qualified=False, qualified_timing=False,
        canonical_lef_res=True, canonical_merge_via_wire_res=True,
        wire_resistance_scope='Canonical -lef_res retains original LEF MAX wire resistance in every draft pass',
        model_scope='Draft five-metal capacitance plus unqualified independent parallel-cut explicit VIARES copies',
        observer_exception='Read-only graph/clock queries and assertions only; canonical timing bodies unchanged')


def diagnostic_config(original, model):
    require(model in MODELS and tuple(original.get('STA_CORNERS', [])) == CORNERS,
        'All three exact original cell corners are required')
    require(original.get('CLOCK_PERIOD') == 20 and original.get('PL_TARGET_DENSITY_PCT') == 85 and
        original.get('RCX_MERGE_VIA_WIRE_RES') is True and original.get('RCX_SDC_FILE') is None and
        original.get('SIGNOFF_SDC_FILE') == original.get('PNR_SDC_FILE') == '/work/inputs/core.sdc' and
        original.get('STA_EXTRA_CORNER_TCL_FILE') is None and original.get('STA_THREADS') is None,
        'Original clock, constraints, extractor policy or hook differs')
    require(set(original.get('RCX_RULESETS', {})) == {'nom_*'}, 'Unexpected original RC model membership')
    updated = dict(original, RCX_RULESETS={'nom_*': f'/work/diagnostic/rules/{model}.rules'},
        STA_EXTRA_CORNER_TCL_FILE='/work/diagnostic/observe.tcl')
    # The original or repair class may be recorded by the resolved candidate.
    # The original registered class is used only to schedule the same two
    # canonical classes; all earlier/later scheduled steps are skipped.
    require(type(original.get('meta')) is dict and original['meta'].get('flow') in
        ('Streaming8x4Certified', 'Streaming8x4PostAntennaRepair'), 'Unknown physical flow metadata')
    updated['meta'] = dict(original['meta'], flow='Streaming8x4Certified')
    return updated


def config_delta(original, actual, model):
    require(actual == diagnostic_config(original, model), 'Undeclared diagnostic config delta')
    return {key: dict(before=original.get(key), after=actual.get(key)) for key in sorted(set(original) | set(actual))
        if original.get(key) != actual.get(key)}


def native_package(manifest_path):
    manifest_path = regular(manifest_path).resolve(); record = P.read(manifest_path)
    require(record.get('schema') == 'pinwheel.librelane-container-source-copy.v1' and
        record.get('cad_launched') is False and record.get('container_process_launched') is False,
        'Not the immutable native source intake')
    files = record['file_sha256']; package = {}
    for name, digest in files.items():
        require(name.startswith('librelane/') and sha(manifest_path.parent / name) == digest,
            'Native source intake changed')
        package[name.removeprefix('librelane/')] = digest
    require(all(package.get(name) == digest for name, digest in PACKAGE_PINS.items()),
        'Canonical RCX/STA source bodies differ')
    return record, package


def snapshot(inputs):
    closure = dependency_closure(P.ROOT, ENTRIES)
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P.ROOT, text=True, timeout=30).strip()
    sources = {}
    for name in closure['files']:
        data = subprocess.check_output(['git', 'show', head + ':' + name], cwd=P.ROOT, timeout=30)
        require(hashlib.sha256(data).hexdigest() == sha(P.ROOT / name), 'Commit diagnostic source first: ' + name)
        target = inputs / 'producer' / name; target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(data)
        sources[name] = sha(target)
    shutil.copyfile(P.ROOT / ENTRIES[2], inputs / Path(ENTRIES[2]).name)
    return head, sources, closure


def seed_for(target, flow):
    source = Path(target['actual_odb']['path']).resolve(); flow = Path(flow).resolve()
    require(source.is_relative_to(flow), 'Actual ODB escapes selected physical flow')
    return {'odb': '/work/source/' + str(source.relative_to(flow)), 'def': '/work/views/design.def',
        'nl': '/work/views/signoff-views/implemented.v', 'sdc': '/work/inputs/core.sdc',
        'spef': {}, 'sdf': {}, 'lib': {}, 'metrics': {}}


def request_for(target, flow, views_root, package, script_sha, expectation):
    seed = seed_for(target, flow); views_root = Path(views_root)
    return dict(schema='pinwheel.streaming-8x4-draft-rc-timing-request.v1', policy=policy(),
        source_odb_sha256=target['actual_odb']['sha256'], inventory_sha256=sha(views_root / 'actual-signal/inventory.json'),
        observer_expectation=expectation, observer_sha256=script_sha,
        native_package_sha256=package, model_rules_sha256=RULE_SHA,
        input_sha256={seed['odb']: target['actual_odb']['sha256'], seed['def']: sha(views_root / 'design.def'),
            seed['nl']: sha(views_root / 'signoff-views/implemented.v'), seed['sdc']: SDC_SHA,
            '/work/views/actual-signal/inventory.json': sha(views_root / 'actual-signal/inventory.json')},
        model_qualified=False, qualified_timing=False)


def pdk_bindings(config, pdk):
    require(set(config.get('CELL_LIBS', {})) == set(CORNERS) and
        all(len(config['CELL_LIBS'][corner]) == 2 for corner in CORNERS), 'All six original cell libraries required')
    names = set(config.get('TECH_LEFS', {}).values()) | {name for values in config['CELL_LIBS'].values() for name in values}
    require(len(names) == 7, 'Original technology/six-library membership differs')
    result = {}
    for name in sorted(names):
        require(name.startswith('/work/pdk/'), 'Technology/cell model escaped original PDK')
        result[name] = sha(Path(pdk) / name.removeprefix('/work/pdk/'))
    require(all(result[name] == TECH_SHA for name in config['TECH_LEFS'].values()), 'Original five-metal technology LEF differs')
    return result


def prepare(views_path, rules_plan, source_manifest, output):
    views_path = regular(views_path).resolve(); views, view_preparation = V.closed_views(views_path)
    base_prepared = Path(view_preparation['prepared']); base = P.verify(base_prepared)
    target = views['target']; flow = Path(target['physical_report']['path']).parent / 'flow'
    original = P.read(flow / 'resolved.json')
    require(sha(base_prepared / 'inputs/core.sdc') == SDC_SHA, 'Complete original SDC changed')
    rules_plan = regular(rules_plan).resolve(); require(sha(rules_plan) == PLAN_SHA, 'Owned draft rules plan changed')
    native, package = native_package(source_manifest)
    require(native['image_id'] == P.read(target['physical_report']['path'])['runtime']['image_id'], 'Model consumer runtime differs')
    inventory_path = views_path.parent / 'actual-signal/inventory.json'; inventory = P.read(inventory_path)
    observer, expectation = O.observer(inventory, target['actual_odb']['sha256'], sha(inventory_path))
    output = Path(output).absolute(); require(not output.exists(), 'Preserve previous draft diagnostic preparation')
    inputs = output / 'inputs'; inputs.mkdir(parents=True)
    head, sources, closure = snapshot(inputs)
    (inputs / 'rules').mkdir(); (inputs / 'observe.tcl').write_text(observer)
    for model in MODELS:
        source = rules_plan.parent / (model + '-owned_explicit_via_rules.txt')
        require(sha(source) == RULE_SHA[model] and re.search(r'^LayerCount\s+5\s*$', source.read_text(), re.M),
            'Owned five-metal draft model changed')
        shutil.copyfile(source, inputs / 'rules' / (model + '.rules'))
        P.write(inputs / (model + '-config.json'), diagnostic_config(original, model))
    # Use the native State JSON field names (DEF is "def", NL is "nl").
    seed = seed_for(target, flow)
    P.write(inputs / 'seed.json', seed)
    request = request_for(target, flow, views_path.parent, package, sha(inputs / 'observe.tcl'), expectation)
    request['input_sha256'].update(pdk_bindings(original, base['pdk_root']))
    P.write(inputs / 'request.json', request)
    record = dict(schema='pinwheel.streaming-8x4-draft-rc-timing-preparation.v1', native_executed=False,
        model_qualified=False, qualified_timing=False, physical_acceptance=False,
        views_report=bound(views_path), target=target, physical_candidate=views['physical_candidate'],
        original_preparation=bound(base_prepared / 'preparation.json'), original_resolved=bound(flow / 'resolved.json'),
        rules_plan=bound(rules_plan), native_source_manifest=bound(source_manifest), source_flow=str(flow),
        pdk_root=base['pdk_root'], producer_commit=head, producer_sha256=sources,
        producer_dependency_closure=closure, input_sha256=P.inventory(inputs), request=request,
        policy=policy(), prepared_utc=datetime.now(timezone.utc).isoformat())
    P.write(output / 'preparation.json', record); verify(output); return record


def verify(output):
    output = Path(output).resolve(strict=True); record = P.read(output / 'preparation.json')
    require(record.get('schema') == 'pinwheel.streaming-8x4-draft-rc-timing-preparation.v1' and
        record.get('native_executed') is False and record.get('model_qualified') is False and
        record.get('qualified_timing') is False and record.get('physical_acceptance') is False and
        record.get('policy') == policy() and P.inventory(output / 'inputs') == record['input_sha256'],
        'Draft diagnostic preparation changed')
    for key in ('views_report', 'original_preparation', 'original_resolved', 'rules_plan', 'native_source_manifest'):
        require(bound(record[key]['path']) == record[key], 'Diagnostic authority changed: ' + key)
    views, view_preparation = V.closed_views(record['views_report']['path'])
    require(record['target'] == views['target'] and record['physical_candidate'] == views['physical_candidate'] and
        record['original_preparation'] == bound(Path(view_preparation['prepared']) / 'preparation.json'),
        'Draft diagnostic selected another physical candidate')
    original = P.read(record['original_resolved']['path']); native, package = native_package(record['native_source_manifest']['path'])
    require(sha(record['rules_plan']['path']) == PLAN_SHA and package == record['request']['native_package_sha256'],
        'Diagnostic native/model source binding differs')
    for model in MODELS:
        require(sha(output / 'inputs/rules' / (model + '.rules')) == RULE_SHA[model] and
            P.read(output / 'inputs' / (model + '-config.json')) == diagnostic_config(original, model),
            'Diagnostic model/config changed')
    for name, digest in record['producer_sha256'].items():
        require(sha(P.ROOT / name) == digest == sha(output / 'inputs/producer' / name), 'Diagnostic producer changed')
        data = subprocess.check_output(['git', 'show', record['producer_commit'] + ':' + name], cwd=P.ROOT, timeout=30)
        require(hashlib.sha256(data).hexdigest() == digest, 'Staged diagnostic source differs from commit')
    require(dependency_closure(P.ROOT, ENTRIES) == record['producer_dependency_closure'] and
        P.read(output / 'inputs/request.json') == record['request'], 'Diagnostic request/source closure changed')
    inventory_path = Path(record['views_report']['path']).parent / 'actual-signal/inventory.json'
    script, expectation = O.observer(P.read(inventory_path), record['target']['actual_odb']['sha256'], sha(inventory_path))
    require((output / 'inputs/observe.tcl').read_text() == script and expectation == record['request']['observer_expectation'] and
        sha(output / 'inputs/observe.tcl') == record['request']['observer_sha256'], 'Diagnostic observer changed')
    expected_request = request_for(record['target'], record['source_flow'], inventory_path.parent.parent,
        package, sha(output / 'inputs/observe.tcl'), expectation)
    expected_request['input_sha256'].update(pdk_bindings(original, record['pdk_root']))
    require(P.read(output / 'inputs/seed.json') == seed_for(record['target'], record['source_flow']) and
        record['request'] == expected_request, 'Diagnostic fresh seed/request differs')
    require(native['image_id'] == P.read(record['target']['physical_report']['path'])['runtime']['image_id'],
        'Diagnostic runtime source differs')
    base = P.verify(Path(record['original_preparation']['path']).parent)
    techs = set(original.get('TECH_LEFS', {}).values())
    require(record['pdk_root'] == base['pdk_root'] and len(techs) == 1 and set(original['CELL_LIBS']) == set(CORNERS) and
        all(len(original['CELL_LIBS'][corner]) == 2 for corner in CORNERS), 'Original technology/cell corner membership differs')
    for name in techs:
        require(name.startswith('/work/pdk/') and sha(Path(base['pdk_root']) / name.removeprefix('/work/pdk/')) == TECH_SHA,
            'Original five-metal technology LEF differs')
    require(sha(Path(record['original_preparation']['path']).parent / 'inputs/core.sdc') == SDC_SHA,
        'Complete original signoff constraints differ')
    return record


def package_unchanged(package, expected):
    actual = {str(path.relative_to(package)): sha(path) for path in sorted(package.rglob('*'))
        if path.is_file() and '__pycache__' not in path.parts and path.suffix != '.pyc'}
    require(actual == expected, 'Pinned native package bytes/membership changed')


def invocation(model, source_odb_sha256):
    require(model in MODELS, 'Unexpected diagnostic model')
    return dict(argv=['--manual-pdk', '--pdk-root', '/work/pdk', '--pdk', 'ihp-sg13cmos5l', '--jobs', '1',
        '--flow', 'Streaming8x4Certified', '--run-tag', 'draft-' + model.lower(),
        '--force-run-dir', '/work/result/' + model + '/flow',
        '--with-initial-state', '/work/diagnostic/seed.json', '--from', 'OpenROAD.RCX',
        '--to', 'OpenROAD.STAPostPNR', '/work/diagnostic/' + model + '-config.json'],
        policy=policy(), model=model, skipped_scheduled_prefix_and_tail=True,
        source_odb_sha256=source_odb_sha256)


def pass_command(interpreter, model):
    require(model in MODELS and type(interpreter) is str and re.fullmatch(r'/nix/store/[^/]+/bin/python3(?:\.13)?', interpreter),
        'Unsupported diagnostic native Python identity')
    return [interpreter, '-B', '/work/diagnostic/producer/' + OWN, 'native-pass',
        '--inputs', '/work/diagnostic', '--output', '/work/result/' + model, '--model', model]


def native_pass(inputs, output, model):
    """Observe exact subprocess calls then delegate to unchanged canonical bodies."""
    from librelane.steps import openroad
    from librelane.steps.tclstep import TclStep
    from librelane.common import _get_process_limit
    from librelane.__main__ import cli
    from librelane_plugin_streaming_8x4 import Streaming8x4Certified
    inputs = Path(inputs); output = Path(output); request = P.read(inputs / 'request.json')
    require(request['policy'] == policy() and model in MODELS, 'Wrong diagnostic native policy/model')
    require(os.environ.get('_OPENLANE_MAX_CORES') == '1' and _get_process_limit() == 1,
        'Canonical per-corner executor must have one worker; --jobs alone is insufficient')
    package = Path(openroad.__file__).resolve().parents[1]
    package_unchanged(package, request['native_package_sha256'])
    for name, digest in request['input_sha256'].items(): require(sha(name) == digest, 'Diagnostic source view changed')
    require(sha(inputs / 'rules' / (model + '.rules')) == RULE_SHA[model] and
        sha(inputs / 'observe.tcl') == request['observer_sha256'], 'Diagnostic model/observer changed')
    ids = [step.id for step in Streaming8x4Certified.Steps]
    require(ids[ids.index('OpenROAD.RCX') + 1] == 'OpenROAD.STAPostPNR' and
        Streaming8x4Certified.Steps[ids.index('OpenROAD.RCX')] is openroad.RCX and
        Streaming8x4Certified.Steps[ids.index('OpenROAD.STAPostPNR')] is openroad.STAPostPNR,
        'Canonical RCX/STA schedule or unchanged class identity differs')
    # Observe the canonical caller's complete environment before TclStep moves
    # some variables into its retained _env*.tcl file. Delegate the exact same
    # arguments to the unchanged implementation; no graph/model commands added.
    delegate = TclStep.run_subprocess; lock = threading.Lock(); index = 0
    journal = output / 'native-journal.jsonl'
    def observe(self, cmd, *args, **kwargs):
        nonlocal index
        with lock:
            call = index; index += 1
            row = dict(event='start', call=call, step=self.id, argv=[str(x) for x in cmd],
                env={str(k): str(v) for k, v in (kwargs.get('env') or os.environ).items()},
                log_path=str(kwargs.get('log_to') or self.get_log_path()),
                executable_sha256=sha(Path(shutil.which(str(cmd[0]))).resolve()))
            with journal.open('a') as stream: stream.write(json.dumps(row, sort_keys=True) + '\n')
        code = None; error = None
        try:
            result = delegate(self, cmd, *args, **kwargs); code = result['returncode']; return result
        except BaseException as failure:
            error = type(failure).__name__ + ': ' + str(failure)
            code = getattr(failure, 'returncode', None); raise
        finally:
            with lock:
                with journal.open('a') as stream:
                    stream.write(json.dumps(dict(event='finish', call=call, exit_code=code, error=error), sort_keys=True) + '\n')
    TclStep.run_subprocess = observe
    require(str(inputs) == '/work/diagnostic' and str(output) == '/work/result/' + model,
        'Diagnostic native pass uses undeclared mounts')
    command = invocation(model, request['source_odb_sha256'])
    P.write(output / 'invocation.json', command)
    try: cli(args=command['argv'], standalone_mode=False)
    finally:
        TclStep.run_subprocess = delegate
        package_unchanged(package, request['native_package_sha256'])
        for name, digest in request['input_sha256'].items(): require(sha(name) == digest, 'Diagnostic source changed during native pass')


def native(inputs, output):
    inputs = Path(inputs); output = Path(output); request = P.read(inputs / 'request.json'); rows = []
    require(request.get('schema') == 'pinwheel.streaming-8x4-draft-rc-timing-request.v1' and
        request['policy'] == policy(), 'Wrong diagnostic native request')
    require(str(inputs) == '/work/diagnostic' and str(output) == '/work/result' and
        Path(__file__).absolute() == Path('/work/diagnostic/producer/' + OWN), 'Use the exact frozen native dispatcher')
    P.write(output / 'native-python.json', dict(schema='pinwheel.streaming-8x4-draft-rc-native-python.v1',
        executable=sys.executable, executable_sha256=sha(sys.executable), version=sys.version,
        model_qualified=False, qualified_timing=False))
    for model in MODELS:
        destination = output / model; destination.mkdir()
        command = pass_command(sys.executable, model)
        started = time.monotonic(); row = dict(model=model, argv=command, status='running', timeout_seconds=300)
        rows.append(row); P.write(output / 'native-passes.json', rows)
        try:
            with (destination / 'flow.log').open('w') as stream:
                completed = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT, timeout=300)
            row.update(status='completed', exit_code=completed.returncode)
        except subprocess.TimeoutExpired:
            row.update(status='timed_out', exit_code=124)
        finally:
            row['elapsed_seconds'] = time.monotonic() - started; P.write(output / 'native-passes.json', rows)
        require(row.get('exit_code') == 0, 'Draft diagnostic pass incomplete; later models not executed: ' + model)


def checked_passes(output, record):
    output = Path(output); identity = P.read(output / 'native-python.json')
    require(identity.get('schema') == 'pinwheel.streaming-8x4-draft-rc-native-python.v1' and
        identity.get('model_qualified') is False and identity.get('qualified_timing') is False and
        re.fullmatch(r'[0-9a-f]{64}', identity.get('executable_sha256', '')) and
        identity.get('version', '').startswith('3.13.13 '), 'Native diagnostic Python identity differs')
    rows = P.read(output / 'native-passes.json')
    require(type(rows) is list and len(rows) == 3 and [row.get('model') for row in rows] == list(MODELS),
        'Incomplete/extra/reordered diagnostic model matrix')
    for model, row in zip(MODELS, rows):
        require(set(row) == {'model', 'argv', 'status', 'timeout_seconds', 'exit_code', 'elapsed_seconds'} and
            row['argv'] == pass_command(identity['executable'], model) and row['status'] == 'completed' and
            type(row['exit_code']) is int and row['exit_code'] == 0 and type(row['timeout_seconds']) is int and
            row['timeout_seconds'] == 300 and type(row['elapsed_seconds']) in (int, float) and
            math.isfinite(row['elapsed_seconds']) and 0 <= row['elapsed_seconds'] <= 301 and
            P.read(output / model / 'invocation.json') == invocation(model, record['request']['source_odb_sha256']),
            'Diagnostic model process/config/300s allowance/initial-state invocation differs')
    return rows


def calls(path):
    rows = [json.loads(line) for line in regular(path).read_text().splitlines()]
    starts = [row for row in rows if row['event'] == 'start']; finishes = [row for row in rows if row['event'] == 'finish']
    require(len(rows) == 14 and len(starts) == len(finishes) == 7 and [row['call'] for row in starts] == list(range(7)) and
        sorted(row['call'] for row in finishes) == list(range(7)) and all(row['exit_code'] == 0 for row in finishes),
        'Incomplete canonical direct native command journal')
    require([row['step'] for row in starts] == ['OpenROAD.RCX'] + ['OpenROAD.STAPostPNR'] * 6,
        'Unexpected actual native step inventory')
    require(all(row.get('env', {}).get('_OPENLANE_MAX_CORES') == '1' for row in starts),
        'Actual canonical corner-worker resource setting differs')
    require(sum(row['argv'][0].endswith('/sta') or row['argv'][0] == 'sta' for row in starts) == 3 and
        sum(any(arg.endswith('/filter_unannotated.py') for arg in row['argv']) for row in starts) == 3 and
        starts[0]['argv'][-1].endswith('/openroad/rcx.tcl'), 'Wrong canonical RCX/STA/filter command membership')
    return starts


def analyze(directory, record, model):
    flow = directory / 'flow'; config = P.read(flow / 'resolved.json')
    delta = config_delta(P.read(record['original_resolved']['path']), config, model)
    states = sorted(path for path in flow.glob('*/state_out.json'))
    require(len(states) == 2 and states[0].parent.name.endswith('-openroad-rcx') and
        states[1].parent.name.endswith('-openroad-stapostpnr'), 'Diagnostic did not complete exactly RCX then STA')
    rcx, sta = states[0].parent, states[1].parent
    native_calls = calls(directory / 'native-journal.jsonl')
    request = record['request']; inventories = P.read(Path(record['views_report']['path']).parent / 'actual-signal/inventory.json')
    rcx_state = P.read(states[0]); sta_state = P.read(states[1])
    seed = seed_for(record['target'], record['source_flow'])
    require(all(state.get(key) == seed[key] for state in (rcx_state, sta_state) for key in ('odb', 'def', 'nl', 'sdc')),
        'Canonical diagnostic changed/carried another physical graph or constraints')
    require(set(rcx_state['spef']) == {'nom_*'} and sta_state['spef'] == rcx_state['spef'], 'Missing/foreign carried SPEF')
    spef_name = rcx_state['spef']['nom_*']; mount = '/work/result/' + model + '/flow/'
    require(spef_name.startswith(mount), 'SPEF not freshly extracted in this model pass')
    spef = flow / spef_name[len(mount):]; regular(spef)
    source_env = native_calls[0]['env']
    require(source_env.get('RCX_RULESET') == f'/work/diagnostic/rules/{model}.rules' and
        source_env.get('SAVE_SPEF') == spef_name and source_env.get('RCX_MERGE_VIA_WIRE_RES') == '1' and
        source_env.get('CURRENT_DEF') == '/work/views/design.def' and
        source_env.get('RCX_LEF') == config['TECH_LEFS']['nom_*'],
        'Canonical extraction model/output/policy binding differs')
    coverage = O.spef_coverage(spef.read_text(), inventories); cases = {}
    for corner in CORNERS:
        dest = sta / corner
        require(dest.is_dir(), 'Missing actual STA cell corner')
        selected = [row for row in native_calls if row['env'].get('_CURRENT_CORNER_NAME') == corner and
            (row['argv'][0] == 'sta' or row['argv'][0].endswith('/sta'))]
        require(len(selected) == 1 and selected[0]['env'].get('OPENLANE_SDC_IDEAL_CLOCKS') == '0' and
            selected[0]['env'].get('_SDC_IN') == '/work/inputs/core.sdc' and
            selected[0]['env'].get('STA_EXTRA_CORNER_TCL_FILE') == '/work/diagnostic/observe.tcl' and
            selected[0]['env'].get('CURRENT_NL') == '/work/views/signoff-views/implemented.v' and
            selected[0]['env'].get('_CURRENT_SPEF_BY_CORNER') == spef_name and
            selected[0]['env'].get('_CURRENT_CORNER_LIBS', '').split() == config['CELL_LIBS'][corner],
            'Actual canonical corner/model/constraints/hook binding differs')
        filters = [row for row in native_calls if any(arg.endswith('/filter_unannotated.py') for arg in row['argv']) and
            '--corner' in row['argv'] and row['argv'][row['argv'].index('--corner') + 1] == corner]
        require(len(filters) == 1 and seed['odb'] in filters[0]['argv'] and
            any(arg.endswith('/' + corner + '/checks.rpt') for arg in filters[0]['argv']),
            'Actual canonical annotation filter targets another ODB/corner')
        clock = O.check_observer((dest / 'sta.log').read_text(), request['observer_expectation'], corner,
            (dest / 'clock.rpt').read_text(), (dest / 'unpropagated.rpt').read_text())
        quality = timing_quality(inventories, (dest / 'checks.rpt').read_text())
        metric = sta_state['metrics']['design__max_fanout_violation__count__corner:' + corner]
        require(type(metric) is int and metric == quality['raw_fanout_violations'], 'Raw fanout reconciliation differs')
        cases[corner] = dict(clock=clock, quality=quality, model=model, spef_sha256=sha(spef),
            cell_libraries={name:request['input_sha256'][name] for name in config['CELL_LIBS'][corner]},
            tech_lef_sha256=request['input_sha256'][source_env['RCX_LEF']],
            raw_clock_report_sha256=sha(dest / 'clock.rpt'),
            raw_unpropagated_report_sha256=sha(dest / 'unpropagated.rpt'),
            canonical_filtered_unannotated_metrics=P.read(dest / 'filter_unannotated_metrics.json'))
    return dict(model=model, rules_sha256=RULE_SHA[model], config_delta=delta, spef=bound(spef),
        spef_coverage=coverage, cases=cases, assessment=assess_timing(sta_state['metrics'], list(CORNERS)),
        raw_metrics=R.receipt_value(sta_state['metrics']), direct_native_calls=len(native_calls),
        model_qualified=False, qualified_timing=False)


def container_command(preparation, output, record, runtime, owner, name):
    lock = P.read(P.ROOT / 'tools/physical-toolchain.json')
    physical = P.read(record['target']['physical_report']['path'])
    source = P.read(record['native_source_manifest']['path'])
    # Docker's loaded image ID and the OCI descriptor are distinct identities.
    # Bind the actual observed image to both selected physical execution and
    # its source intake; retain the original architecture/layer/config lock.
    image = physical['runtime']['image_id']
    require(re.fullmatch(r'sha256:[0-9a-f]{64}', image) and source['image_id'] == image and
        runtime == physical['runtime'] == dict(image_id=image, architecture='arm64', os='linux',
        rootfs_diff_ids=lock['container_rootfs_diff_ids'], runtime_config_sha256=lock['container_runtime_config_sha256']) and
        re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+', name) and str(uuid.UUID(owner)) == owner,
        'Diagnostic runtime/owned container identity differs')
    preparation = Path(preparation); output = Path(output)
    prepared = Path(record['original_preparation']['path']).parent
    views = Path(record['views_report']['path']).parent
    return ['docker', 'run', '--rm', '--pull', 'never', '--name', name,
        '--label', 'org.pinwheel.streaming8_owner=' + owner, '--network', 'none', '--cpus', '4',
        '--memory', '6g', '--memory-swap', '6g', '--read-only', '--tmpfs', '/tmp:rw,size=512m',
        '--env', 'PYTHONDONTWRITEBYTECODE=1', '--env', '_OPENLANE_MAX_CORES=1',
        '--env', 'PYTHONPATH=/work/diagnostic:/work/diagnostic/producer/scripts:/work/inputs',
        '--mount', f'type=bind,source={preparation / "inputs"},target=/work/diagnostic,readonly',
        '--mount', f'type=bind,source={prepared / "inputs"},target=/work/inputs,readonly',
        '--mount', f'type=bind,source={record["source_flow"]},target=/work/source,readonly',
        '--mount', f'type=bind,source={views},target=/work/views,readonly',
        '--mount', f'type=bind,source={record["pdk_root"]},target=/work/pdk,readonly',
        '--mount', f'type=bind,source={output},target=/work/result', '--workdir', '/work/diagnostic',
        runtime['image_id'], 'python3', '-B', '/work/diagnostic/producer/' + OWN, 'native',
        '--inputs', '/work/diagnostic', '--output', '/work/result']


def checked_execution(output, preparation, record, runtime):
    output = Path(output); execution = P.read(output / 'execution.json'); command = execution.get('argv')
    require(type(command) is list and len(command) > 6 and
        command == container_command(preparation, output, record, runtime, execution['owner'], command[6]) and
        execution.get('status') == 'completed' and execution.get('exit_code') == 0 and
        execution.get('timeout_seconds') == 1080 and execution.get('container_termination', {}).get('status') == 'absent',
        'Diagnostic owned execution/resource/mount/environment/1080s contract differs')
    return execution


def run(args):
    P.ROOT = Path(args.workspace).resolve(strict=True) if args.workspace else P.ROOT
    preparation = Path(args.preparation).resolve(strict=True); record = verify(preparation)
    worker = preparation / 'inputs/producer' / OWN
    if not args.frozen:
        os.execv(sys.executable, [sys.executable, '-B', str(worker), 'run', '--preparation', str(preparation),
            '--output', str(Path(args.output).absolute()), '--name', args.name, '--workspace', str(P.ROOT), '--frozen'])
    require(Path(__file__).resolve() == worker.resolve() and re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+', args.name),
        'Use exact frozen diagnostic producer and safe owned container name')
    output = Path(args.output).absolute(); require(not output.exists(), 'Preserve previous diagnostic execution'); output.mkdir(parents=True)
    runtime = inspect_runtime(P.read(P.ROOT / 'tools/physical-toolchain.json')); owner = str(uuid.uuid4())
    command = container_command(preparation, output, record, runtime, owner, args.name)
    execution = V.owned_native(command, output, owner, 1080)
    report = dict(schema='pinwheel.streaming-8x4-draft-rc-timing-run.v1', preparation=bound(preparation / 'preparation.json'),
        target=record['target'], physical_candidate=record['physical_candidate'], policy=policy(), runtime=runtime,
        execution=execution, measurements_completed=False, diagnostic_checks_passed=False,
        model_qualified=False, qualified_timing=False, physical_acceptance=False)
    try:
        require(checked_execution(output, preparation, record, runtime) == execution, 'Retained diagnostic execution differs')
        checked_passes(output, record)
        results = {model: analyze(output / model, record, model) for model in MODELS}
        require(sum(row['direct_native_calls'] for row in results.values()) == 21, 'Incomplete actual native call matrix')
        report.update(measurements_completed=True, results=results,
            diagnostic_checks_passed=all(row['spef_coverage']['complete'] and row['assessment']['status'] == 'passed' and
                all(case['quality']['annotation_complete_for_consumed_nets'] for case in row['cases'].values()) for row in results.values()))
    except BaseException as error: report['error'] = type(error).__name__ + ': ' + str(error)
    try:
        require(verify(preparation) == record and inspect_runtime(P.read(P.ROOT / 'tools/physical-toolchain.json')) == runtime,
            'Diagnostic input/runtime changed')
        report['inputs_pdk_runtime_unchanged'] = True
    except BaseException as error:
        report.update(measurements_completed=False, diagnostic_checks_passed=False, closeout_error=str(error))
    report['artifact_sha256'] = {str(path.relative_to(output)): sha(path) for path in sorted(output.rglob('*'))
        if path.is_file() and path != output / 'report.json'}
    R.write(output / 'report.json', report); return report


def closed_report(path):
    path = regular(path).resolve(); report = P.read(path)
    require(report.get('schema') == 'pinwheel.streaming-8x4-draft-rc-timing-run.v1' and
        report.get('measurements_completed') is True and report.get('inputs_pdk_runtime_unchanged') is True and
        report.get('model_qualified') is False and report.get('qualified_timing') is False and
        report.get('physical_acceptance') is False and report.get('policy') == policy(),
        'Draft diagnostic measurement packet is incomplete or promotes qualification')
    marker = report['preparation']; require(bound(marker['path']) == marker, 'Diagnostic preparation changed')
    record = verify(Path(marker['path']).parent)
    require(report['target'] == record['target'] and report['physical_candidate'] == record['physical_candidate'] and
        report['execution'] == checked_execution(path.parent, Path(marker['path']).parent, record, report['runtime']),
        'Diagnostic target/owned closeout differs')
    checked_passes(path.parent, record)
    artifacts = {str(item.relative_to(path.parent)): sha(item) for item in sorted(path.parent.rglob('*'))
        if item.is_file() and item != path}
    require(artifacts == report['artifact_sha256'], 'Diagnostic complete artifact membership/bytes changed')
    results = {model: analyze(path.parent / model, record, model) for model in MODELS}
    require(report['results'] == results and sum(row['direct_native_calls'] for row in results.values()) == 21,
        'Diagnostic model/corner/call interpretation changed')
    passed = all(row['spef_coverage']['complete'] and row['assessment']['status'] == 'passed' and
        all(case['quality']['annotation_complete_for_consumed_nets'] for case in row['cases'].values()) for row in results.values())
    require(report['diagnostic_checks_passed'] == passed, 'Draft diagnostic measurement assessment differs')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__); sub = parser.add_subparsers(dest='mode', required=True)
    prep = sub.add_parser('prepare')
    for name in ('views', 'rules-plan', 'source-manifest', 'output'): prep.add_argument('--' + name, required=True, type=Path)
    check = sub.add_parser('verify'); check.add_argument('--preparation', required=True, type=Path)
    reopen = sub.add_parser('reopen'); reopen.add_argument('--report', required=True, type=Path)
    launch = sub.add_parser('run')
    for name in ('preparation', 'output'): launch.add_argument('--' + name, required=True, type=Path)
    launch.add_argument('--name', required=True); launch.add_argument('--workspace', type=Path)
    launch.add_argument('--frozen', action='store_true', help=argparse.SUPPRESS)
    for mode in ('native', 'native-pass'):
        native_parser = sub.add_parser(mode)
        for name in ('inputs', 'output'): native_parser.add_argument('--' + name, required=True, type=Path)
        if mode == 'native-pass': native_parser.add_argument('--model', required=True, choices=MODELS)
    args = parser.parse_args()
    if args.mode == 'prepare': prepare(args.views, args.rules_plan, args.source_manifest, args.output)
    elif args.mode == 'verify': verify(args.preparation)
    elif args.mode == 'reopen': closed_report(args.report)
    elif args.mode == 'native': native(args.inputs, args.output)
    elif args.mode == 'native-pass': native_pass(args.inputs, args.output, args.model)
    else:
        result = run(args); print(args.output / 'report.json'); return 0 if result['measurements_completed'] else 3
    return 0


if __name__ == '__main__': raise SystemExit(main())
