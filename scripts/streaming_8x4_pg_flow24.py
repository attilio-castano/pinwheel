"""New PG-aware candidate authority; old interrupted/replay ODBs are seeds only.

Root launches only through closure24_resources. Frozen attempt consumers reopen
their executed source snapshot and Git objects, not later checkout versions.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import uuid

sys.dont_write_bytecode = True
import streaming_8x4_prepare as P
import streaming_8x4_run as R
import streaming_8x4_route_replay as RR
import streaming_8x4_closure24_policy as CLOCK
from streaming_8x4_geometry import regular, require, sha
from streaming_tt_intake import dependency_closure
from streaming_tt_physical import inspect_runtime

ROOT = Path(__file__).resolve().parents[1]
PRIOR = 'build/campaigns/8x4-20261022-01'
CAMPAIGN = 'build/campaigns/8x4-20261024-01'
OWN = 'scripts/streaming_8x4_pg_flow24.py'
PLUGIN = 'physical/streaming_8x4/librelane_plugin_streaming_8x4_pg24.py'
HELPER = 'scripts/streaming_8x4_pg_diode.py'
FLOW = 'Streaming8x4PGClosure24'
BOOTSTRAP = 'Pinwheel.PGDiodeBootstrap'
MODES = ('late-smoke', 'initial-smoke', 'full')
NATIVE_RESOURCES = dict(schema='pinwheel.closure24-pg-fixed-resource-policy.v1',
    openroad_threads=2, container_cpus=2, memory_bytes=6*1024**3, extra_swap_bytes=0,
    full_leaf_seconds_cap=14040, smoke_leaf_seconds_cap=1800,
    minimum_outer_reserve_seconds=60, resource_only_delta=True)
INITIAL_CONFIG_RELATIVE = 'flow/35-openroad-repairantennas/1-openroad-diodeinsertion/config.json'
INITIAL_CONFIG_SHA256 = 'd5fed26a78ed476c5bc2e8cbb928fc05a12a39389425dfa0ffbeadf0463626d5'


def thread_count(packet):
    # Historical executed packets remain on their original four-worker policy.
    if 'resource_policy' not in packet: return 4
    require(packet['resource_policy'] == NATIVE_RESOURCES, 'Fixed PG resource policy changed')
    return NATIVE_RESOURCES['openroad_threads']


def validate_diagnostic_config(config, packet, replay=None, initial=None):
    version = packet.get('diagnostic_config_version', 1)
    require(type(version) is int and version in (1, 2), 'Unsupported diagnostic config adapter')
    require(config.get('OPENROAD_THREADS') == thread_count(packet), 'Observed PG worker count differs')
    if version == 2:
        expected = diagnostic_config(packet, replay, initial)
        require(json.dumps(config, sort_keys=True, allow_nan=False) ==
                json.dumps(expected, sort_keys=True, allow_nan=False),
                'Initial config membership/values differ beyond the worker delta')
        return dict(adapter_version=2, baseline_initial_sha256=INITIAL_CONFIG_SHA256,
                    only_delta=dict(OPENROAD_THREADS=dict(before=4, after=thread_count(packet))))
    # Reuse the unchanged historical validator for every other field, after
    # explicitly checking and removing only the declared resource-only delta.
    return RR.validate_config(dict(config, OPENROAD_THREADS=4))


def diagnostic_config(packet, replay, initial=None):
    RR.validate_config(replay)
    version = packet.get('diagnostic_config_version', 1)
    require(type(version) is int and version in (1, 2), 'Unsupported diagnostic config adapter')
    if version == 1:
        return dict(replay, OPENROAD_THREADS=thread_count(packet))
    require(packet['mode'] == 'initial-smoke' and type(initial) is dict and
            type(initial.get('OPENROAD_THREADS')) is int and initial['OPENROAD_THREADS'] == 4 and
            initial.get('CLOCK_PERIOD') == 20 and initial.get('DESIGN_NAME') == RR.TOP and
            initial.get('PNR_SDC_FILE') == '/work/inputs/core.sdc',
            'Exact executed initial-step config/semantic authority required')
    # All initial fields and their membership come from the authenticated
    # executed _DiodeInsertion config; no DRT-only variables or defaults added.
    return dict(initial, OPENROAD_THREADS=thread_count(packet))


def initial_config_authority(replay):
    item = replay['repair_preparation']
    require(bound(item['path']) == item, 'Historical repair preparation changed')
    repair = P.read(item['path']); parent = repair['parent_report']
    require(bound(parent['path']) == parent, 'Historical executed parent report changed')
    path = Path(parent['path']).parent / INITIAL_CONFIG_RELATIVE
    require(sha(path) == INITIAL_CONFIG_SHA256 == P.read(parent['path'])['artifact_sha256'].get(INITIAL_CONFIG_RELATIVE),
            'Exact closed executed initial-step configuration changed')
    return bound(path)


def bound(path):
    path = regular(path).resolve()
    return dict(path=str(path), sha256=sha(path))


def workspace_context(workspace):
    global ROOT
    if workspace is not None:
        ROOT = Path(workspace).resolve(strict=True)
    P.ROOT = ROOT


def parent_context():
    replay = ROOT / PRIOR / 'route-replay-preparation-01'
    packet = RR.verify(replay)
    base = P.verify(Path(packet['original_preparation']['path']).parent)
    require(packet['runtime']['image_id'] == 'sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92',
            'Different retained runtime')
    return replay, packet, base


def historical_seed(mode, packet):
    if mode == 'late-smoke':
        return Path(packet['source_odb']['path'])
    if mode == 'full':
        path = ROOT / PRIOR / 'route-replay-preparation-01/step/postdiode.odb'
        require(sha(path) == 'a0c41ff2ffef86fd7fc0d2e592184832b6158079d9f5824258a9539aaa8e1f4f',
                'Exact preserved postdiode seed changed')
        return path
    require(mode == 'initial-smoke', 'Unknown seed scope')
    repair = P.read(packet['repair_preparation']['path'])
    report = P.read(repair['parent_report']['path'])
    matches = [row for row in report['states']
               if row['step_directory'].startswith('34-') and
               Path(row['state']).parent.parent == Path(repair['parent_report']['path']).parent / 'flow']
    require(len(matches) == 1, 'No exact pre-initial-antenna state')
    view = matches[0]['views']['odb']
    require(sha(view['path']) == view['sha256'] == report['artifact_sha256'][
        str(Path(view['path']).relative_to(Path(repair['parent_report']['path']).parent))],
        'Initial path seed is not its closed artifact')
    return Path(view['path'])


def known_diodes():
    path = ROOT / PRIOR / 'route-replay-coordinate-analysis-03/report.json'
    require(sha(path) == 'a73fb5aede7059b823d990d463bf95b0f2e9daaabdb0bc30a100ec4a1cdd1308',
            'Closed geometry analysis changed')
    # The complete pre/post census gives device identity, independently of
    # which marker happened to mention a diode.
    analysis = P.read(path)
    step = ROOT / PRIOR / 'route-replay-preparation-01/step'
    for name in ('before.tsv', 'postdiode.tsv'):
        target = (step / name).resolve()
        require(analysis['input_sha256'].get(str(target)) == sha(target), 'Closed added-device census changed')
    def inventory(name):
        return {row[1]: row[2] for row in
                (line.split('\t') for line in (step / name).read_text().splitlines())
                if row[0] == 'INST'}
    before, after = inventory('before.tsv'), inventory('postdiode.tsv')
    names = sorted(set(after) - set(before))
    require(len(names) == 39 and all(after[name] == 'sg13cmos5l_antennanp' for name in names) and
            all(after.get(name) == master for name, master in before.items()),
            'Exact 39 added devices/preexisting masters differ')
    return names


def register_variant(policy, definition=None):
    require(policy in ('A', 'B'), 'Unknown bounded PG placement policy')
    if definition is None:
        require(policy == 'A', 'Fallback must bind its complete declared placement definition')
        definition = dict(radius_sites=16, adjacent_rows=0)
    directory = ROOT / CAMPAIGN / 'physical-variants'
    directory.mkdir(exist_ok=True)
    records = [P.read(path) for path in sorted(directory.glob('variant-*.json'))]
    for row in records:
        if row['policy'] == policy:
            require(row['strategy'] == 'PG-aware-antenna-access' and
                    definition == row.get('policy_definition', dict(radius_sites=16, adjacent_rows=0)),
                    'Variant identity/placement definition changed')
            verify_variant_authority(row)
            return row
    require(datetime.now(timezone.utc) < CLOCK.timestamp(CLOCK.SCHEDULE['primary_route_cutoff']),
            'New routing repair variant after the primary cutoff')
    require(len(records) < 2 and (policy == 'A' or any(row['policy'] == 'A' for row in records)),
            'Maximum two campaign variants; B requires the declared A predecessor')
    fallback = None
    if policy == 'B':
        authority = directory / 'routing-fallback-B-admission.json'
        fallback = bound(authority); admitted = P.read(authority)
        first = directory / 'variant-01.json'
        require(admitted.get('schema') == 'pinwheel.closure24-routing-fallback-admission.v1' and
                admitted.get('policy') == 'B' and admitted.get('root_reviewed_A_failure') is True and
                admitted.get('predecessor') == bound(first) and
                admitted.get('failure_evidence') == bound(admitted['failure_evidence']['path']),
                'B requires separately retained Root-reviewed failed A evidence')
    index = len(records) + 1
    row = dict(schema='pinwheel.closure24-physical-variant.v1', ordinal=index,
               policy=policy, strategy='PG-aware-antenna-access',
               registered_utc=datetime.now(timezone.utc).isoformat(),
               maximum_variants=2, semantic_state_bits=6039, clock_period_ns=20,
               routing_fallback_admission=fallback, policy_definition=definition)
    path = directory / ('variant-%02d.json' % index)
    with path.open('x') as stream:
        json.dump(row, stream, indent=2); stream.write('\n')
    return row


def verify_variant_authority(row):
    """Reopen the immutable fallback decision on every later admission/readback."""
    directory = ROOT / CAMPAIGN / 'physical-variants'
    require(row.get('policy') in ('A', 'B') and row.get('maximum_variants') == 2 and
            row.get('ordinal') == (1 if row['policy'] == 'A' else 2),
            'Physical variant policy/ordinal/budget changed')
    if row['policy'] == 'A':
        require(row.get('routing_fallback_admission') is None, 'A cannot inherit fallback authority')
        return
    item = row.get('routing_fallback_admission')
    authority = directory / 'routing-fallback-B-admission.json'
    require(item == bound(authority), 'B fallback admission changed after registration')
    admitted = P.read(authority)
    require(admitted.get('schema') == 'pinwheel.closure24-routing-fallback-admission.v1' and
            admitted.get('policy') == 'B' and admitted.get('root_reviewed_A_failure') is True and
            admitted.get('predecessor') == bound(directory / 'variant-01.json') and
            admitted.get('failure_evidence') == bound(admitted['failure_evidence']['path']),
            'B requires the unchanged retained failed A decision')


def snapshot(inputs):
    entries = (OWN, PLUGIN, HELPER)
    closure = dependency_closure(ROOT, entries)
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    values = {}
    for name in closure['files']:
        raw = subprocess.check_output(['git', 'show', commit + ':' + name], cwd=ROOT)
        require(hashlib.sha256(raw).hexdigest() == sha(ROOT / name), 'Commit candidate producer first: ' + name)
        target = inputs / 'producer' / name
        target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(raw)
        values[name] = sha(target)
    shutil.copyfile(ROOT / PLUGIN, inputs / 'librelane_plugin_streaming_8x4_pg24.py')
    return commit, values, closure


def insert_hook(body, bootstrap=False):
    seam = 'read_current_odb\n'
    require(body.count(seam) == 1, 'Canonical single read-current-ODB seam changed')
    extra = 'source /work/closure/inputs/hook.tcl\n'
    if bootstrap:
        extra += 'pg_diode_bootstrap\n'
    return body.replace(seam, seam + extra, 1)


def prepare(mode, policy, output):
    import streaming_8x4_pg_diode as G
    require(mode in MODES and policy in ('A', 'B'), 'Unknown candidate mode/policy')
    replay, old, base = parent_context()
    seed = historical_seed(mode, old); variant = register_variant(policy, G.POLICIES[policy])
    output = Path(output).absolute(); require(not output.exists(), 'Preserve prior preparation')
    inputs = output / 'inputs'; inputs.mkdir(parents=True)
    commit, sources, closure = snapshot(inputs)
    pdk = Path(base['pdk_root'])
    prefix = 'ihp-sg13cmos5l/libs.ref/sg13cmos5l_stdcell/lef/'
    tech, cell = prefix + 'sg13cmos5l_tech.lef', prefix + 'sg13cmos5l_stdcell.lef'
    request = G.make_request(pdk / tech, pdk / cell, policy=policy,
                            native_tech_lef='/work/pdk/' + tech,
                            native_cell_lef='/work/pdk/' + cell)
    P.write(inputs / 'pg-request.json', request)
    names = known_diodes()
    repair = P.read(old['repair_preparation']['path'])
    parent_report = P.read(repair['parent_report']['path'])
    parent_dir = Path(repair['parent_report']['path']).parent
    order_path = parent_dir / 'metadata/flow-order.json'
    resolved_path = parent_dir / 'flow/resolved.json'
    for path in (order_path, resolved_path):
        require(parent_report['artifact_sha256'].get(str(path.relative_to(parent_dir))) == sha(path),
                'Historical canonical order/config artifact changed')
    original_steps = P.read(order_path)['actual_steps']
    hook = G.hook_tcl('/work/closure/inputs/pg-request.json', output_dir=None,
                      python_executable='python3',
                      helper_path='/work/closure/inputs/producer/' + HELPER,
                      policy=policy, initial_names=names if mode == 'full' else ())
    (inputs / 'hook.tcl').write_text(hook)
    version = 2 if mode == 'initial-smoke' else 1
    config_context = dict(mode=mode, resource_policy=NATIVE_RESOURCES, diagnostic_config_version=version)
    initial_authority = initial_config_authority(old) if version == 2 else None
    initial_data = P.read(initial_authority['path']) if initial_authority else None
    if initial_authority:
        shutil.copyfile(initial_authority['path'], inputs / 'historical-initial-config.json')
        shutil.copyfile(replay / 'inputs/config.json', inputs / 'historical-drt-config.json')
    config = diagnostic_config(config_context, P.read(replay / 'inputs/config.json'), initial_data)
    P.write(inputs / 'config.json', config)
    native_source = ROOT / PRIOR / 'intake/librelane-native-source/librelane/scripts/openroad'
    drt = (native_source / 'drt.tcl').read_text()
    initial = (native_source / 'antenna_repair.tcl').read_text()
    require(sha(native_source / 'drt.tcl') == old['native_package_sha256']['scripts/openroad/drt.tcl'] and
            sha(native_source / 'antenna_repair.tcl') == old['native_package_sha256']['scripts/openroad/antenna_repair.tcl'],
            'Canonical script source changed')
    (inputs / 'drt-pg.tcl').write_text(insert_hook(drt))
    (inputs / 'initial-pg.tcl').write_text(insert_hook(initial))
    (inputs / 'bootstrap.tcl').write_text('source $::env(SCRIPTS_DIR)/openroad/common/io.tcl\n'
        'read_current_odb\nsource /work/closure/inputs/hook.tcl\npg_diode_bootstrap\nwrite_views\n')
    preamble = RR.replay_tcl().split('replay_capture $replay/before\n')[0]
    preamble = preamble.replace('set replay /work/replay/step', 'set replay $::env(STEP_DIR)')
    late = preamble + '\nsource /work/closure/inputs/hook.tcl\nreplay_capture $replay/before\n' + \
        'set violations [tee -variable antenna_log {check_antennas}]\n' + \
        'set pins [regexp -all -inline {\\[INFO ANT-0001\\] Found ([0-9]+) pin violations\\.} $antenna_log]\n' + \
        'replay_need [expr {$violations == 35 && [llength $pins] == 2 && [lindex $pins 1] == 36}] {Exact historical35net/36pin reproduction required}\n' + \
        'set before_instances [llength [[ord::get_db_block] getInsts]]\n' + \
        'set count [repair_antennas sg13cmos5l_antennanp -ratio_margin 10]\n' + \
        'replay_need [expr {$count == 39 && [llength [[ord::get_db_block] getInsts]] - $before_instances == 39}] {Exact39diode reproduction required; no truncation}\n' + \
        'replay_capture $replay/postdiode\nwrite_guides $replay/postdiode.guide\n' + \
        'puts "PINWHEEL_PG_DIODES $count"\n' + \
        'detailed_route -droute_end_iter 6 -or_seed 42 -verbose 1 -drc_report_iter_step 1 -output_drc $replay/bounded.drc\n' + \
        'replay_capture $replay/postroute\nwrite_guides $replay/postroute.guide\n'
    (inputs / 'late-smoke.tcl').write_text(late)
    # Full seed carries the unchanged certified input NL only as an input
    # reference. Bootstrap writes fresh NL/PNL from the actual seed database.
    P.write(inputs / 'seed.json', dict(odb='/work/seed.odb', nl='/work/inputs/design.v', metrics={}))
    packet = dict(schema='pinwheel.closure24-pg-flow-preparation.v1', mode=mode, policy=policy,
        variant=variant, resource_policy=NATIVE_RESOURCES, diagnostic_config_version=version,
        source_odb=bound(seed), seed_scope='seed-only; never final-target authority',
        historical_replay_preparation=bound(replay / 'preparation.json'),
        original_preparation=old['original_preparation'], pdk_root=str(pdk),
        runtime=old['runtime'], native_package_sha256=old['native_package_sha256'],
        canonical_flow_steps=original_steps, original_resolved_config=bound(resolved_path),
        known_late_diodes=names, source_artifact_sha256=base['source_artifact_sha256'] if 'source_artifact_sha256' in base else
        'b8b0a29851369f2b181b67db77778979703a30adc92051e2992a2e8fb98dc971',
        producer_commit=commit, producer_sha256=sources, producer_dependency_closure=closure,
        input_sha256=P.inventory(inputs), semantic_state_bits=6039, clock_period_ns=20,
        candidate_delta='only PG-aware new-diode placement/access and refreshed affected guides; canonical scripts retained as bound overlays',
        native_executed=False, eligible_final_target=False, physical_acceptance=False,
        model_qualified=False, qualified_timing=False)
    if initial_authority: packet['original_initial_config'] = initial_authority
    P.write(output / 'preparation.json', packet)
    verify(output); return packet


def verify(output, workspace=None):
    workspace_context(workspace)
    output = Path(output).resolve(); packet = P.read(output / 'preparation.json')
    require(packet['schema'] == 'pinwheel.closure24-pg-flow-preparation.v1' and
            packet['mode'] in MODES and packet['policy'] in ('A', 'B') and
            packet['native_executed'] is False and packet['eligible_final_target'] is False and
            packet['physical_acceptance'] is False and P.inventory(output / 'inputs') == packet['input_sha256'],
            'Frozen PG flow packet changed')
    require(bound(packet['source_odb']['path']) == packet['source_odb'], 'Seed ODB changed')
    require(bound(packet['original_resolved_config']['path']) == packet['original_resolved_config'],
            'Original resolved configuration changed')
    require(bound(packet['historical_replay_preparation']['path']) == packet['historical_replay_preparation'],
            'Historical seed preparation changed')
    replay = Path(packet['historical_replay_preparation']['path']).parent
    initial = None
    if packet.get('diagnostic_config_version', 1) == 2:
        original = initial_config_authority(P.read(replay / 'preparation.json'))
        require(packet.get('original_initial_config') == original and
                sha(output / 'inputs/historical-initial-config.json') == original['sha256'] and
                (output / 'inputs/historical-drt-config.json').read_bytes() == (replay / 'inputs/config.json').read_bytes(),
                'Staged exact initial/DRT configuration authority changed')
        initial = P.read(output / 'inputs/historical-initial-config.json')
    actual_config = P.read(output / 'inputs/config.json')
    validate_diagnostic_config(actual_config, packet, P.read(replay / 'inputs/config.json'), initial)
    require(actual_config == diagnostic_config(packet,
            P.read(replay / 'inputs/config.json'), initial),
            'Diagnostic configuration differs from exact historical values and declared adapter')
    base_path = Path(packet['original_preparation']['path'])
    require(bound(base_path) == packet['original_preparation'], 'Original preparation seal differs')
    base = P.verify(base_path.parent)
    old = P.read(packet['historical_replay_preparation']['path'])
    require(packet['pdk_root'] == base['pdk_root'] and packet['runtime'] == old['runtime'] and
            old['original_preparation'] == packet['original_preparation'] and
            packet['semantic_state_bits'] == 6039 and packet['clock_period_ns'] == 20,
            'Original input/PDK/runtime/semantic contract changed')
    ledger = ROOT / CAMPAIGN / 'physical-variants' / ('variant-%02d.json' % packet['variant']['ordinal'])
    require(P.read(ledger) == packet['variant'], 'Campaign-wide physical variant registration changed')
    verify_variant_authority(packet['variant'])
    # Executed snapshot plus immutable Git object are the source authority.
    staged = output / 'inputs/producer'
    require(dependency_closure(staged, (OWN, PLUGIN, HELPER)) == packet['producer_dependency_closure'],
            'Frozen producer dependency membership differs')
    for name, expected in packet['producer_sha256'].items():
        require(sha(staged / name) == expected, 'Frozen producer changed: ' + name)
        raw = subprocess.check_output(['git', 'show', packet['producer_commit'] + ':' + name], cwd=ROOT)
        require(hashlib.sha256(raw).hexdigest() == expected, 'Producer is not its committed Git source')
    return packet


def resolved_contract(packet, output):
    path = Path(output) / 'flow/resolved.json'
    if not path.exists():
        return dict(observed=False, validated=False, reason='Native stopped before resolved configuration')
    before = P.read(packet['original_resolved_config']['path']); after = P.read(path)
    expected = dict(before)
    expected['OPENROAD_THREADS'] = thread_count(packet)
    if before.get('meta') != after.get('meta'):
        require(type(before.get('meta')) is dict and after.get('meta') == dict(before['meta'], flow=FLOW),
                'Undeclared resolved flow metadata change')
        expected['meta'] = after['meta']
    require(after == expected and after['CLOCK_PERIOD'] == 20 and after['PL_TARGET_DENSITY_PCT'] == 85 and
            after['DRT_OPT_ITERS'] == 64 and after['OPENROAD_THREADS'] == thread_count(packet) and
            all(after[key] is False for key in ('RUN_EQY','RUN_KLAYOUT_XOR','RUN_LINTER')),
            'Actual resolved candidate changes preserved physical/semantic rules')
    return dict(observed=True, validated=True, original=packet['original_resolved_config'], actual=bound(path),
                delta={key:dict(before=before.get(key),after=after.get(key)) for key in after if before.get(key) != after.get(key)})


def native_step(mode):
    from librelane.steps import openroad
    from librelane.steps.tclstep import TclStep
    from librelane.state import State
    root = Path('/work/closure'); inputs = root / 'inputs'
    packet = P.read('/work/preparation.json')
    require(packet['schema'] == 'pinwheel.closure24-pg-flow-preparation.v1' and packet['mode'] == mode and
            packet['semantic_state_bits'] == 6039 and packet['clock_period_ns'] == 20,
            'Native candidate mode/contract changed')
    cgroup = Path('/sys/fs/cgroup')
    limits = {name:(cgroup / name).read_text().strip() for name in ('cpu.max','memory.max','memory.swap.max','pids.max')}
    cpu = limits['cpu.max'].split()
    threads = thread_count(packet)
    require(len(cpu) == 2 and all(v.isdigit() for v in cpu) and int(cpu[0]) == threads * int(cpu[1]) and
            limits['memory.max'] == str(6*1024**3) and limits['memory.swap.max'] == '0' and limits['pids.max'] == '256',
            'Native PG container resource policy differs')
    P.write('/work/metadata/native-limits.json', limits)
    RR.package_unchanged(Path(openroad.__file__).resolve().parents[1], packet['native_package_sha256'])
    require(sha('/work/seed.odb') == packet['source_odb']['sha256'] and P.inventory(inputs) == packet['input_sha256'],
            'Native PG flow input changed')
    if mode == 'full':
        from librelane_plugin_streaming_8x4_pg24 import Streaming8x4PGClosure24
        from librelane_plugin_streaming_8x4 import Streaming8x4Certified
        actual = [step.id for step in Streaming8x4PGClosure24.Steps]
        expected = [step.id for step in Streaming8x4Certified.Steps]
        expected.insert(expected.index('OpenROAD.DetailedRouting'), BOOTSTRAP)
        require([step.id for step in Streaming8x4Certified.Steps] == packet['canonical_flow_steps'] and
                actual == expected and tuple(actual[actual.index('OpenROAD.DetailedRouting'):]) == R.TAIL,
                'Full candidate omits or changes ordinary flow tail')
        P.write('/work/metadata/flow-order.json', dict(original_steps=[step.id for step in Streaming8x4Certified.Steps],
            actual_steps=actual, canonical_tail=list(R.TAIL), ordinary_tail_preserved=True,
            source_overlay=True, disabled_is_not_executed=True, qualified=False))
        command = [sys.executable, '-B', '-m', 'librelane', '--manual-pdk', '--pdk-root', '/work/pdk',
            '--pdk', 'ihp-sg13cmos5l', '--jobs', str(threads), '--flow', FLOW,
            '--override-config', 'OPENROAD_THREADS='+str(threads), '--run-tag', 'pg-closure24',
            '--force-run-dir', '/work/run', '--with-initial-state', '/work/closure/inputs/seed.json',
            '--from', BOOTSTRAP, '--to', 'Misc.ReportManufacturability', '/work/inputs/core.json']
        os.execv(sys.executable, command)
    base = openroad.DetailedRouting if mode == 'late-smoke' else openroad._DiodeInsertion
    class Smoke(base):
        id = 'Pinwheel.PGDiodeSmoke'
        name = 'PG-aware diode path diagnostic'
        outputs = [] if mode == 'late-smoke' else base.outputs
        def get_script_path(self):
            return str(inputs / ('late-smoke.tcl' if mode == 'late-smoke' else 'initial-pg.tcl'))
    if packet.get('diagnostic_config_version', 1) == 2:
        require(packet.get('original_initial_config', {}).get('sha256') == INITIAL_CONFIG_SHA256 and
                sha(inputs / 'historical-initial-config.json') == INITIAL_CONFIG_SHA256,
                'Native initial source configuration differs')
        binding = validate_diagnostic_config(P.read(inputs / 'config.json'), packet,
            P.read(inputs / 'historical-drt-config.json'), P.read(inputs / 'historical-initial-config.json'))
        P.write('/work/metadata/diagnostic-config-binding.json', dict(binding,
            actual_config_sha256=sha(inputs / 'config.json'),
            baseline_drt_sha256=sha(inputs / 'historical-drt-config.json'),
            exact_initial_membership_and_values=True, qualified=False))
    else:
        validate_diagnostic_config(P.read(inputs / 'config.json'), packet)
    config = Smoke._load_config_from_file(inputs / 'config.json', '/work/pdk')
    step = Smoke(config, State.load(dict(odb='/work/seed.odb', metrics={})))
    step.start(step_dir='/work/run/step')


def container_command(preparation, output, packet, name, owner):
    base = Path(packet['original_preparation']['path']).parent
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+', name) and str(uuid.UUID(owner)) == owner,
            'Invalid PG candidate ownership')
    return ['docker', 'run', '--rm', '--pull', 'never', '--name', name,
        '--label', 'org.pinwheel.streaming8_owner=' + owner, '--network', 'none',
        '--cpus', str(thread_count(packet)), '--memory', '6g', '--memory-swap', '6g', '--pids-limit', '256',
        '--env', 'PYTHONDONTWRITEBYTECODE=1', '--env',
        'PYTHONPATH=/work/closure/inputs:/work/inputs:/work/closure/inputs/producer/scripts',
        '--mount', f'type=bind,source={preparation / "inputs"},target=/work/closure/inputs,readonly',
        '--mount', f'type=bind,source={preparation / "preparation.json"},target=/work/preparation.json,readonly',
        '--mount', f'type=bind,source={base / "inputs"},target=/work/inputs,readonly',
        '--mount', f'type=bind,source={packet["pdk_root"]},target=/work/pdk,readonly',
        '--mount', f'type=bind,source={packet["source_odb"]["path"]},target=/work/seed.odb,readonly',
        '--mount', f'type=bind,source={output / "flow"},target=/work/run',
        '--mount', f'type=bind,source={output / "metadata"},target=/work/metadata',
        '--workdir', '/work/inputs', packet['runtime']['image_id'], 'python3', '-B',
        '/work/closure/inputs/producer/' + OWN, 'native-step', '--mode', packet['mode']]


def run(preparation, output, name, timeout, frozen=False):
    preparation = Path(preparation).resolve(); packet = verify(preparation)
    worker = preparation / 'inputs/producer' / OWN
    if not frozen:
        os.execv(sys.executable, [sys.executable, '-B', str(worker), 'run', '--preparation', str(preparation),
            '--output', str(Path(output).absolute()), '--name', name, '--timeout', str(timeout),
            '--workspace', str(ROOT), '--frozen'])
    require(Path(__file__).resolve() == worker.resolve(), 'Execute the exact frozen worker')
    full_limit = NATIVE_RESOURCES['full_leaf_seconds_cap'] if 'resource_policy' in packet else 10800
    require(type(timeout) is int and 1 <= timeout <= (full_limit if packet['mode'] == 'full' else 1800),
            'Declared PG flow job cap exceeded')
    output = Path(output).absolute(); require(not output.exists(), 'Preserve prior Native owner')
    output.mkdir(parents=True); (output / 'flow').mkdir(); (output / 'metadata').mkdir()
    runtime = inspect_runtime(P.read(ROOT / 'tools/physical-toolchain.json'))
    require(runtime == packet['runtime'], 'Selected actual runtime differs')
    owner = str(uuid.uuid4()); argv = container_command(preparation, output, packet, name, owner)
    receipt = dict(schema='pinwheel.closure24-pg-native-run.v1', mode=packet['mode'], policy=packet['policy'],
        variant=packet['variant'], status='running', exit_code=None, preparation=bound(preparation / 'preparation.json'),
        original_preparation=packet['original_preparation'], argv=argv, runtime=runtime,
        source_odb=packet['source_odb'], ownership_label=owner, container_name=name,
        source_ff_bits=6039, clock_period_ns=20, tiles='8x4', parent_is_not_final_target=True,
        started_utc=datetime.now(timezone.utc).isoformat(), qualified=False, physical_acceptance=False,
        model_qualified=False, qualified_timing=False,
        configured_disabled_checks={name:False for name in ('RUN_EQY','RUN_KLAYOUT_XOR','RUN_LINTER')})
    R.write(output / 'report.json', receipt)
    started = time.monotonic(); process = None; previous = signal.getsignal(signal.SIGTERM)
    def interrupted(signum, frame): raise KeyboardInterrupt('signal ' + str(signum))
    signal.signal(signal.SIGTERM, interrupted)
    with (output / 'native.log').open('w') as log:
        try:
            process = subprocess.Popen(argv, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            code = process.wait(timeout=timeout)
            receipt.update(exit_code=code, status='flow_completed' if code == 0 else 'failed')
        except subprocess.TimeoutExpired: receipt.update(exit_code=124, status='timed_out')
        except KeyboardInterrupt as error: receipt.update(exit_code=130, status='interrupted', error=str(error))
        except BaseException as error: receipt.update(exit_code=127, status='blocked', error=type(error).__name__+': '+str(error))
        finally:
            receipt['container_termination'] = R.cleanup(owner, log)
            if process is not None and process.poll() is None:
                os.killpg(process.pid, signal.SIGTERM)
                try: process.wait(timeout=5)
                except subprocess.TimeoutExpired: os.killpg(process.pid, signal.SIGKILL); process.wait(timeout=5)
            signal.signal(signal.SIGTERM, previous)
            try:
                require(verify(preparation) == packet and inspect_runtime(P.read(ROOT / 'tools/physical-toolchain.json')) == runtime,
                        'PG candidate input/runtime changed')
                receipt['inputs_pdk_runtime_unchanged'] = True
                if packet['mode'] == 'full': receipt['resolved_contract'] = resolved_contract(packet, output)
            except BaseException as error:
                receipt.update(status='invalidated', inputs_pdk_runtime_unchanged=False, closeout_error=str(error))
            if receipt['container_termination']['status'] != 'absent': receipt['status'] = 'cleanup_unconfirmed'
            try:
                receipt['states'] = R.states(output, Path(packet['original_preparation']['path']).parent, Path(packet['pdk_root']))
            except BaseException as error: receipt.update(status='invalidated', state_inventory_error=str(error))
            receipt['elapsed_seconds'] = time.monotonic() - started
            receipt['artifact_sha256'] = {str(path.relative_to(output)):sha(path) for path in sorted(output.rglob('*'))
                                          if path.is_file() and path != output / 'report.json'}
            R.write(output / 'report.json', receipt)
    print(output / 'report.json', flush=True)
    return receipt


def select_report(report_path, report_sha256, workspace=None):
    workspace_context(workspace)
    path = regular(report_path).resolve(); require(sha(path) == report_sha256, 'Closed physical report changed')
    report = P.read(path)
    require(report['schema'] == 'pinwheel.closure24-pg-native-run.v1' and report['mode'] == 'full' and
            ((report['status'] == 'flow_completed' and report['exit_code'] == 0) or
             (report['status'] == 'failed' and type(report['exit_code']) is int and report['exit_code'] != 0)) and
            report['inputs_pdk_runtime_unchanged'] is True and
            report['container_termination']['status'] == 'absent',
            'Only closed full-flow terminal evidence can supply a target')
    packet = verify(Path(report['preparation']['path']).parent)
    require(bound(report['preparation']['path']) == report['preparation'], 'Preparation seal differs')
    require(packet['mode'] == 'full' and packet['variant'] == report['variant'] and
            packet['policy'] == report['policy'] and report['source_ff_bits'] == 6039 and
            report['clock_period_ns'] == 20 and report['tiles'] == '8x4' and
            report['parent_is_not_final_target'] is True,
            'Reported full candidate/semantic identity differs')
    actual = {str(p.relative_to(path.parent)):sha(p) for p in path.parent.rglob('*') if p.is_file() and p != path}
    require(actual == report['artifact_sha256'], 'Complete physical artifact membership differs')
    order = P.read(path.parent / 'metadata/flow-order.json')
    expected_steps = list(packet['canonical_flow_steps'])
    expected_steps.insert(expected_steps.index('OpenROAD.DetailedRouting'), BOOTSTRAP)
    require(order['original_steps'] == packet['canonical_flow_steps'] and order['actual_steps'] == expected_steps and
            order['canonical_tail'] == list(R.TAIL) and order['ordinary_tail_preserved'] is True and
            order['source_overlay'] is True and order['disabled_is_not_executed'] is True and
            order['qualified'] is False and report['resolved_contract'] == resolved_contract(packet, path.parent) and
            report['resolved_contract']['validated'] is True,
            'Actual full flow order or resolved contract differs')
    flow = (path.parent / 'flow').resolve()
    reported_states = [regular(row['state']).resolve() for row in report['states']]
    require(len(set(reported_states)) == len(reported_states) and
            set(reported_states) == {p.resolve() for p in flow.rglob('state_out.json')},
            'Reported completed-state universe is missing, extra or duplicated')
    rows = []
    for row in report['states']:
        state = regular(row['state']).resolve()
        require(sha(state) == row['state_sha256'] == actual.get(str(state.relative_to(path.parent))),
                'Completed state bytes are not their closed artifact')
        if state.parent.parent != path.parent / 'flow': continue
        match = re.fullmatch(r'(\d+)-(.+)', state.parent.name)
        require(match is not None and sha(state) == row['state_sha256'], 'State order or bytes changed')
        view = row['views']['odb']
        odb = regular(view['path']).resolve()
        require(odb.is_relative_to(flow) and sha(odb) == view['sha256'] and
                actual.get(str(odb.relative_to(path.parent))) == view['sha256'] and
                P.read(state)['odb'] == view['container'] == '/work/run/' + str(odb.relative_to(flow)),
                'State ODB is outside this fresh authenticated flow')
        rows.append((int(match[1]), row, state, odb))
    require(len({row[0] for row in rows}) == len(rows), 'Duplicate top-level state order')
    drt = [row for row in rows if row[1]['step_directory'].endswith('-openroad-detailedrouting')]
    bootstrap = [row for row in rows if row[1]['step_directory'].endswith('-pinwheel-pgdiodebootstrap')]
    require(len(drt) == len(bootstrap) == 1 and bootstrap[0][0] < drt[0][0],
            'No unique completed whole DetailedRouting and PG bootstrap')
    require(all(row[3].parent == row[2].parent for row in (*drt, *bootstrap)),
            'Bootstrap/DRT must produce fresh ODBs in their own stage directories')
    producers = {row[3]:row[0] for row in rows if row[3].parent == row[2].parent}
    require(all(row[3] in producers and producers[row[3]] <= row[0] for row in rows),
            'Carried ODB has no authenticated earlier fresh completed producer')
    latest = max(rows, key=lambda row:row[0])
    require(latest[0] >= drt[0][0] and sha(path) == report_sha256, 'Final physical target changed')
    return dict(schema='pinwheel.closure24-pg-final-target.v1', physical_report=bound(path),
        physical_status=report['status'], physical_exit_code=report['exit_code'],
        completed_detailed_route_state=bound(drt[0][2]), physical_state=bound(latest[2]),
        actual_odb=bound(latest[3]), latest_step=latest[1]['step_directory'],
        physical_candidate_kind='pg-aware-antenna-access24', variant=packet['variant'],
        original_preparation=packet['original_preparation'], pg_preparation=report['preparation'],
        parent_is_not_final_target=True, target_scope='final-routed-digital-pending-proof',
        physical_acceptance=False, post_pnr_equivalence_proved=False, model_qualified=False)


def main():
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('prepare'); p.add_argument('--mode', choices=MODES, required=True)
    p.add_argument('--policy', choices=('A','B'), required=True); p.add_argument('--output', type=Path, required=True)
    p = sub.add_parser('verify'); p.add_argument('--preparation', type=Path, required=True)
    p = sub.add_parser('run')
    for name in ('preparation','output'): p.add_argument('--'+name, type=Path, required=True)
    p.add_argument('--name', required=True); p.add_argument('--timeout', type=int, required=True)
    p.add_argument('--workspace', type=Path); p.add_argument('--frozen', action='store_true')
    p = sub.add_parser('native-step'); p.add_argument('--mode', choices=MODES, required=True)
    args = parser.parse_args()
    if getattr(args, 'workspace', None): ROOT = args.workspace.resolve(); P.ROOT = ROOT
    if args.command == 'prepare': result = prepare(args.mode, args.policy, args.output)
    elif args.command == 'verify': result = verify(args.preparation)
    elif args.command == 'native-step': return native_step(args.mode)
    else:
        result = run(args.preparation,args.output,args.name,args.timeout,args.frozen)
        return result['exit_code'] or (0 if result['status']=='flow_completed' else 2)
    print(json.dumps({key:result.get(key) for key in ('schema','mode','policy','physical_acceptance')}, sort_keys=True))


if __name__ == '__main__': raise SystemExit(main())
