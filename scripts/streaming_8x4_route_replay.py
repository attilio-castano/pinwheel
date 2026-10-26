"""Diagnostic replay of the sole repaired candidate's saved clean internal ODB.

This is neither another physical candidate nor a completed DetailedRouting
authority. Fresh readDesign can differ from the old process's updateDesign.
Root GO and the separate campaign guard are required for Native execution.
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
import time
import uuid

sys.dont_write_bytecode = True
import process_group
import streaming_8x4_prepare as P
import streaming_8x4_postantenna_repair as J
import streaming_8x4_run as R
import streaming_8x4_signoff_execute as V
from streaming_8x4_geometry import regular, require, sha
from streaming_tt_intake import dependency_closure
from streaming_tt_physical import inspect_runtime

OWN = 'scripts/streaming_8x4_route_replay.py'
ENTRIES = (OWN, 'tools/physical-toolchain.json')
COMMIT = 'dcf36133a369abc8f3c5e5738cd4d82e4903c0e0'
PARENT_SHA = 'cb6df6542c12ebefd6e7a220f624e6465a59fccbcdcbb00645e75f01db5c8943'
RESOURCE_SHA = '237d48c6b349ab7de03f1e72143acf829eb70ff3060e5582c588d0ec5312e68a'
SEED_SHA = '596af58622f1e194f4e55897e0c27c1420a28450c8d2848fa913849eb877f0d8'
DRT_TCL_SHA = 'e7e4e4984dff976e96fdf42561b185000bc2a9a3a21553b9bc781cfaef94447f'
SOURCE_SHA = 'c047454e404408023508a1930a9d897e812e0fd6a3a18877303af55235f03425'
EXPECTED = dict(net_violations=35, pin_violations=36, inserted_diodes=39)
TOP = 'tt_um_pinwheel_streaming_ready_d2'


def bound(path):
    return dict(path=str(regular(path).resolve()), sha256=sha(path))


def policy():
    return dict(cpus=4, memory_gib=6, swap_extra_gib=0, threads=4, leaf_seconds=1770,
        work_seconds=1800, outer_seconds=1860, droute_end_iter=6, seed=42,
        historical_droute_end_iter=64, expected_reproduction=EXPECTED,
        new_physical_candidate=False, physical_delta=False, completed_DetailedRouting=False,
        eligible_final_target=False, physical_acceptance=False, qualified=False,
        historical_placements_identical=False,
        fresh_process_limit='readDesign reconstructs state; historical second DRT used updateDesign',
        scope='Same-candidate antenna/routing reproduction and shape diagnosis only')


def validate_config(config):
    exact = dict(OPENROAD_THREADS=4, RT_MIN_LAYER='Metal2', RT_MAX_LAYER='Metal4',
        CLOCK_PERIOD=20, DRT_OPT_ITERS=64,
        GRT_ANTENNA_REPAIR_MARGIN=10, DRT_ANTENNA_REPAIR_MARGIN=10,
        GRT_ALLOW_CONGESTION=False, DRT_ANTENNA_REPAIR_JUMPER_ONLY=False,
        DRT_ANTENNA_REPAIR_DIODE_ONLY=False, DRT_SAVE_SNAPSHOTS=False,
        DRT_SAVE_DRC_REPORT_ITERS=None, NON_DEFAULT_RULES=None, DRT_ASSIGN_NDR=None,
        DRT_DISABLE_AUTO_TAPER=None, DIODE_CELL='sg13cmos5l_antennanp',
        PNR_SDC_FILE='/work/inputs/core.sdc', DESIGN_NAME=TOP)
    require(all(config.get(k) == v for k, v in exact.items()), 'Historical DRT config/options differ')
    return exact


def source_evidence(root):
    root = Path(root).resolve(); require(sha(root / 'manifest.json') == SOURCE_SHA, 'Replay source manifest differs')
    packet = P.read(root / 'manifest.json')
    require(packet['schema'] == 'pinwheel.streaming-8x4-route-replay-source.v1' and
        packet['commit'] == COMMIT and packet['native_executed'] is False, 'Replay source intake differs')
    expected = {'manifest.json': sha(root / 'manifest.json')}
    for row in packet['files']:
        name = row['path']; require(Path(name).name == name and name not in expected, 'Unsafe duplicate source')
        data = regular(root / name).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(row['bytes'] == len(data) and row['sha256'] == sha(root / name) and row['git_blob'] == blob and
            row['url'].startswith('https://github.com/The-OpenROAD-Project/OpenROAD/blob/' + COMMIT + '/'),
            'Pinned replay source bytes/blob differ')
        expected[name] = row['sha256']
    require(set(expected) == {'manifest.json', 'GlobalRouter.cpp', 'GlobalRouter.tcl', 'RepairAntennas.cpp',
        'TritonRoute.cpp', 'TritonRoute.tcl', 'FlexDR.cpp', 'AntennaChecker.cc', 'AntennaChecker.i',
        'AntennaChecker.tcl', 'Utl.tcl', 'OpenRoad.i', 'OpenRoad.cc'} and P.inventory(root) == expected,
        'Replay source membership differs')
    return expected


def parent_authority(report_path, resource_path):
    report_path = regular(report_path).resolve(); resource_path = regular(resource_path).resolve()
    require(sha(report_path) == PARENT_SHA and sha(resource_path) == RESOURCE_SHA, 'Not the closed sole repair02')
    row = P.read(report_path); resource = P.read(resource_path)
    require(row['schema'] == 'pinwheel.streaming-8x4-postantenna-repair-run.v1' and
        row['status'] == 'interrupted' and row['exit_code'] == 130 and row['error'] == 'signal 15' and
        row['inputs_pdk_runtime_unchanged'] is True and row['container_termination']['status'] == 'absent' and
        resource['status'] == 'stopped' and resource['exit_code'] == 124 and resource['cleanup_confirmed'] is True and
        resource['inputs_unchanged'] is True and resource['owned_processes_remaining'] == [] and
        resource['containers_remaining'] == [] and resource['cleanup_errors'] == [], 'Parent was not closed and preserved')
    require(P.inventory(report_path.parent) == dict(row['artifact_sha256'], **{'report.json': PARENT_SHA}),
        'Closed repair full artifact inventory changed')
    prep = row['preparation']; require(bound(prep['path']) == prep, 'Repair preparation changed')
    record = J.verify(Path(prep['path']).parent)
    flow = report_path.parent / 'flow'; step = flow / '03-openroad-detailedrouting'
    require(not (step / 'state_out.json').exists(), 'Diagnostic intake must preserve incomplete parent DRT')
    seed = step / 'drt-run-0' / (TOP + '.odb')
    require(sha(seed) == SEED_SHA and (step / 'drt-run-0' / (TOP + '.drc')).read_bytes() == b'',
        'Not the exact saved clean internal database')
    config = P.read(step / 'config.json'); validate_config(config)
    historical = 'openroad -exit -threads 4 -no_splash -metrics /work/run/03-openroad-detailedrouting/or_metrics_out.json '
    require((step / 'COMMANDS').read_text().startswith(historical) and
        (step / 'COMMANDS').read_text().strip().endswith('/librelane/scripts/openroad/drt.tcl'),
        'Historical actual native argv differs')
    log = (step / 'openroad-detailedrouting.log').read_text()
    require(log.count('Inserted 39 diodes.') == 1 and 'Found 35 net violations.' in log and
        'Found 36 pin violations.' in log and
        'detailed_route -droute_end_iter 64 -or_seed 42 -verbose 1' in (report_path.parent / 'native.log').read_text(),
        'Historical actual antenna/route command evidence differs')
    return row, record, seed, step


def snapshot(inputs):
    closure = dependency_closure(P.ROOT, ENTRIES)
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P.ROOT, text=True, timeout=30).strip()
    sources = {}
    for name in closure['files']:
        data = subprocess.check_output(['git', 'show', head + ':' + name], cwd=P.ROOT, timeout=30)
        require(hashlib.sha256(data).hexdigest() == sha(P.ROOT / name), 'Commit replay source first: ' + name)
        target = inputs / 'producer' / name; target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(data)
        sources[name] = sha(target)
    return head, sources, closure


def prepare(parent, resource, source_root, output):
    parent, resource = map(lambda p: regular(p).resolve(), (parent, resource))
    row, original, seed, step = parent_authority(parent, resource)
    source_files = source_evidence(source_root); source_root = Path(source_root).resolve()
    output = Path(output).absolute(); require(not output.exists(), 'Preserve previous replay preparation')
    inputs = output / 'inputs'; inputs.mkdir(parents=True)
    head, sources, closure = snapshot(inputs)
    for name in source_files:
        target = inputs / 'openroad-source' / name; target.parent.mkdir(exist_ok=True)
        shutil.copyfile(source_root / name, target)
    shutil.copyfile(step / 'config.json', inputs / 'config.json')
    (inputs / 'replay.tcl').write_text(replay_tcl())
    package = original['request']['native_package_sha256']
    require(package['scripts/openroad/drt.tcl'] == DRT_TCL_SHA, 'Canonical DRT source changed')
    packet = dict(schema='pinwheel.streaming-8x4-route-replay-preparation.v1', policy=policy(),
        parent_report=bound(parent), parent_resource=bound(resource), source_odb=bound(seed),
        historical_config=bound(step / 'config.json'), historical_commands=bound(step / 'COMMANDS'),
        historical_env=bound(step / '_env.tcl'), source_root=str(source_root), source_evidence_sha256=source_files,
        original_preparation=original['original_preparation'], repair_preparation=row['preparation'],
        runtime=row['runtime'], native_package_sha256=package, producer_commit=head, producer_sha256=sources,
        producer_dependency_closure=closure, input_sha256=P.inventory(inputs), native_executed=False,
        physical_acceptance=False, eligible_final_target=False)
    P.write(output / 'preparation.json', packet); verify(output); return packet


def verify(output):
    output = Path(output).resolve(); packet = P.read(output / 'preparation.json')
    require(packet['schema'] == 'pinwheel.streaming-8x4-route-replay-preparation.v1' and packet['policy'] == policy() and
        packet['native_executed'] is False and packet['physical_acceptance'] is False and
        packet['eligible_final_target'] is False and P.inventory(output / 'inputs') == packet['input_sha256'],
        'Replay preparation bytes/claims differ')
    for key in ('parent_report', 'parent_resource', 'source_odb', 'historical_config', 'historical_commands',
        'historical_env', 'original_preparation', 'repair_preparation'):
        require(bound(packet[key]['path']) == packet[key], 'Replay authority changed: ' + key)
    row, original, seed, step = parent_authority(packet['parent_report']['path'], packet['parent_resource']['path'])
    require(packet['source_odb'] == bound(seed) and packet['runtime'] == row['runtime'] and
        packet['native_package_sha256'] == original['request']['native_package_sha256'] and
        packet['original_preparation'] == original['original_preparation'] and
        packet['repair_preparation'] == row['preparation'], 'Replay parent/candidate identity differs')
    require(source_evidence(packet['source_root']) == packet['source_evidence_sha256'] ==
        source_evidence(output / 'inputs/openroad-source'), 'Replay source evidence differs')
    require((output / 'inputs/config.json').read_bytes() == (step / 'config.json').read_bytes() and
        (output / 'inputs/replay.tcl').read_text() == replay_tcl(), 'Replay config/body changed')
    require(dependency_closure(P.ROOT, ENTRIES) == packet['producer_dependency_closure'] and
        set(packet['producer_sha256']) == set(packet['producer_dependency_closure']['files']), 'Replay closure changed')
    for name, digest in packet['producer_sha256'].items():
        require(sha(P.ROOT / name) == digest == sha(output / 'inputs/producer' / name), 'Replay producer changed')
        data = subprocess.check_output(['git', 'show', packet['producer_commit'] + ':' + name], cwd=P.ROOT, timeout=30)
        require(hashlib.sha256(data).hexdigest() == digest, 'Replay producer commit differs')
    P.verify(Path(packet['original_preparation']['path']).parent)
    return packet


def replay_tcl():
    return r'''# Fresh diagnostic body; original drt.tcl is separately pinned and unchanged.
source $::env(SCRIPTS_DIR)/openroad/common/io.tcl
read_current_odb
set replay /work/replay/step
proc replay_need {ok message} { if {!$ok} { error $message } }
set describe_return [tee -variable describe_printed {ord::openroad_git_describe}]
set version_return [tee -variable version_printed {ord::openroad_version}]
foreach {name value} [list describe-return $describe_return describe-printed $describe_printed version-return $version_return version-printed $version_printed] {
    set stream [open $replay/$name.txt w]; puts -nonewline $stream $value; close $stream
}
set replay_hashes [list]
foreach token [regexp -all -inline {[0-9a-f]+} "$describe_return $describe_printed $version_return $version_printed"] {
    if {[string length $token] >= 40} { lappend replay_hashes $token }
}
set replay_hashes [lsort -unique $replay_hashes]
replay_need [expr {$replay_hashes eq {dcf36133a369abc8f3c5e5738cd4d82e4903c0e0}}] {Pinned OpenROAD revision mismatch/empty observation}
puts {PINWHEEL_REPLAY_OPENROAD dcf36133a369abc8f3c5e5738cd4d82e4903c0e0}
proc replay_row {stream args} {
    foreach value $args { replay_need [expr {![regexp {[\t\r\n]} $value]}] {Unsupported census identifier} }
    puts $stream [join $args "\t"]
}
proc replay_capture {prefix} {
    set block [ord::get_db_block]
    write_db ${prefix}.odb
    write_def ${prefix}.def
    write_verilog -include_pwr_gnd ${prefix}.v
    set stream [open ${prefix}.tsv w]
    replay_row $stream TOP [$block getName]
    foreach inst [$block getInsts] {
        replay_row $stream INST [$inst getName] [[$inst getMaster] getName] {*}[ $inst getLocation ] [$inst getOrient] [$inst getPlacementStatus]
        foreach term [$inst getITerms] {
            set net [$term getNet]; set net_name ""
            if {$net ne "NULL"} { set net_name [$net getName] }
            set mterm [$term getMTerm]
            replay_row $stream ITERM [$inst getName] [$mterm getName] [$mterm getIoType] [$mterm getSigType] $net_name
        }
    }
    foreach net [$block getNets] {
        replay_row $stream NET [$net getName] [$net getSigType] [llength [$net getITerms]] [llength [$net getBTerms]]
    }
    foreach term [$block getBTerms] {
        set net [$term getNet]; set net_name ""
        if {$net ne "NULL"} { set net_name [$net getName] }
        replay_row $stream BTERM [$term getName] [$term getIoType] [$term getSigType] $net_name
    }
    close $stream
}
replay_capture $replay/before
set nets [tee -variable antenna_log {check_antennas}]
set stream [open $replay/antenna-before.log w]; puts -nonewline $stream $antenna_log; close $stream
set net_matches [regexp -all -inline {\[INFO ANT-0002\] Found ([0-9]+) net violations\.} $antenna_log]
set pin_matches [regexp -all -inline {\[INFO ANT-0001\] Found ([0-9]+) pin violations\.} $antenna_log]
replay_need [expr {$nets == 35 && [llength $net_matches] == 2 && [lindex $net_matches 1] == 35 && [llength $pin_matches] == 2 && [lindex $pin_matches 1] == 36}] {Historical 35net/36pin antenna reproduction failed}
set before_count [llength [[ord::get_db_block] getInsts]]
set inserted [log_cmd repair_antennas sg13cmos5l_antennanp -ratio_margin 10]
set after_count [llength [[ord::get_db_block] getInsts]]
replay_capture $replay/postdiode
write_guides $replay/postdiode.guide
replay_need [expr {$inserted == 39 && $after_count - $before_count == 39}] {Historical 39diode reproduction failed}
set stream [open $replay/reproduction.tsv w]
puts $stream "net_violations\t$nets\npin_violations\t36\ninserted_diodes\t$inserted\nbefore_instances\t$before_count\nafter_instances\t$after_count"
close $stream
puts {PINWHEEL_REPLAY_REPRODUCTION_GATE_PASSED}; flush stdout
log_cmd detailed_route -droute_end_iter 6 -or_seed 42 -verbose 1 -drc_report_iter_step 1 -output_drc $replay/bounded.drc
replay_capture $replay/postroute
write_guides $replay/postroute.guide
puts {PINWHEEL_REPLAY_BOUNDED_ROUTE_RETURNED}; flush stdout
'''


def package_unchanged(root, expected):
    actual = {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob('*'))
        if p.is_file() and '__pycache__' not in p.parts and p.suffix != '.pyc'}
    require(actual == expected, 'Native canonical package changed')


def native_step():
    from librelane.steps import openroad
    from librelane.steps.tclstep import TclStep
    from librelane.state import State
    packet = P.read('/work/replay/preparation.json'); inputs = Path('/work/replay/inputs')
    package = Path(openroad.__file__).resolve().parents[1]
    package_unchanged(package, packet['native_package_sha256'])
    require(sha('/work/seed.odb') == SEED_SHA and (inputs / 'replay.tcl').read_text() == replay_tcl() and
        P.inventory(inputs) == packet['input_sha256'], 'Native replay input changed')
    class RouteReplay(openroad.DetailedRouting):
        id = 'Pinwheel.RouteReplayDiagnostic'
        name = 'Same-candidate diagnostic replay'
        outputs = []
        def get_script_path(self): return '/work/replay/inputs/replay.tcl'
    delegate = TclStep.run_subprocess; journal = Path('/work/replay/native-journal.jsonl')
    def observed(self, command, *args, **kwargs):
        start = dict(event='start', argv=[str(x) for x in command], step=self.id,
            env={str(k): str(v) for k, v in kwargs['env'].items()},
            executable_sha256=sha(Path(shutil.which(str(command[0]))).resolve()))
        with journal.open('a') as stream: stream.write(json.dumps(start, sort_keys=True) + '\n')
        code = None
        try:
            result = delegate(self, command, *args, **kwargs); code = result['returncode']; return result
        finally:
            with journal.open('a') as stream: stream.write(json.dumps(dict(event='finish', exit_code=code), sort_keys=True) + '\n')
    TclStep.run_subprocess = observed
    try:
        config = RouteReplay._load_config_from_file(inputs / 'config.json', '/work/pdk')
        validate_config(P.read(inputs / 'config.json'))
        step = RouteReplay(config, State.load({'odb': '/work/seed.odb', 'metrics': {}}))
        step.start(step_dir='/work/replay/step')
    finally:
        TclStep.run_subprocess = delegate
        package_unchanged(package, packet['native_package_sha256'])
        require(sha('/work/seed.odb') == SEED_SHA and P.inventory(inputs) == packet['input_sha256'],
            'Native replay input changed during execution')


def native():
    root = Path('/work/replay'); start = time.monotonic()
    command = [sys.executable, '-B', '/work/replay/inputs/producer/' + OWN, 'native-step']
    row = dict(schema='pinwheel.streaming-8x4-route-replay-native.v1', argv=command,
        timeout_seconds=1770, exit_code=None, process_tree_reaped=False, policy=policy())
    try:
        result = process_group.run_captured(command, cwd=root, timeout=1770, log_path=root / 'native.log')
        row.update(exit_code=result.returncode, process_tree_reaped=True)
    except BaseException as error:
        row.update(error=type(error).__name__ + ': ' + str(error),
            exit_code=124 if isinstance(error, subprocess.TimeoutExpired) else 2,
            process_tree_reaped=getattr(error, 'process_group_stopped', False))
    row['work_wall_seconds'] = time.monotonic() - start
    row['work_budget_satisfied'] = row['work_wall_seconds'] <= 1800
    P.write(root / 'native.json', row)
    return 0 if row['exit_code'] == 0 and row['process_tree_reaped'] and row['work_budget_satisfied'] else 2


def validate_runtime(runtime, expected):
    lock = P.read(P.ROOT / 'tools/physical-toolchain.json')
    require(runtime == expected == dict(image_id=expected['image_id'], architecture='arm64', os='linux',
        rootfs_diff_ids=lock['container_rootfs_diff_ids'], runtime_config_sha256=lock['container_runtime_config_sha256']),
        'Replay selected runtime identity changed')


def container_command(output, packet, runtime, owner, name):
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+', name) and str(uuid.UUID(owner)) == owner, 'Unsafe replay owner/name')
    validate_runtime(runtime, packet['runtime']); base = P.read(packet['original_preparation']['path'])
    return ['docker', 'run', '--rm', '--pull', 'never', '--name', name, '--label',
        'org.pinwheel.streaming8_owner=' + owner, '--network', 'none', '--cpus', '4', '--memory', '6g',
        '--memory-swap', '6g', '--pids-limit', '256', '--read-only', '--tmpfs', '/tmp:rw,size=512m',
        '--env', 'PYTHONDONTWRITEBYTECODE=1', '--env', 'PYTHONPATH=/work/replay/inputs/producer/scripts',
        '--mount', f'type=bind,source={output},target=/work/replay',
        '--mount', f'type=bind,source={output / "inputs"},target=/work/replay/inputs,readonly',
        '--mount', f'type=bind,source={packet["source_odb"]["path"]},target=/work/seed.odb,readonly',
        '--mount', f'type=bind,source={base["pdk_root"]},target=/work/pdk,readonly',
        '--mount', f'type=bind,source={Path(packet["original_preparation"]["path"]).parent / "inputs"},target=/work/inputs,readonly',
        '--workdir', '/work/replay', runtime['image_id'], 'python3', '-B',
        '/work/replay/inputs/producer/' + OWN, 'native']


def run(output, name):
    output = Path(output).absolute(); packet = verify(output)
    require({p.name for p in output.iterdir()} == {'inputs', 'preparation.json'}, 'Replay output is not fresh')
    runtime = inspect_runtime(P.read(P.ROOT / 'tools/physical-toolchain.json')); owner = str(uuid.uuid4())
    command = container_command(output, packet, runtime, owner, name)
    execution = V.owned_native(command, output, owner, 1800)
    report = dict(schema='pinwheel.streaming-8x4-route-replay-run.v1', preparation=bound(output / 'preparation.json'),
        runtime=runtime, execution=execution, policy=policy(), same_candidate_parent=packet['parent_report'],
        physical_acceptance=False, eligible_final_target=False, completed_DetailedRouting=False,
        reproduction_gate_passed=False, bounded_route_returned=False, diagnostic_completed=False,
        inputs_runtime_unchanged=False)
    try:
        require(verify(output) == packet and inspect_runtime(P.read(P.ROOT / 'tools/physical-toolchain.json')) == runtime,
            'Replay input/PDK/runtime changed')
        report['inputs_runtime_unchanged'] = True
        measured = measurements(output)
        report.update(measured)
        report['diagnostic_completed'] = diagnostic_completed(measured, execution)
    except BaseException as error: report['readback_error'] = type(error).__name__ + ': ' + str(error)
    report['artifact_sha256'] = {k: v for k, v in P.inventory(output).items() if k != 'report.json'}
    P.write(output / 'report.json', report); return report


def reproduction(text):
    values = {}
    for line in text.splitlines():
        name, value = line.split('\t'); require(name not in values and value.isdigit(), 'Invalid reproduction record')
        values[name] = int(value)
    require(set(values) == set(EXPECTED) | {'before_instances', 'after_instances'} and
        all(values[k] == v for k, v in EXPECTED.items()) and
        values['after_instances'] - values['before_instances'] == 39, 'Historical antenna counts did not reproduce')
    return values


def census(text):
    insts = {}; terms = {}; nets = {}; bterms = {}; top = []
    for line in text.splitlines():
        row = line.split('\t'); kind = row[0]
        if kind == 'TOP':
            require(len(row) == 2, 'Invalid top row'); top.append(row[1])
        elif kind == 'INST':
            require(len(row) == 7 and row[1] not in insts, 'Invalid/duplicate instance census')
            require(all(re.fullmatch(r'-?[0-9]+', x) for x in row[3:5]), 'Invalid instance coordinates')
            insts[row[1]] = row[2:]
        elif kind == 'ITERM':
            require(len(row) == 6 and tuple(row[1:3]) not in terms, 'Invalid/duplicate ITerm census')
            terms[tuple(row[1:3])] = row[3:]
        elif kind == 'NET':
            require(len(row) == 5 and row[1] not in nets and all(x.isdigit() for x in row[3:]), 'Invalid/duplicate net census')
            nets[row[1]] = [row[2], int(row[3]), int(row[4])]
        elif kind == 'BTERM':
            require(len(row) == 5 and row[1] not in bterms, 'Invalid/duplicate BTerm census')
            bterms[row[1]] = row[2:]
        else: raise ValueError('Unknown census row type')
    require(top == [TOP] and insts and terms and nets and bterms, 'Vacuous/wrong-top census')
    iterm_counts = {name: 0 for name in nets}; bterm_counts = dict(iterm_counts)
    def compatible(term_type, net_type):
        return term_type == net_type if term_type in ('POWER', 'GROUND') or net_type in ('POWER', 'GROUND') else True
    for (instance, pin), (direction, kind, net) in terms.items():
        require(instance in insts and pin and direction in ('INPUT', 'OUTPUT', 'INOUT'), 'Unresolved ITerm owner/direction')
        if net:
            require(net in nets and compatible(kind, nets[net][0]), 'Wrong ITerm net/type'); iterm_counts[net] += 1
    for name, (direction, kind, net) in bterms.items():
        require(net in nets and compatible(kind, nets[net][0]), 'Unresolved BTerm net/type'); bterm_counts[net] += 1
    require(all([iterm_counts[name], bterm_counts[name]] == values[1:] for name, values in nets.items()),
        'Census complete net endpoint counts differ')
    return dict(instances=insts, terminals=terms, nets=nets, bterms=bterms)


def fanout_delta(before_text, after_text):
    before, after = census(before_text), census(after_text)
    require(set(before['instances']) <= set(after['instances']) and before['bterms'] == after['bterms'] and
        set(before['nets']) == set(after['nets']) and
        all(after['terminals'].get(key) == value for key, value in before['terminals'].items()) and
        all(after['instances'][name][0] == value[0] for name, value in before['instances'].items()),
        'Canonical diode replay changed preexisting masters/connectivity')
    added = sorted(set(after['instances']) - set(before['instances']))
    require(len(added) == 39 and all(after['instances'][name][0] == 'sg13cmos5l_antennanp' for name in added),
        'New instance membership is not exactly 39 canonical diodes')
    touched = set()
    for name in added:
        signal = [(pin, row) for (inst, pin), row in after['terminals'].items()
            if inst == name and row[1] not in ('POWER', 'GROUND')]
        require(len(signal) == 1 and signal[0][1][0] == 'INPUT' and signal[0][1][2] in after['nets'],
            'Diode signal terminal disconnected/unsupported')
        touched.add(signal[0][1][2])
    rows = []
    for net in sorted(touched):
        drivers = [[inst, pin] for (inst, pin), row in after['terminals'].items() if row[2] == net and row[0] == 'OUTPUT']
        rows.append(dict(net=net, drivers=sorted(drivers), before_endpoints=sum(before['nets'][net][1:]),
            after_endpoints=sum(after['nets'][net][1:]),
            before_loads_per_single_driver=sum(before['nets'][net][1:])-1 if len(drivers) == 1 else None,
            after_loads_per_single_driver=sum(after['nets'][net][1:])-1 if len(drivers) == 1 else None))
    return dict(added_diodes=added, touched_nets=rows, complete_before_instances=len(before['instances']),
        complete_after_instances=len(after['instances']), preexisting_connectivity_unchanged=True,
        fanout_scope='Exact terminal endpoint count; no STA/electrical or fanout-limit acceptance')


def measurements(output):
    output = Path(output); step = output / 'step'; native = P.read(output / 'native.json')
    require(native['schema'] == 'pinwheel.streaming-8x4-route-replay-native.v1' and native['policy'] == policy() and
        native['timeout_seconds'] == 1770 and type(native['work_wall_seconds']) in (int, float) and
        math.isfinite(native['work_wall_seconds']) and native['work_wall_seconds'] >= 0 and
        native['work_budget_satisfied'] is (native['work_wall_seconds'] <= 1800), 'Replay native work policy differs')
    result = dict(reproduction_gate_passed=False, bounded_route_returned=False)
    if (step / 'reproduction.tsv').exists():
        result['reproduction'] = reproduction((step / 'reproduction.tsv').read_text())
        require(all((step / ('postdiode.' + ext)).is_file() for ext in ('odb', 'def', 'v', 'tsv', 'guide')),
            'Reproduction gate without complete pre-route snapshot')
        result['fanout_delta'] = fanout_delta((step / 'before.tsv').read_text(), (step / 'postdiode.tsv').read_text())
        result['reproduction_gate_passed'] = True
    raw = (output / 'native.log').read_text()
    versions = re.findall(r'^PINWHEEL_REPLAY_OPENROAD (.*)$', raw, re.M)
    require(versions == [COMMIT], 'Actual replay OpenROAD revision differs')
    version_identity({name: regular(step / (name + '.txt')).read_text() for name in
        ('describe-return', 'describe-printed', 'version-return', 'version-printed')})
    returned = 'PINWHEEL_REPLAY_BOUNDED_ROUTE_RETURNED' in raw
    if returned:
        require(result['reproduction_gate_passed'] and native['exit_code'] == 0 and native['process_tree_reaped'] is True and
            native['work_budget_satisfied'] is True and all((step / ('postroute.' + ext)).is_file()
            for ext in ('odb', 'def', 'v', 'tsv', 'guide')) and (step / 'bounded.drc').is_file(),
            'Bounded route completion lacks actual closed views/DRC')
        result['bounded_route_returned'] = True
        journal(output)
    return result


def version_identity(observations):
    require(set(observations) == {'describe-return', 'describe-printed', 'version-return', 'version-printed'} and
        all(type(v) is str for v in observations.values()), 'Incomplete version observations')
    hashes = {token for token in re.findall(r'[0-9a-f]+', ' '.join(observations.values())) if len(token) >= 40}
    require(hashes == {COMMIT}, 'Empty/wrong/conflicting actual OpenROAD revision')
    return COMMIT


def diagnostic_completed(measured, execution):
    return bool(measured['bounded_route_returned'] and execution.get('status') == 'completed' and
        type(execution.get('exit_code')) is int and execution['exit_code'] == 0 and
        execution.get('container_termination', {}).get('status') == 'absent')


def journal(output):
    rows = [json.loads(line) for line in regular(Path(output) / 'native-journal.jsonl').read_text().splitlines()]
    require(len(rows) == 2 and rows[0]['event'] == 'start' and rows[1] == dict(event='finish', exit_code=0),
        'Replay actual canonical direct call did not close exactly once')
    row = rows[0]; argv = row['argv']; env = row['env']
    require(row['step'] == 'Pinwheel.RouteReplayDiagnostic' and len(argv) == 8 and
        Path(argv[0]).name == 'openroad' and Path(argv[0]).is_absolute() and argv[1:] ==
        ['-exit', '-threads', '4', '-no_splash', '-metrics', '/work/replay/step/or_metrics_out.json',
        '/work/replay/inputs/replay.tcl'] and re.fullmatch(r'[0-9a-f]{64}', row['executable_sha256']),
        'Replay actual canonical OpenROAD argv differs')
    expected = dict(CURRENT_ODB='/work/seed.odb', PNR_SDC_FILE='/work/inputs/core.sdc',
        _SDC_IN='/work/inputs/core.sdc', OPENROAD_THREADS='4', RT_MIN_LAYER='Metal2', RT_MAX_LAYER='Metal4',
        DRT_OPT_ITERS='64', GRT_ANTENNA_REPAIR_MARGIN='10', DIODE_CELL='sg13cmos5l_antennanp')
    require(all(env.get(k) == v for k, v in expected.items()), 'Replay actual canonical input/env differs')
    config = P.read(Path(output) / 'inputs/config.json'); corner = config['DEFAULT_CORNER']
    require(env.get('_LIB_CORNER_0', '').split() == [corner] + config['CELL_LIBS'][corner] and
        '_LIB_CORNER_1' not in env, 'Replay actual default-cell-corner membership differs')
    return rows


def reopen(output):
    output = Path(output).resolve(); packet = verify(output); report = P.read(output / 'report.json')
    require(report['schema'] == 'pinwheel.streaming-8x4-route-replay-run.v1' and report['policy'] == policy() and
        report['preparation'] == bound(output / 'preparation.json') and report['same_candidate_parent'] == packet['parent_report'] and
        report['physical_acceptance'] is False and report['eligible_final_target'] is False and
        report['completed_DetailedRouting'] is False and report['inputs_runtime_unchanged'] is True and
        P.inventory(output) == dict(report['artifact_sha256'], **{'report.json': sha(output / 'report.json')}),
        'Replay closed artifact/claim inventory differs')
    execution = P.read(output / 'execution.json')
    require(execution == report['execution'] and execution['timeout_seconds'] == 1800 and
        execution['container_termination']['status'] == 'absent' and
        execution['argv'] == container_command(output, packet, report['runtime'], execution['owner'],
            execution['argv'][execution['argv'].index('--name') + 1]), 'Replay actual runtime/argv/cleanup differs')
    measured = measurements(output)
    require(all(report.get(k) == v for k, v in measured.items()), 'Replay measurements differ from retained raw evidence')
    require(report['diagnostic_completed'] is diagnostic_completed(measured, execution),
        'Replay diagnostic success differs from owned controller closure')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__); sub = parser.add_subparsers(dest='mode', required=True)
    prep = sub.add_parser('prepare')
    for name in ('parent-report', 'parent-resource', 'source-root', 'output'): prep.add_argument('--' + name, type=Path, required=True)
    for mode in ('verify', 'reopen'):
        p = sub.add_parser(mode); p.add_argument('--output', type=Path, required=True)
    launch = sub.add_parser('run'); launch.add_argument('--output', type=Path, required=True); launch.add_argument('--name', required=True)
    sub.add_parser('native'); sub.add_parser('native-step'); args = parser.parse_args()
    if args.mode == 'prepare': prepare(args.parent_report, args.parent_resource, args.source_root, args.output); return 0
    if args.mode == 'verify': verify(args.output); return 0
    if args.mode == 'native': return native()
    if args.mode == 'native-step': native_step(); return 0
    if args.mode == 'reopen': result = reopen(args.output)
    else: result = run(args.output, args.name)
    print(json.dumps({k: result[k] for k in ('reproduction_gate_passed', 'bounded_route_returned', 'diagnostic_completed', 'eligible_final_target')}, indent=2))
    return 0 if result['diagnostic_completed'] else 2


if __name__ == '__main__': raise SystemExit(main())
