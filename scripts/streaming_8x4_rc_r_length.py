"""Fresh fixed26-net R length/width diagnostic; Root alone admits Native.

Baseline and local -lef_res candidate are new policies. Original absolute
failures, process tables and all frozen producers remain unchanged.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer_semantic as OLD
import streaming_8x4_rc_consumer_semantic_closeout as AUTH
import streaming_8x4_rc_r_length_geometry as G
import streaming_8x4_rc_r_length_math as M

C, P, N, need = OLD.C, OLD.P, OLD.N, OLD.need
BASELINE = 'b38f0ff0b3ace618a2cd854aaf06b4b18b9eec771de9e7ea7db9e01257e7f65e'
RAW = 'abce0d09344562621fd6df1b4e10b25d4c62af7a2cc478c40fe66ce87fe4d2d3'
RESOURCE = '05cedf7ae89887f0268a51a5e61a6b499c1f16c00e8c585038dc3e5ea7ec2807'
PROCESS = '2f9121203214d9ad6afa287e53fd51a6ca34405405971b3fdac531a5e211fd2d'
NEW = ('streaming_8x4_rc_r_length.py', 'streaming_8x4_rc_r_length_geometry.py',
       'streaming_8x4_rc_r_length_math.py', 'streaming_8x4_rc_r_length_readback.py',
       'streaming_8x4_rc_consumer_semantic_closeout.py', 'streaming_8x4_rc_consumer_ndr_closeout.py')
OUTPUT = 'rc-r-length-width-01'
ROOT = Path(__file__).resolve().parents[1]


def write(path, value): N.write(path, value)


def protocol():
    return dict(schema='pinwheel.streaming-8x4-rc-R-length-width-protocol.v1',
        jobs=[dict(corner=c, policy=p) for c, p in M.JOBS], nets=26, ports=52, segments=31, named_vias=5,
        lengths_um=['50', '100', '150'], policies=list(M.POLICIES), extractor_version='1.0',
        only_candidate_deltas=['-lef_res', 'five local routing LEF RPSQ values from exact selected ITF'],
        original_absolute_relative_tolerance='0.001', original_via_absolute_tolerance_ohm='0.001',
        slope_relative_tolerance='0.001', mutual_slope_relative_tolerance='0.001',
        heldout='I150 intersects 2*I100-I50; six-significant-digit raw resistor rounding only',
        cpus=1, memory_bytes=2147483648, no_extra_swap=True, pids=128, scratch_bytes=134217728,
        seconds_per_leaf=30, work_seconds=210, outer_seconds=300, root_go_required=True,
        shared_PDK_modified=False, original_17net_experiment_passed=False, model_qualified=False,
        capacitance_qualified=False, full_width_range_qualified=False)


def producers(old):
    result = dict(old['producer_sha256']); result.update({n: P.sha(Path(__file__).with_name(n)) for n in NEW})
    return dict(sorted(result.items()))


def original_result(base):
    need(P.sha(base / 'original-result/raw.json') == RAW and P.sha(base / 'original-result/resource.json') == RESOURCE,
        'Original six-call failed numerical/raw custody authority differs')
    raw = json.loads((base / 'original-result/raw.json').read_text())
    jobs = raw['raw_consumer_readback']['jobs']
    need(raw['all_six_native_calls_closed'] is True and raw['workflow_passed'] is False
        and len(jobs) == 6 and sum(w['passed'] is False for j in jobs for w in j['analysis']['wires']) == 72
        and sum(v['passed'] is True for j in jobs for v in j['analysis']['vias']) == 30,
        'Original72 wire failures/30 via passes must remain unchanged')


def data(base):
    old = OLD.verify(base / 'baseline-semantic', BASELINE)
    reference = C.verify_plan(base / 'baseline-semantic/consumer-inputs', old['consumer_plan_sha256'])
    need(P.sha(base / 'process-intake/manifest.json') == PROCESS == reference['process_intake_manifest_sha256'],
        'Exact pinned process/ITF intake differs')
    texts, _ = P.verify_intake(base / 'process-intake'); corners = {}
    for corner in ('MIN', 'TYP', 'MAX'):
        itf = P.parse_stack(texts['itf_' + corner.lower()])
        sheets = {n: str(itf['CONDUCTOR', n]['RPSQ']) for n in N.METALS}
        need(sheets == reference['corners'][corner]['wire_sheet_R'], 'Actual ITF and original corner targets differ')
        corners[corner] = reference['corners'][corner]
    return old, reference, corners


def expected_inputs(base):
    old, ref, corners = data(base); source = base / 'baseline-semantic/consumer-inputs'
    tech = (source / 'tech.lef').read_text(); widths = (source / 'widths.lef').read_text()
    fixture, ndr = G.fixture(tech, widths); files = {'fixture.def': fixture.encode(), 'widths.lef': widths.encode(), 'tech.lef': tech.encode()}
    witnesses = {}
    for corner in ('MIN', 'TYP', 'MAX'):
        local, witness = G.local_lef(tech, corners[corner]['wire_sheet_R']); witnesses[corner] = witness
        files[corner + '-local.lef'] = local.encode()
        files[corner + '-rules.txt'] = (source / (corner + '-retained_rules.txt')).read_bytes()
    files['baseline_rules.tcl'] = C.tcl().encode()
    need(C.tcl().count('extract_parasitics ') == 1 and '-lef_res' not in C.tcl(), 'Frozen extraction Tcl changed')
    files['width_aware_LEF.tcl'] = C.tcl().replace('extract_parasitics ', 'extract_parasitics -lef_res ', 1).encode()
    return files, witnesses, ndr, corners, ref


def prepare(baseline, process_intake, original_raw, original_resource, output):
    OLD.verify(baseline, BASELINE); need(not output.exists() and output.parent.is_dir(), 'Fresh R-study preparation required')
    output.mkdir(); shutil.copytree(baseline, output / 'baseline-semantic'); shutil.copytree(process_intake, output / 'process-intake')
    (output / 'original-result').mkdir(); shutil.copyfile(original_raw, output / 'original-result/raw.json')
    shutil.copyfile(original_resource, output / 'original-result/resource.json'); original_result(output)
    files, witnesses, ndr, corners, ref = expected_inputs(output)
    for name, raw in files.items(): (output / name).write_bytes(raw)
    old = OLD.verify(output / 'baseline-semantic', BASELINE)
    plan = dict(schema='pinwheel.streaming-8x4-rc-R-length-width-plan.v1', qualified=False, model_qualified=False,
        native_executed=False, root_go_required=True, baseline_semantic_plan_sha256=BASELINE,
        protocol=protocol(), fixture_rows=G.rows(), corners=corners, LEF_inventory=ref['LEF_inventory'],
        local_LEF_witnesses=witnesses, NDR_witness=ndr, producer_sha256=producers(old),
        generated_files_sha256={n: C.digest(v) for n, v in files.items()}, files_sha256=N.file_inventory(output),
        original_absolute_audit_remains_failed=True)
    write(output / 'plan.json', plan); verify(output, P.sha(output / 'plan.json'))
    return dict(plan_sha256=P.sha(output / 'plan.json'), native_executed=False, model_qualified=False)


def verify(base, digest):
    need(P.sha(base / 'plan.json') == digest, 'R-study plan identity differs')
    row = json.loads((base / 'plan.json').read_text()); old = OLD.verify(base / 'baseline-semantic', BASELINE)
    files, witnesses, ndr, corners, ref = expected_inputs(base); actual = N.file_inventory(base); actual.pop('plan.json')
    need(row['schema'] == 'pinwheel.streaming-8x4-rc-R-length-width-plan.v1'
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'native_executed'))
        and row['root_go_required'] is True and row['baseline_semantic_plan_sha256'] == BASELINE
        and row['protocol'] == protocol() and row['fixture_rows'] == G.rows() and row['corners'] == corners
        and row['LEF_inventory'] == ref['LEF_inventory'] and row['local_LEF_witnesses'] == witnesses and row['NDR_witness'] == ndr
        and row['producer_sha256'] == producers(old) and row['files_sha256'] == actual
        and row['generated_files_sha256'] == {n: C.digest(v) for n, v in files.items()}
        and all((base / n).read_bytes() == v for n, v in files.items())
        and row['original_absolute_audit_remains_failed'] is True, 'R-study exact scope/source/input/ITF/old failure differs')
    original_result(base); return row


def math_plan(plan):
    return {k: plan[k] for k in ('fixture_rows', 'corners', 'LEF_inventory')}


def cgroups():
    root = Path('/sys/fs/cgroup'); row = {n: (root / n).read_text().strip() for n in ('memory.max', 'memory.swap.max', 'cpu.max', 'pids.max')}
    cpu = row['cpu.max'].split()
    need(row['memory.max'].isdigit() and 0 < int(row['memory.max']) <= 2147483648 and row['memory.swap.max'] == '0'
        and len(cpu) == 2 and all(x.isdigit() for x in cpu) and 0 < int(cpu[0]) <= int(cpu[1])
        and row['pids.max'].isdigit() and 0 < int(row['pids.max']) <= 128, 'R-study cgroup resources differ')
    return row


def copies(plan, corner, policy):
    need((corner, policy) in M.JOBS, 'Undeclared R-study job')
    return dict(tech=corner + '-local.lef' if policy == 'width_aware_LEF' else 'tech.lef',
        tcl=policy + '.tcl', rules=corner + '-rules.txt')


def parse_leaf(base, plan, owner, corner, policy):
    text = (owner / 'native.log').read_text()
    need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b', text) and text.count('PINWHEEL_CONSUMER_TERMINAL') == 1,
        'R-study Native warning/error/terminal gap')
    selected = copies(plan, corner, policy)
    for name, source in [('fixture.def', 'fixture.def'), ('widths.lef', 'widths.lef'), ('tech.lef', selected['tech']),
        ('rules.txt', selected['rules']), ('run.tcl', selected['tcl'])]:
        need(P.sha(owner / name) == plan['generated_files_sha256'][source], 'Actual R-study selected input bytes differ')
    geometry = G.compare((owner / 'before.def').read_text(), (owner / 'after.def').read_text(),
        (owner / 'tech.lef').read_text(), plan['NDR_witness'], plan['fixture_rows'])
    spef = (owner / 'result.spef').read_text(); values = C.parse_spef(spef, {r['name'] for r in G.rows()})
    absolute = C.analyze_values(math_plan(plan), corner, 'retained_rules', values)
    return dict(geometry=geometry, values=values, absolute_audit=absolute, rounding_intervals=M.intervals(spef, values))


def run(base, digest, output):
    plan = verify(base, digest); cg = cgroups(); need(not output.exists() and output.parent.is_dir(), 'Fresh R-study execution owner required')
    output.mkdir(); started = time.monotonic(); jobs = []
    report = dict(schema='pinwheel.streaming-8x4-rc-R-length-width-execution.v1', plan_sha256=digest,
        qualified=False, model_qualified=False, capacitance_qualified=False, original_17net_experiment_passed=False,
        passed=False, measurement_packet_completed=False, original_absolute_audits_retained=True, jobs=jobs, cgroups=cg)
    try:
        for corner, policy in M.JOBS:
            need(time.monotonic() - started < 175, 'Insufficient210s R-study work allowance')
            owner = output / (corner + '-' + policy); owner.mkdir(); selected = copies(plan, corner, policy)
            for target, source in [('fixture.def', 'fixture.def'), ('widths.lef', 'widths.lef'), ('tech.lef', selected['tech']),
                ('run.tcl', selected['tcl']), ('rules.txt', selected['rules'])]: shutil.copyfile(base / source, owner / target)
            copied = {p.name: P.sha(p) for p in owner.iterdir()}; command = ['openroad', '-no_init', '-exit', 'run.tcl']
            with (owner / 'native.log').open('xb') as stream:
                child = subprocess.Popen(command, cwd=owner, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                try: code = child.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL); child.wait(); raise ValueError('R-study OpenROAD timeout')
            need(type(code) is int and code == 0, 'R-study OpenROAD exit failure')
            try: os.killpg(child.pid, 0)
            except ProcessLookupError: pass
            else: os.killpg(child.pid, signal.SIGKILL); raise ValueError('R-study child group remains live')
            need(all(P.sha(owner / n) == h for n, h in copied.items()), 'R-study copied input changed')
            parsed = parse_leaf(base, plan, owner, corner, policy)
            write(owner / 'physical.json', parsed['geometry'])
            jobs.append(dict(corner=corner, policy=policy, argv=command, exit_code=code,
                process_tree_reaped=True, copied_inputs_unchanged=True, copied_input_sha256=copied,
                output_sha256={n: P.sha(owner / n) for n in ('native.log', 'before.def', 'after.def', 'result.spef', 'physical.json')},
                values=parsed['values'], absolute_audit=parsed['absolute_audit'], rounding_intervals=parsed['rounding_intervals']))
        report['analysis'] = M.measurements(plan, jobs)
        report['measurement_packet_completed'] = len(jobs) == 6
        report['passed'] = report['analysis']['length_width_diagnostic_controls_passed']
    except BaseException as error: report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        report['inputs_unchanged'] = verify(base, digest) == plan; report['passed'] &= report['inputs_unchanged']
        report['wall_seconds'] = time.monotonic() - started; write(output / 'report.json', report)
    return report


def proposal(base, digest, old_proposal, require_fresh=True):
    plan = verify(base, digest); previous = AUTH.checked_proposal(old_proposal)
    need(previous['plan_sha256'] == BASELINE, 'Original semantic command authority differs')
    command = list(previous['argv']); replacements = {previous['container_name']: 'pinwheel-8x4-' + OUTPUT,
        'type=bind,src=' + str(Path(previous['plan_path']).parent) + ',dst=/rc-inputs,readonly': 'type=bind,src=' + str(base.resolve()) + ',dst=/rc-inputs,readonly',
        '/rc-source/streaming_8x4_rc_consumer_semantic.py': '/rc-source/streaming_8x4_rc_r_length.py',
        BASELINE: digest, '/rc-output-parent/rc-consumer-semantic-01': '/rc-output-parent/' + OUTPUT}
    for before, after in replacements.items(): need(command.count(before) == 1, 'Exact R-study command identity adaptation differs'); command[command.index(before)] = after
    parent = next(x.split('src=', 1)[1].split(',dst=', 1)[0] for x in command if 'dst=/rc-output-parent' in x)
    need(Path(parent).resolve() == ROOT / 'build/campaigns/8x4-20261022-01/rc-native-outputs', 'Original output owner differs')
    if require_fresh: need(not (Path(parent) / OUTPUT).exists(), 'R-study output must be fresh')
    return dict(schema='pinwheel.streaming-8x4-rc-R-length-width-command-proposal.v1', root_go_required=True,
        admitted=False, native_executed=False, model_qualified=False, plan_path=str((base / 'plan.json').resolve()),
        plan_sha256=digest, parent_semantic_proposal=dict(path=str(old_proposal.resolve()), sha256=P.sha(old_proposal)),
        producer_sha256=plan['producer_sha256'], protocol=protocol(), timeout_seconds=300,
        container_name='pinwheel-8x4-' + OUTPUT, output_directory=str(Path(parent) / OUTPUT), argv=command)


def launch_reopen(proposal_path, record):
    tag = '8x4-' + OUTPUT; campaign = ROOT / 'build/campaigns/8x4-20261022-01'
    resource = ROOT / 'build/streaming-tt-resources' / tag / 'report.json'
    python = '/opt/homebrew/opt/python@3.13/bin/python3.13'
    argv = [python, '-B', str(ROOT / 'scripts/streaming_8x4_acceptance_resources.py'), '--campaign-root', str(ROOT),
        '--kind', 'solver', '--tag', tag, '--timeout-seconds', '300', '--rss-mib', '4096',
        '--container-name', record['container_name'], '--input', str(proposal_path.resolve()),
        '--input', record['plan_path'], '--input', record['parent_semantic_proposal']['path']]
    for name in record['producer_sha256']: argv += ['--input', str(ROOT / 'scripts' / name)]
    argv += ['--', *record['argv']]
    return dict(schema='pinwheel.streaming-8x4-rc-R-length-width-launch-reopen-proposal.v1', root_go_required=True,
        native_executed=False, resource_supervisor_argv=argv, required_resource_report=str(resource),
        HOST_closeout_argv=[python, '-B', str(ROOT / 'scripts/streaming_8x4_rc_r_length_readback.py'),
            '--inputs', str(Path(record['plan_path']).parent), '--plan-sha256', record['plan_sha256'],
            '--directory', record['output_directory'], '--resource-report', str(resource),
            '--command-proposal', str(proposal_path.resolve()), '--output', str(campaign / 'rc-r-length-width-closeout-01.json')],
        HOST_only_after_actual_terminal_and_Root_signal=True, model_qualified=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__); sub = parser.add_subparsers(dest='mode', required=True)
    p = sub.add_parser('prepare')
    for n in ('baseline', 'process-intake', 'original-raw', 'original-resource', 'output'): p.add_argument('--' + n, type=Path, required=True)
    for mode in ('verify', 'run', 'proposal'):
        p = sub.add_parser(mode); p.add_argument('--inputs', type=Path, required=True); p.add_argument('--plan-sha256', required=True)
        if mode != 'verify': p.add_argument('--output', type=Path, required=True)
        if mode == 'proposal':
            p.add_argument('--old-proposal', type=Path, required=True); p.add_argument('--launch-reopen', type=Path, required=True)
    a = parser.parse_args()
    if a.mode == 'prepare': result = prepare(a.baseline, a.process_intake, a.original_raw, a.original_resource, a.output)
    elif a.mode == 'verify': result = dict(verified=bool(verify(a.inputs, a.plan_sha256)), native_executed=False)
    elif a.mode == 'proposal':
        result = proposal(a.inputs, a.plan_sha256, a.old_proposal); write(a.output, result)
        write(a.launch_reopen, launch_reopen(a.output, result))
    else: result = run(a.inputs, a.plan_sha256, a.output)
    print(json.dumps(result, indent=2)); return 2 if a.mode == 'run' and not result['passed'] else 0


if __name__ == '__main__': raise SystemExit(main())
