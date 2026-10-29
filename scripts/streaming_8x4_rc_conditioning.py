"""New fixed conditioning experiments; Root alone admits Native execution.

The layered two-call control and uniform five-mesh development continuation
have separate typed identities. No old plan, producer or failed result changes.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_execute as E
import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_solver_diagnostic as D
import streaming_8x4_rc_conditioning_parser as Q

NEW_SOURCES = ('streaming_8x4_rc_conditioning.py', 'streaming_8x4_rc_conditioning_parser.py',
               'streaming_8x4_rc_conditioning_readback.py')
BASELINES = {
    Q.PROFILES[0]: {'hash': '6ea3613a03b2c29b8706da76d02e5a4f67ae2f5dc6ff55ddfe5cc1e27b418cc4',
        'case': 'TYP-w.16-s.18-L10-E20', 'output': 'rc-m1-conditioning-01',
        'observed_report': 'ab8b62c37034a8a558f854c8c68d81f67e6bf3eb38010a2301a10448d17786c8',
        'observed_log': '309029efcab2f40f78b35ca2b81ebba7a423b9efdf37ba062ac99e76b895765b'},
    Q.PROFILES[1]: {'hash': D.BASELINE_HASH, 'case': 'wire_w0p16_L20_M30',
        'output': 'rc-uniform-d025-five-mesh-01',
        'observed_report': '354634741bbc75a4d6bcf49391a7e033d246621f87cf1039549d1e099ed7cbee'}}
ENVIRONMENT = dict(D.ENVIRONMENT)


def policy(profile):
    P.need(profile in Q.PROFILES, 'Undeclared conditioning profile')
    count = len(Q.branches(profile)); work = 270 if count == 2 else 660
    return {'schema': 'pinwheel.streaming-8x4-rc-conditioning-policy.v1', 'profile': profile,
        'case': BASELINES[profile]['case'], 'branches': Q.branches(profile), 'maximum_calls': count,
        'gmres_tolerance': '0.0005', 'scheme': 'Galerkin', 'seconds_per_leaf': 120,
        'work_seconds': work, 'outer_seconds': work + 60, 'cpus': 1,
        'memory_bytes': 6442450944, 'scratch_bytes': 536870912, 'pids': 128,
        'no_extra_swap': True, 'all_warnings_fatal': True,
        'maximum_numeric_matrix_asymmetry_relative': '0.01',
        'maximum_cellwise_mesh_change': '0.02', 'consecutive_mesh_pairs_required': 2,
        'numeric_failure_policy': 'retain every failure and continue fixed branches only after reaping and custody close',
        'automatic_retry_or_parameter_selection': False, 'root_go_required': True,
        'model_qualified': False, 'full_pilot_passed': False, 'continuum_error_enclosure': False,
        'scope': 'same-geometry conditioning diagnostic only' if count == 2 else 'one development geometry five-mesh diagnostic only'}


def write(path, data):
    P.need(not path.exists() and path.parent.is_dir(), 'Preserve existing conditioning artifact')
    E.write(path, data)


def inventory(owner):
    return {n: r for n, r in E.tree(owner).items() if n != 'plan.json'}


def observation_rows(profile, baseline, observed):
    """Bind original failures/mesh jump to exact immutable primary observations."""
    fixed = BASELINES[profile]
    P.need(E.sha(observed / 'report.json') == fixed['observed_report'], 'Wrong original observation receipt')
    top = json.loads((observed / 'report.json').read_text())
    if profile == Q.PROFILES[0]:
        P.need(E.sha(observed / 'native.log') == fixed['observed_log'], 'Wrong original failed M1 log')
        rows = [(observed, Q.MESHES[0])]
    else:
        selected = [r for r in top['actual_jobs'] if r['case'] == fixed['case']]
        P.need([r['mesh'] for r in selected] == Q.MESHES, 'Wrong original five-mesh observation membership')
        rows = []
        for row in selected:
            name = Path(row['directory']).name
            P.need(name.startswith('job-') and name[4:].isdigit(), 'Unsafe observation owner')
            owner = observed / name
            P.need(E.sha(owner / 'report.json') == row['report_sha256'], 'Original selected leaf seal differs')
            rows.append((owner, row['mesh']))
    result = []
    for owner, mesh in rows:
        row = json.loads((owner / 'report.json').read_text()); raw = (owner / 'native.log').read_text()
        P.need(row['plan_sha256'] == fixed['hash'] and row['case'] == fixed['case'] and row['mesh'] == mesh
            and row['argv'] == ['/solver/runtime/bin/FasterCap', '-b', 'geometry.lst', '-g', '-m' + mesh, '-t0.0005', '-d1']
            and row['exit_code'] == 0 and row['timed_out'] is False
            and all(row[k] is True for k in ('solver_executed', 'process_tree_reaped', 'source_runtime_unchanged', 'copied_inputs_unchanged'))
            and (profile != Q.PROFILES[0] or row['producer_plan_unchanged'] is True)
            and E.sha(owner / 'native.log') == row['log_sha256'], 'Original observation exit/custody/arguments differ')
        result.append({'owner': owner, 'mesh': mesh, 'report': row, 'raw': raw})
    return result


def check_baseline_observations(profile, owner, case):
    records = []
    original = json.loads((owner / 'original-report.json').read_text())
    selected = None
    if profile == Q.PROFILES[1]:
        selected = [r for r in original['actual_jobs'] if r['case'] == case['name']]
        P.need([r['mesh'] for r in selected] == Q.MESHES, 'Retained original five-mesh membership differs')
    for index, mesh in enumerate(Q.MESHES[:1] if profile == Q.PROFILES[0] else Q.MESHES):
        leaf = owner / ('observation-' + str(index))
        row = json.loads((leaf / 'report.json').read_text()); raw = (leaf / 'native.log').read_text()
        P.need(row['plan_sha256'] == BASELINES[profile]['hash'] and row['case'] == case['name']
            and row['mesh'] == mesh and row['log_sha256'] == E.sha(leaf / 'native.log'),
            'Retained baseline observation identity differs')
        if profile == Q.PROFILES[0]:
            P.need(E.sha(leaf / 'report.json') == BASELINES[profile]['observed_report']
                and E.sha(leaf / 'native.log') == BASELINES[profile]['observed_log'] and row['passed'] is False,
                'Original failed M1 observation differs')
            evidence = Q.observations(raw, case['matrix_names'])
            P.need(len(evidence['warning_or_error_lines']) == 2 and evidence['raw_matrix'] is not None
                and any(P.number(x) < 0 for x in evidence['raw_matrix']['printed_row_sums']),
                'Original failed M1 physics evidence missing')
            records.append(evidence)
        else:
            P.need(E.sha(leaf / 'report.json') == selected[index]['report_sha256'] and row['passed'] is True
                and row['argv'] == ['/solver/runtime/bin/FasterCap', '-b', 'geometry.lst', '-g', '-m' + mesh, '-t0.0005', '-d1']
                and row['exit_code'] == 0 and row['timed_out'] is False
                and all(row[k] is True for k in ('solver_executed', 'process_tree_reaped', 'source_runtime_unchanged', 'copied_inputs_unchanged')),
                'Original mesh leaf did not strictly pass exact custody')
            numeric = P.parse_manual_log(raw, case['matrix_names'], mesh, '0.0005', '1')
            numeric['matrix_F'] = [[str(P.number(x) * P.number(case['coordinate_unit_m'])) for x in r] for r in numeric['matrix']]
            P.need(row['numeric'] == numeric, 'Original mesh strict raw readback differs')
            records.append(numeric)
    if profile == Q.PROFILES[1]:
        changes = [str(P.cellwise_change(a, b)) for a, b in zip(records, records[1:])]
        P.need(P.number(changes[2]) > P.number('.30'), 'Original development mesh-jump evidence differs')
        return {'mesh_changes': changes, 'mesh_stability_passed': False}
    return {'failed_physics_observation': records[0], 'numeric_passed': False}


def prepare(profile, baseline_path, cases, runtime, evidence, observed, output):
    fixed = BASELINES[profile]
    P.need(E.sha(baseline_path) == fixed['hash'] and not output.exists() and output.parent.is_dir(), 'Wrong baseline/fresh owner')
    baseline = json.loads(baseline_path.read_text())
    matched = [c for c in baseline['cases'] if c['name'] == fixed['case']]
    P.need(len(matched) == 1, 'Wrong exact development case membership'); case = matched[0]
    P.need(E.tree(cases / case['name']) == case['files'] and E.tree(runtime) == baseline['runtime']
        and E.sha(runtime / 'bin/FasterCap') == P.SOLVER_SHA256, 'Original geometry/runtime differs')
    if profile == Q.PROFILES[0]:
        P.need(E.sha(cases / 'manifest.json') == baseline['geometry_manifest_sha256']
            and case['coordinate_unit_m'] == '0.00000095367431640625', 'Wrong S20 physical geometry')
    else: P.validate_protocol(baseline['protocol'])
    originals = observation_rows(profile, baseline, observed)
    for row in originals: P.need(E.tree(row['owner'] / 'work') == case['files'], 'Original copied observation geometry differs')
    source_evidence = D.source_evidence(evidence)
    names = set(baseline['producers_sha256']) | set(D.NEW_SOURCES) | set(NEW_SOURCES)
    for n, value in baseline['producers_sha256'].items():
        P.need(E.sha(Path(__file__).with_name(n)) == value, 'Original producer differs')
    output.mkdir()
    for name in ('baseline', 'geometry', 'source-evidence'): (output / name).mkdir()
    shutil.copyfile(baseline_path, output / 'baseline/plan.json')
    shutil.copyfile(observed / 'report.json', output / 'baseline/original-report.json')
    for index, row in enumerate(originals):
        dest = output / 'baseline' / ('observation-' + str(index)); dest.mkdir()
        for n in ('report.json', 'native.log'): shutil.copyfile(row['owner'] / n, dest / n)
    for n in case['files']: shutil.copyfile(cases / case['name'] / n, output / 'geometry' / n)
    for n in source_evidence: shutil.copyfile(evidence / n, output / 'source-evidence' / n)
    if profile == Q.PROFILES[0]: shutil.copyfile(cases / 'manifest.json', output / 'baseline/geometry-manifest.json')
    result = {'schema': 'pinwheel.streaming-8x4-rc-conditioning-plan.v1', 'profile': profile,
        'qualified': False, 'model_qualified': False, 'full_pilot_passed': False, 'native_executed': False,
        'baseline_plan_sha256': fixed['hash'], 'original_report_sha256': fixed['observed_report'],
        'case': case, 'runtime': baseline['runtime'], 'source_evidence': source_evidence,
        'solver_sha256': P.SOLVER_SHA256, 'policy': policy(profile),
        'baseline_observation': check_baseline_observations(profile, output / 'baseline', case),
        'producer_sha256': {n: E.sha(Path(__file__).with_name(n)) for n in sorted(names)},
        'files': inventory(output)}
    write(output / 'plan.json', result); verify(output, E.sha(output / 'plan.json')); return result


def verify(inputs, plan_hash):
    P.need(E.sha(inputs / 'plan.json') == plan_hash, 'Frozen conditioning plan differs')
    plan = json.loads((inputs / 'plan.json').read_text()); profile = plan['profile']; fixed = BASELINES[profile]
    P.need(plan['schema'] == 'pinwheel.streaming-8x4-rc-conditioning-plan.v1'
        and all(plan[k] is False for k in ('qualified', 'model_qualified', 'full_pilot_passed', 'native_executed'))
        and plan['policy'] == policy(profile) and plan['baseline_plan_sha256'] == fixed['hash']
        and E.sha(inputs / 'baseline/plan.json') == fixed['hash'] and inventory(inputs) == plan['files'],
        'Conditioning scope/policy/complete input seals differ')
    baseline = json.loads((inputs / 'baseline/plan.json').read_text())
    matches = [c for c in baseline['cases'] if c['name'] == fixed['case']]
    P.need(len(matches) == 1 and matches[0] == plan['case'] and E.tree(inputs / 'geometry') == plan['case']['files']
        and plan['runtime'] == baseline['runtime'] and plan['solver_sha256'] == baseline['solver_sha256'] == P.SOLVER_SHA256
        and plan['original_report_sha256'] == fixed['observed_report'] == E.sha(inputs / 'baseline/original-report.json')
        and D.source_evidence(inputs / 'source-evidence') == plan['source_evidence']
        and check_baseline_observations(profile, inputs / 'baseline', plan['case']) == plan['baseline_observation'],
        'Conditioning original geometry/runtime/observations/source differs')
    if profile == Q.PROFILES[0]:
        P.need(E.sha(inputs / 'baseline/geometry-manifest.json') == baseline['geometry_manifest_sha256'], 'S20 manifest changed')
    else: P.validate_protocol(baseline['protocol'])
    names = set(baseline['producers_sha256']) | set(D.NEW_SOURCES) | set(NEW_SOURCES)
    P.need(set(plan['producer_sha256']) == names, 'Conditioning producer closure membership differs')
    for n, value in plan['producer_sha256'].items():
        P.need(E.sha(Path(__file__).with_name(n)) == value and baseline['producers_sha256'].get(n, value) == value,
               'Conditioning original/new producer bytes differ')
    return plan


def runtime_unchanged(plan, runtime):
    return D.runtime_unchanged(plan, runtime)


def container_proposal(inputs, plan_hash, runtime, parent, require_fresh=True):
    inputs, runtime, parent = (p.resolve() for p in (inputs, runtime, parent)); plan = verify(inputs, plan_hash)
    profile = plan['profile']; name = BASELINES[profile]['output']; pol = policy(profile)
    P.need(runtime_unchanged(plan, runtime) and parent.is_dir() and (not require_fresh or not (parent / name).exists()), 'Proposal runtime/output differs')
    argv = ['docker', 'run', '--name', 'pinwheel-8x4-' + name, '--rm', '--pull', 'never', '--network', 'none', '--read-only',
        '--cpus', '1', '--memory', '6g', '--memory-swap', '6g', '--pids-limit', '128',
        '--tmpfs', '/tmp:rw,nosuid,noexec,size=536870912',
        '--mount', f'type=bind,src={Path(__file__).resolve().parent},dst=/rc-source,readonly',
        '--mount', f'type=bind,src={inputs},dst=/rc-inputs,readonly',
        '--mount', f'type=bind,src={runtime},dst=/solver/runtime,readonly',
        '--mount', f'type=bind,src={parent},dst=/rc-output-parent',
        '--entrypoint', '/nix/store/lqn6mbgzzdrqq2qkwddcmxj9z6amdd86-python3-3.13.13/bin/python3', D.IMAGE,
        '-I', '-B', '/rc-source/streaming_8x4_rc_conditioning.py', 'run', '--inputs', '/rc-inputs',
        '--plan-sha256', plan_hash, '--runtime', '/solver/runtime', '--output', '/rc-output-parent/' + name]
    return {'schema': 'pinwheel.streaming-8x4-rc-conditioning-command-proposal.v1', 'profile': profile,
        'root_go_required': True, 'native_executed': False, 'admitted': False,
        'model_qualified': False, 'full_pilot_passed': False, 'policy': pol,
        'plan_path': str(inputs / 'plan.json'), 'plan_sha256': plan_hash, 'runtime_path': str(runtime),
        'output_parent': str(parent), 'output_name': name, 'container_name': 'pinwheel-8x4-' + name,
        'timeout_seconds': pol['outer_seconds'], 'producer_sha256': plan['producer_sha256'], 'argv': argv}


def leaf(inputs, plan_hash, plan, branch, runtime, output):
    P.need(branch in Q.branches(plan['profile']) and not output.exists() and output.parent.is_dir()
        and str(runtime) == '/solver/runtime' and runtime_unchanged(plan, runtime), 'Wrong conditioning leaf/runtime')
    output.mkdir(); work = output / 'work'; work.mkdir()
    for n, row in plan['case']['files'].items():
        P.need(Path(n).name == n and row['kind'] == 'file', 'Only flat regular conditioning geometry admitted')
        shutil.copyfile(inputs / 'geometry' / n, work / n); (work / n).chmod(0o444)
    result = {'schema': 'pinwheel.streaming-8x4-rc-conditioning-leaf.v1', 'profile': plan['profile'],
        'qualified': False, 'model_qualified': False, 'full_pilot_passed': False,
        'plan_sha256': plan_hash, 'branch': branch, 'case': plan['case']['name'],
        'argv': Q.argv(branch, plan['profile']), 'environment': ENVIRONMENT,
        'cgroups': E.verify_cgroups(), 'passed': False, 'solver_executed': False,
        'exit_code': None, 'timed_out': False, 'process_tree_reaped': False, 'numeric': None,
        'timeout_seconds': 120, 'scratch_available_bytes_before': shutil.disk_usage('/tmp').free}
    child = None; started = time.monotonic(); raw = ''
    try:
        with (output / 'native.log').open('xb') as stream:
            child = subprocess.Popen(result['argv'], cwd=work, env=dict(ENVIRONMENT), stdout=stream,
                stderr=subprocess.STDOUT, start_new_session=True); result['solver_executed'] = True
            try: result['exit_code'] = child.wait(timeout=120)
            except subprocess.TimeoutExpired:
                result['timed_out'] = True; os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2); result['exit_code'] = child.returncode
        try: os.killpg(child.pid, 0)
        except ProcessLookupError: result['process_tree_reaped'] = True
        else:
            os.killpg(child.pid, signal.SIGKILL); raise ValueError('Conditioning child group remains live')
        P.need(result['exit_code'] == 0 and not result['timed_out'], 'Conditioning solver exit/timeout failed')
        raw = (output / 'native.log').read_text()
        result['numeric'] = Q.parse(raw, plan['case']['matrix_names'], branch, plan['profile'], plan['case']['coordinate_unit_m'])
        result['passed'] = True
    except BaseException as error: result['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if child is not None and child.poll() is None: os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
        result['copied_inputs_unchanged'] = E.tree(work) == plan['case']['files']
        result['source_runtime_unchanged'] = E.tree(inputs / 'geometry') == plan['case']['files'] and runtime_unchanged(plan, runtime)
        result['producer_plan_unchanged'] = verify(inputs, plan_hash) == plan
        raw = (output / 'native.log').read_text() if (output / 'native.log').exists() else raw
        result['log_sha256'] = E.sha(output / 'native.log') if (output / 'native.log').exists() else None
        result['observations'] = Q.observations(raw, plan['case']['matrix_names'])
        result['wall_seconds'] = time.monotonic() - started
        result['scratch_available_bytes_after'] = shutil.disk_usage('/tmp').free
        result['passed'] &= all(result[k] is True for k in ('process_tree_reaped', 'copied_inputs_unchanged', 'source_runtime_unchanged', 'producer_plan_unchanged'))
        write(output / 'report.json', result)
    return result


def run(inputs, plan_hash, runtime, output):
    plan = verify(inputs, plan_hash); profile = plan['profile']; pol = policy(profile)
    P.need(str(runtime) == '/solver/runtime' and runtime_unchanged(plan, runtime)
        and output.name == BASELINES[profile]['output'] and not output.exists() and output.parent.is_dir(), 'Wrong conditioning run owner/runtime')
    E.verify_cgroups(); output.mkdir(); rows = []; leaves = []; started = time.monotonic()
    result = {'schema': 'pinwheel.streaming-8x4-rc-conditioning-execution.v1', 'profile': profile,
        'plan_sha256': plan_hash, 'policy': pol, 'jobs': rows, 'qualified': False, 'model_qualified': False,
        'full_pilot_passed': False, 'measurement_packet_completed': False, 'passed': False}
    try:
        for index, branch in enumerate(Q.branches(profile)):
            P.need(time.monotonic() - started <= pol['work_seconds'] - 130, 'Insufficient next-leaf/cleanup allowance')
            verify(inputs, plan_hash)
            owner = output / ('job-' + str(index).zfill(3)); value = leaf(inputs, plan_hash, plan, branch, runtime, owner)
            rows.append({'branch': branch, 'passed': value['passed'], 'report_sha256': E.sha(owner / 'report.json')})
            D.closed_leaf(value); leaves.append(value)
        result.update(Q.aggregate(profile, leaves)); result['measurement_packet_completed'] = True
    except BaseException as error: result['error'] = type(error).__name__ + ': ' + str(error)
    result['inputs_runtime_unchanged'] = verify(inputs, plan_hash) == plan and runtime_unchanged(plan, runtime)
    result['measurement_packet_completed'] &= result['inputs_runtime_unchanged']
    result['passed'] &= result['measurement_packet_completed']; result['wall_seconds'] = time.monotonic() - started
    write(output / 'report.json', result); return result


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare'); q.add_argument('--profile', choices=Q.PROFILES, required=True)
    for n in ('baseline', 'cases', 'runtime', 'source-evidence', 'observed', 'output'): q.add_argument('--' + n, type=Path, required=True)
    for action in ('verify', 'proposal', 'run'):
        q = sub.add_parser(action); q.add_argument('--inputs', type=Path, required=True); q.add_argument('--plan-sha256', required=True)
        if action != 'verify': q.add_argument('--runtime', type=Path, required=True); q.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if a.action == 'prepare':
        plan = prepare(a.profile, a.baseline, a.cases, a.runtime, a.source_evidence, a.observed, a.output)
        result = {'profile': a.profile, 'plan_sha256': E.sha(a.output / 'plan.json'), 'native_executed': False, 'maximum_calls': plan['policy']['maximum_calls']}
    elif a.action == 'verify':
        plan = verify(a.inputs, a.plan_sha256); result = {'verified': True, 'profile': plan['profile'], 'native_executed': False}
    elif a.action == 'proposal':
        result = container_proposal(a.inputs, a.plan_sha256, a.runtime, a.output.parent); write(a.output, result)
    else: result = run(a.inputs, a.plan_sha256, a.runtime, a.output)
    print(json.dumps(result, indent=2))
    if a.action == 'run' and not result['passed']: raise SystemExit(2)


if __name__ == '__main__': main()
