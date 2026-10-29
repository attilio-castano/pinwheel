"""Fixed, separately typed four-call conditioning/interaction diagnostic.

Root alone admits Native execution. Numeric failures remain failures while the
predeclared factorial continues only after each child is reaped and immutable
inputs/runtime reopen. This worker cannot qualify a model or a full wire pilot.
"""
import argparse
from datetime import datetime, timezone
import hashlib
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
import streaming_8x4_rc_solver_diagnostic_parser as Q

BASELINE_HASH = '2ae5d3b357b92677963eed5e27d4e847e3ffc896ab86f70c73ff5b861990f260'
CASE = 'wire_w0p32_L30_M30'
SOURCE_MANIFEST_HASH = 'bc77f662bc2bf61c255194110255944c71667413f849d597a3dcb8f880577417'
NEW_SOURCES = ('streaming_8x4_rc_solver_diagnostic.py', 'streaming_8x4_rc_solver_diagnostic_parser.py',
               'streaming_8x4_rc_solver_diagnostic_readback.py')
CONTAINER = 'pinwheel-8x4-rc-solver-diagnostic-01'
OUTPUT = 'rc-solver-diagnostic-01'
IMAGE = 'sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92'
ENVIRONMENT = {'PATH': '/nix/store/4yfx6p85jy8v8003v5ia8c738mbcwnnq-coreutils-full-9.11/bin:/usr/bin:/bin',
    'HOME': '/tmp', 'LANG': 'C', 'LC_ALL': 'C', 'TZ': 'UTC',
    'OMP_NUM_THREADS': '1', 'OMP_DYNAMIC': 'FALSE', 'LD_BIND_NOW': '1'}


def protocol():
    return {'schema': 'pinwheel.streaming-8x4-rc-four-call-numerical-protocol.v1',
        'branches': Q.BRANCHES, 'case': CASE, 'manual_mesh': Q.MESH, 'gmres_tolerance': Q.GMRES,
        'scheme': 'Galerkin', 'coordinate_unit_m': '0.000001', 'maximum_calls': 4,
        'seconds_per_leaf': 120, 'work_seconds': 540, 'outer_seconds': 600,
        'cpus': 1, 'memory_bytes': 6442450944, 'scratch_bytes': 536870912,
        'no_extra_swap': True, 'warnings_fatal': True, 'root_go_required': True,
        'automatic_retry_or_parameter_selection': False,
        'qualification_scope': 'development same-geometry diagnostic only; no mesh, independent-reference or full uniform-pilot admission',
        'numeric_failure_policy': 'retain branch failure and continue exact remaining branches only after terminal reap and immutable input/runtime checks',
        'model_qualified': False, 'continuum_error_enclosure': False}


def write(path, data):
    P.need(not path.exists() and path.parent.is_dir(), 'Preserve existing diagnostic artifact')
    E.write(path, data)


def source_evidence(owner):
    path = owner / 'manifest.json'
    P.need(E.sha(path) == SOURCE_MANIFEST_HASH, 'Pinned iterative source intake differs')
    manifest = json.loads(path.read_text())
    P.need(manifest['fastercap_commit'] == 'b42179a8fdd25ab42fe45527282b4a738d7e7f87'
           and len(manifest['files']) == 5 and manifest['native_executed'] is False,
           'Wrong source evidence membership/provenance')
    for row in manifest['files']:
        item = owner / row['name']; raw = item.read_bytes()
        P.need(Path(row['name']).name == row['name'] and not item.is_symlink()
               and len(raw) == row['bytes'] and E.sha(item) == row['sha256']
               and hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == row['git_blob'],
               'Exact primary source blob differs')
    return E.tree(owner)


def prepare(baseline_plan, cases, runtime, source_intake, failed_owner, output):
    P.need(E.sha(baseline_plan) == BASELINE_HASH and not output.exists() and output.parent.is_dir(),
           'Baseline/fresh numerical diagnostic owner differs')
    old = json.loads(baseline_plan.read_text()); P.validate_protocol(old['protocol'])
    selected = [c for c in old['cases'] if c['name'] == CASE]
    P.need(len(selected) == 1, 'Exact failed case is missing/duplicated'); case = selected[0]
    P.need(case['width_um'] == '0.32' and case['length_um'] == case['margin_um'] == '30'
           and case['coordinate_unit_m'] == '0.000001' and E.tree(cases / CASE) == case['files'],
           'Failed physical geometry/unit differs')
    failed = json.loads((failed_owner / 'report.json').read_text())
    P.need(failed['plan_sha256'] == BASELINE_HASH and failed['case'] == CASE and failed['mesh'] == Q.MESH
           and failed['passed'] is False and failed['exit_code'] == 0 and failed['process_tree_reaped'] is True
           and failed['source_runtime_unchanged'] is True and failed['copied_inputs_unchanged'] is True
           and E.sha(failed_owner / 'native.log') == failed['log_sha256']
           and E.tree(failed_owner / 'work') == case['files']
           and Q.failure_evidence((failed_owner / 'native.log').read_text())['nonconvergence_reports'],
           'Original observed numerical failure identity differs')
    P.need(E.tree(runtime) == old['runtime'] and E.sha(runtime / 'bin/FasterCap') == P.SOLVER_SHA256,
           'Unchanged diagnostic runtime differs')
    evidence = source_evidence(source_intake); producers = dict(old['producers_sha256'])
    for name, value in producers.items():
        P.need(E.sha(Path(__file__).with_name(name)) == value, 'Frozen uniform producer differs')
    for name in NEW_SOURCES: producers[name] = E.sha(Path(__file__).with_name(name))
    output.mkdir(); (output / 'baseline').mkdir(); (output / 'geometry').mkdir(); (output / 'source-evidence').mkdir()
    shutil.copyfile(baseline_plan, output / 'baseline/plan.json')
    for name in ('report.json', 'native.log'): shutil.copyfile(failed_owner / name, output / 'baseline' / ('failed-' + name))
    for name in case['files']: shutil.copyfile(cases / CASE / name, output / 'geometry' / name)
    for name in evidence: shutil.copyfile(source_intake / name, output / 'source-evidence' / name)
    plan = {'schema': 'pinwheel.streaming-8x4-rc-solver-diagnostic-plan.v1', 'qualified': False,
        'model_qualified': False, 'uniform_finite_wire_pilot_passed': False, 'native_executed': False,
        'baseline_plan_sha256': BASELINE_HASH, 'case': case, 'runtime': old['runtime'],
        'solver_sha256': P.SOLVER_SHA256, 'source_evidence': evidence, 'protocol': protocol(),
        'producer_sha256': producers, 'failed_baseline_report_sha256': E.sha(failed_owner / 'report.json'),
        'failed_baseline_log_sha256': E.sha(failed_owner / 'native.log'),
        'created_utc': datetime.now(timezone.utc).isoformat()}
    write(output / 'plan.json', plan); verify(output, E.sha(output / 'plan.json'))
    return {'plan_sha256': E.sha(output / 'plan.json'), 'native_executed': False, 'maximum_calls': 4}


def verify(inputs, plan_hash):
    P.need(E.sha(inputs / 'plan.json') == plan_hash, 'Frozen diagnostic plan differs')
    plan = json.loads((inputs / 'plan.json').read_text())
    P.need(plan['schema'] == 'pinwheel.streaming-8x4-rc-solver-diagnostic-plan.v1'
           and plan['qualified'] is False and plan['model_qualified'] is False
           and plan['uniform_finite_wire_pilot_passed'] is False and plan['native_executed'] is False
           and plan['protocol'] == protocol() and plan['baseline_plan_sha256'] == BASELINE_HASH
           and E.sha(inputs / 'baseline/plan.json') == BASELINE_HASH,
           'Diagnostic typed scope/protocol/baseline differs')
    old = json.loads((inputs / 'baseline/plan.json').read_text())
    P.need(plan['case'] == next(c for c in old['cases'] if c['name'] == CASE)
           and E.tree(inputs / 'geometry') == plan['case']['files']
           and plan['runtime'] == old['runtime'] and plan['solver_sha256'] == old['solver_sha256'] == P.SOLVER_SHA256
           and source_evidence(inputs / 'source-evidence') == plan['source_evidence'],
           'Exact diagnostic physical geometry/runtime/source evidence differs')
    P.need(E.sha(inputs / 'baseline/failed-report.json') == plan['failed_baseline_report_sha256']
           and E.sha(inputs / 'baseline/failed-native.log') == plan['failed_baseline_log_sha256'],
           'Original failed receipt/log changed')
    P.need(set(plan['producer_sha256']) == set(old['producers_sha256']) | set(NEW_SOURCES)
           and all(plan['producer_sha256'][name] == value for name, value in old['producers_sha256'].items()),
           'Diagnostic/frozen producer exact membership differs')
    for name, value in plan['producer_sha256'].items():
        P.need(E.sha(Path(__file__).with_name(name)) == value, 'Diagnostic/frozen producer bytes differ')
    return plan


def runtime_unchanged(plan, runtime):
    return E.tree(runtime) == plan['runtime'] and E.sha(runtime / 'bin/FasterCap') == P.SOLVER_SHA256


def leaf(inputs, plan_hash, plan, branch, runtime, output):
    P.need(branch in Q.BRANCHES and not output.exists() and output.parent.is_dir()
           and str(runtime) == '/solver/runtime' and runtime_unchanged(plan, runtime),
           'Diagnostic branch/runtime/output owner differs')
    output.mkdir(); work = output / 'work'; work.mkdir(); source = inputs / 'geometry'
    for name, row in plan['case']['files'].items():
        P.need(Path(name).name == name and row['kind'] == 'file', 'Only flat regular copied diagnostic inputs admitted')
        shutil.copyfile(source / name, work / name); (work / name).chmod(0o444)
    env = dict(ENVIRONMENT)
    result = {'schema': 'pinwheel.streaming-8x4-rc-solver-diagnostic-leaf.v1',
        'qualified': False, 'model_qualified': False, 'uniform_finite_wire_pilot_passed': False,
        'plan_sha256': plan_hash, 'case': CASE, 'branch': branch, 'argv': Q.argv(branch), 'environment': env,
        'cgroups': E.verify_cgroups(), 'passed': False, 'solver_executed': False,
        'exit_code': None, 'timed_out': False, 'process_tree_reaped': False,
        'scratch_available_bytes_before': shutil.disk_usage('/tmp').free}
    child = None; started = time.monotonic(); raw = ''
    try:
        with (output / 'native.log').open('xb') as stream:
            child = subprocess.Popen(result['argv'], cwd=work, env=env, stdout=stream,
                stderr=subprocess.STDOUT, start_new_session=True); result['solver_executed'] = True
            try: result['exit_code'] = child.wait(timeout=120)
            except subprocess.TimeoutExpired:
                result['timed_out'] = True; os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
                result['exit_code'] = child.returncode
        try: os.killpg(child.pid, 0)
        except ProcessLookupError: result['process_tree_reaped'] = True
        else:
            os.killpg(child.pid, signal.SIGKILL); raise ValueError('Diagnostic child group remains live')
        raw = (output / 'native.log').read_text()
        P.need(type(result['exit_code']) is int and result['exit_code'] == 0 and not result['timed_out'],
               'Diagnostic solver exit/timeout failed')
        result['numeric'] = Q.parse(raw, plan['case']['matrix_names'], branch, plan['case']['coordinate_unit_m'])
        result['passed'] = True
    except BaseException as error: result['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if child is not None and child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
        result['copied_inputs_unchanged'] = E.tree(work) == plan['case']['files']
        result['source_runtime_unchanged'] = E.tree(source) == plan['case']['files'] and runtime_unchanged(plan, runtime)
        result['producer_plan_unchanged'] = verify(inputs, plan_hash) == plan
        log = output / 'native.log'
        if log.exists(): raw = log.read_text()
        result['log_sha256'] = E.sha(log) if log.exists() else None
        result['failure_evidence'] = Q.failure_evidence(raw)
        result['wall_seconds'] = time.monotonic() - started
        result['scratch_available_bytes_after'] = shutil.disk_usage('/tmp').free
        result['passed'] &= all(result[k] is True for k in ('process_tree_reaped', 'copied_inputs_unchanged', 'source_runtime_unchanged', 'producer_plan_unchanged'))
        write(output / 'report.json', result)
    return result


def command_proposal(inputs, plan_hash, runtime, output_parent, require_fresh=True):
    inputs, runtime, output_parent = (p.resolve() for p in (inputs, runtime, output_parent))
    plan = verify(inputs, plan_hash)
    P.need(runtime_unchanged(plan, runtime) and output_parent.is_dir()
           and (not require_fresh or not (output_parent / OUTPUT).exists()), 'Proposal runtime/output owner differs')
    argv = ['docker', 'run', '--name', CONTAINER, '--rm', '--pull', 'never', '--network', 'none', '--read-only',
        '--cpus', '1', '--memory', '6g', '--memory-swap', '6g', '--pids-limit', '128',
        '--tmpfs', '/tmp:rw,nosuid,noexec,size=536870912',
        '--mount', f'type=bind,src={Path(__file__).resolve().parent},dst=/rc-source,readonly',
        '--mount', f'type=bind,src={inputs},dst=/rc-inputs,readonly',
        '--mount', f'type=bind,src={runtime},dst=/solver/runtime,readonly',
        '--mount', f'type=bind,src={output_parent},dst=/rc-output-parent',
        '--entrypoint', '/nix/store/lqn6mbgzzdrqq2qkwddcmxj9z6amdd86-python3-3.13.13/bin/python3', IMAGE,
        '-I', '-B', '/rc-source/streaming_8x4_rc_solver_diagnostic.py', 'run',
        '--inputs', '/rc-inputs', '--plan-sha256', plan_hash, '--runtime', '/solver/runtime',
        '--output', '/rc-output-parent/' + OUTPUT]
    return {'schema': 'pinwheel.streaming-8x4-rc-solver-diagnostic-command-proposal.v1',
        'root_go_required': True, 'admitted': False, 'native_executed': False, 'model_qualified': False,
        'container_name': CONTAINER, 'timeout_seconds': 600, 'work_seconds': 540, 'maximum_calls': 4,
        'plan_path': str(inputs / 'plan.json'), 'plan_sha256': plan_hash,
        'runtime_path': str(runtime), 'output_parent': str(output_parent),
        'producers_sha256': plan['producer_sha256'], 'argv': argv, 'protocol': protocol()}


def closed_leaf(result):
    P.need(type(result['exit_code']) is int and all(result[k] is True for k in
        ('solver_executed', 'process_tree_reaped', 'copied_inputs_unchanged', 'source_runtime_unchanged', 'producer_plan_unchanged')),
        'Cannot advance factorial after missing execution/reaping/custody')


def run(inputs, plan_hash, runtime, output):
    plan = verify(inputs, plan_hash)
    P.need(str(runtime) == '/solver/runtime' and runtime_unchanged(plan, runtime), 'Exact diagnostic runtime mount differs')
    P.need(not output.exists() and output.parent.is_dir(), 'Diagnostic output owner must be fresh')
    E.verify_cgroups(); output.mkdir(); rows = []; started = time.monotonic()
    result = {'schema': 'pinwheel.streaming-8x4-rc-solver-diagnostic-execution.v1',
        'qualified': False, 'model_qualified': False, 'uniform_finite_wire_pilot_passed': False,
        'plan_sha256': plan_hash, 'protocol': protocol(), 'jobs': rows,
        'measurement_packet_completed': False, 'passed': False}
    try:
        for index, branch in enumerate(Q.BRANCHES):
            P.need(time.monotonic() - started <= 410, 'Insufficient540s work allowance for next120s leaf and cleanup')
            verify(inputs, plan_hash)
            directory = output / ('job-' + str(index).zfill(3))
            value = leaf(inputs, plan_hash, plan, branch, runtime, directory)
            rows.append({'branch': branch, 'passed': value['passed'], 'report_sha256': E.sha(directory / 'report.json')})
            closed_leaf(value)
        P.need([r['branch'] for r in rows] == Q.BRANCHES, 'Incomplete exact factorial membership')
        result['measurement_packet_completed'] = True
        result['passed'] = all(r['passed'] is True for r in rows)
    except BaseException as error: result['error'] = type(error).__name__ + ': ' + str(error)
    result['inputs_runtime_unchanged'] = verify(inputs, plan_hash) == plan and runtime_unchanged(plan, runtime)
    result['measurement_packet_completed'] &= result['inputs_runtime_unchanged']
    result['passed'] &= result['measurement_packet_completed']; result['wall_seconds'] = time.monotonic() - started
    write(output / 'report.json', result); return result


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare')
    for name in ('baseline-plan', 'cases', 'runtime', 'source-intake', 'failed-owner', 'output'):
        q.add_argument('--' + name, type=Path, required=True)
    for action in ('verify', 'run'):
        q = sub.add_parser(action); q.add_argument('--inputs', type=Path, required=True); q.add_argument('--plan-sha256', required=True)
        if action == 'run':
            q.add_argument('--runtime', type=Path, required=True); q.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if a.action == 'prepare': result = prepare(a.baseline_plan, a.cases, a.runtime, a.source_intake, a.failed_owner, a.output)
    elif a.action == 'verify': result = verify(a.inputs, a.plan_sha256)
    else: result = run(a.inputs, a.plan_sha256, a.runtime, a.output)
    print(json.dumps(result, indent=2))
    if a.action == 'run' and not result['passed']: raise SystemExit(2)


if __name__ == '__main__': main()
