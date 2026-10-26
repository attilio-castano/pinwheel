"""New fixed 32-grid FVM execution authority; no BEM prerequisite or qualification.

Root alone dispatches Native. Import, preparation and verification only inspect
files and construct small grid inventories. Frozen field equations are reused.
"""
import argparse
import ast
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_all_layers_plan as A
import streaming_8x4_rc_all_layers_execute as V
import streaming_8x4_rc_all_layers_reference as F
import streaming_8x4_rc_full_policy as W
import streaming_8x4_rc_full_readback as H
P, E, M = W.P, W.E, V.M
ROOT = W.ROOT
BASELINE = '37628d053afaf9fd2987bcd7917873cabec76932a9fa4597c190e65391c43f12'
OUTPUT = 'rc-reference-only-32-01'
CONTAINER = 'pinwheel-8x4-' + OUTPUT
NEW = ('streaming_8x4_rc_reference_only.py', 'streaming_8x4_rc_reference_only_readback.py')
PYTHON = '/nix/store/lqn6mbgzzdrqq2qkwddcmxj9z6amdd86-python3-3.13.13/bin/python3'


def policy():
    return {'schema': 'pinwheel.streaming-8x4-rc-reference-only-policy.v1',
        'maximum_calls': 32, 'physical_cases': 8, 'seconds_per_leaf': 120,
        'work_seconds': 1800, 'outer_seconds': 1860, 'cpus': 1,
        'memory_bytes': 2147483648, 'scratch_bytes': 134217728, 'pids': 128,
        'no_extra_swap': True, 'memory_preempt_fraction': '0.95', 'memory_poll_seconds': '0.25',
        'mesh_steps_um': ['.04', '.02'], 'domain_extents_um': ['16', '32'],
        'maximum_nodes': 65000, 'maximum_cg_iterations': 6000,
        'true_residual_relative_tolerance': '1e-9', 'energy_flux_relative_tolerance': '1e-7',
        'reciprocity_relative_tolerance': '1e-7', 'maximum_mesh_change': '0.02', 'maximum_domain_change': '0.02',
        'native_log_policy': 'empty stdout/stderr required; nonempty log is retained closed numerical failure',
        'continue_closed_numerical_failure': True, 'stop_suffix_on_resource_or_custody_failure': True,
        'peak_scope': 'cumulative container cgroup; never reset or claimed as isolated leaf peak',
        'root_go_required': True, 'BEM_prerequisite_required': False,
        'model_qualified': False, 'qualified_timing': False, 'finite_BEM_passed': False,
        'scope': 'eight nominal TYP self/centered-adjacent cases, independent 2D finite-volume reference only; no finite-BEM or full-model authority'}


def sources():
    pending = list(NEW) + ['streaming_8x4_acceptance_resources.py', 'streaming_8x4_acceptance.py', 'streaming_tt_resources.py']; done = {}
    while pending:
        name = pending.pop()
        if name in done: continue
        path = Path(__file__).with_name(name); done[name] = E.sha(path)
        for node in ast.walk(ast.parse(path.read_text())):
            names = [x.name for x in node.names] if isinstance(node, ast.Import) else ([node.module] if isinstance(node, ast.ImportFrom) and node.module else [])
            pending += [n + '.py' for n in names if n.startswith('streaming_') and '.' not in n]
    return dict(sorted(done.items()))


def jobs(plan):
    return [{'case': c['name'], 'step': h, 'extent': e} for c in plan['cases']
            for h in policy()['mesh_steps_um'] for e in policy()['domain_extents_um']]


def baseline(inputs):
    path = inputs / 'original-all-layer-plan.json'
    P.need(E.sha(path) == BASELINE, 'Exact historical all-layer plan changed')
    old = json.loads(path.read_text())
    P.need(old['schema'] == A.SCHEMA and old['M1_complete_pass_required_before_any_numerical_execution'] is True,
           'Historical gated plan authority changed')
    for n, pin in old['producer_sha256'].items():
        P.need(E.sha(Path(__file__).with_name(n)) == pin, 'Historical all-layer producer changed')
    P.need(E.sha(inputs / 'itf-typ.txt') == old['ITF_TYP_sha256'], 'Exact TYP stack changed')
    cases = A.case_universe(A.P.parse_stack((inputs / 'itf-typ.txt').read_text()))
    P.need(cases == old['cases'] and A.grid_inventory(cases) == old['grid_inventory']
        and A.operator_derivation() == old['FVM_derivation']
        and A.reference_storage_budget() == old['reference_structural_storage_admission'],
        'Historical physical/grid/operator authority changed')
    return old


def prepare(original, original_reference, output):
    P.need(not output.exists() and output.parent.is_dir() and E.sha(original / 'plan.json') == BASELINE,
           'Wrong original/fresh reference-only owner')
    # Authenticate the old preparation without invoking its BEM admission path.
    V.verify(original / 'plan.json', BASELINE)
    output.mkdir(); shutil.copyfile(original / 'plan.json', output / 'original-all-layer-plan.json')
    shutil.copyfile(original / 'itf-typ.txt', output / 'itf-typ.txt')
    shutil.copytree(original_reference, output / 'reference')
    old = baseline(output)
    row = {'schema': 'pinwheel.streaming-8x4-rc-reference-only-plan.v1',
        'qualified': False, 'model_qualified': False, 'qualified_timing': False,
        'finite_BEM_passed': False, 'native_executed': False, 'policy': policy(),
        'historical_plan_sha256': BASELINE, 'historical_plan_executed_or_admitted': False,
        'cases': old['cases'], 'grid_inventory': old['grid_inventory'], 'protocol': old['protocol'],
        'FVM_derivation': old['FVM_derivation'], 'storage_admission': old['reference_structural_storage_admission'],
        'original_M1_FVM_control_authority': W.reference_join(output, W.PROFILES[0]),
        'producer_sha256': sources(), 'files': W.input_files(output)}
    W.write(output / 'plan.json', row); verify(output, E.sha(output / 'plan.json')); return row


def verify(inputs, digest):
    P.need(E.sha(inputs / 'plan.json') == digest, 'New reference-only plan hash differs')
    row = json.loads((inputs / 'plan.json').read_text()); old = baseline(inputs)
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-reference-only-plan.v1'
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing', 'finite_BEM_passed', 'native_executed', 'historical_plan_executed_or_admitted'))
        and row['historical_plan_sha256'] == BASELINE and row['policy'] == policy()
        and row['producer_sha256'] == sources() and row['files'] == W.input_files(inputs)
        and row['cases'] == old['cases'] and row['grid_inventory'] == old['grid_inventory']
        and row['protocol'] == old['protocol'] and row['FVM_derivation'] == A.operator_derivation()
        and row['storage_admission'] == A.reference_storage_budget()
        and row['original_M1_FVM_control_authority'] == W.reference_join(inputs, W.PROFILES[0])
        and len(jobs(row)) == 32 and all(g['within_reviewed_65000_node_cap'] is True for g in row['grid_inventory']),
        'Reference-only scope/source/original-reference/case/grid custody differs')
    return row


def proposal(inputs, digest, parent, require_fresh=True):
    inputs, parent = inputs.resolve(), parent.resolve(); plan = verify(inputs, digest)
    P.need(parent.is_dir() and (not require_fresh or not (parent / OUTPUT).exists()), 'Reference-only output owner differs')
    command = ['docker', 'run', '--name', CONTAINER, '--rm', '--pull', 'never', '--network', 'none', '--read-only',
        '--cpus', '1', '--memory', '2g', '--memory-swap', '2g', '--pids-limit', '128',
        '--tmpfs', '/tmp:rw,nosuid,noexec,size=134217728',
        '--mount', f'type=bind,src={Path(__file__).resolve().parent},dst=/rc-source,readonly',
        '--mount', f'type=bind,src={inputs},dst=/rc-inputs,readonly',
        '--mount', f'type=bind,src={parent},dst=/rc-output-parent', '--entrypoint', PYTHON, W.C.D.IMAGE,
        '-I', '-B', '/rc-source/' + NEW[0], 'run', '--inputs', '/rc-inputs', '--plan-sha256', digest,
        '--output', '/rc-output-parent/' + OUTPUT]
    return {'schema': 'pinwheel.streaming-8x4-rc-reference-only-command-proposal.v1',
        'root_go_required': True, 'admitted': False, 'native_executed': False,
        'qualified': False, 'model_qualified': False, 'qualified_timing': False, 'finite_BEM_passed': False,
        'plan_path': str(inputs / 'plan.json'), 'plan_sha256': digest, 'output_name': OUTPUT,
        'container_name': CONTAINER, 'timeout_seconds': 1860, 'policy': policy(),
        'producer_sha256': plan['producer_sha256'], 'argv': command}


def snapshot(root=Path('/sys/fs/cgroup')):
    names = ('memory.current', 'memory.peak', 'memory.max', 'memory.swap.max', 'memory.events', 'memory.events.local', 'cpu.max', 'pids.max')
    row = {n.replace('.', '_'): (root / n).read_text().strip() for n in names}
    for n in ('memory_current', 'memory_peak', 'memory_max', 'memory_swap_max', 'pids_max'):
        P.need(row[n].isdigit(), 'Unsupported FVM cgroup numeric field'); row[n] = int(row[n])
    for n in ('memory_events', 'memory_events_local'):
        fields = [x.split() for x in row[n].splitlines()]
        P.need(all(len(x) == 2 and x[1].isdigit() for x in fields) and len({x[0] for x in fields}) == len(fields), 'Unsupported FVM cgroup event grammar')
        row[n] = {k: int(v) for k, v in fields}
    validate_snapshot(row); return row


def validate_snapshot(row):
    P.need(all(type(row[n]) is int and row[n] >= 0 for n in ('memory_current', 'memory_peak', 'memory_max', 'memory_swap_max', 'pids_max'))
        and 0 < row['memory_max'] <= 2147483648 and row['memory_swap_max'] == 0
        and row['memory_peak'] >= row['memory_current'] and 0 < row['pids_max'] <= 128,
        'Actual FVM cgroup memory/swap/PID policy differs')
    pair = row['cpu_max'].split()
    P.need(len(pair) == 2 and all(x.isdigit() for x in pair) and 0 < int(pair[0]) <= int(pair[1]), 'Actual FVM CPU ceiling differs')
    for n in ('memory_events', 'memory_events_local'):
        P.need({'max', 'oom', 'oom_kill'} <= set(row[n]) and all(type(v) is int and v >= 0 for v in row[n].values()), 'Actual FVM max/OOM counters missing')


def deltas(before, after):
    validate_snapshot(before); validate_snapshot(after)
    P.need(all(before[n] == after[n] for n in ('memory_max', 'memory_swap_max', 'cpu_max', 'pids_max'))
        and after['memory_peak'] >= before['memory_peak'], 'FVM cgroup identity/peak changed')
    result = {}
    for n in ('memory_events', 'memory_events_local'):
        P.need(set(before[n]) == set(after[n]) and all(after[n][k] >= v for k, v in before[n].items()), 'FVM counter reset/membership differs')
        result[n] = {k: after[n][k] - v for k, v in before[n].items()}
    return result


def validate_row(plan, job, row):
    case = next(c for c in plan['cases'] if c['name'] == job['case'])
    V.validate_reference_row(plan, '', case, row, job['step'], job['extent'])
    P.need(math.isfinite(row['wall_seconds']) and row['wall_seconds'] >= 0
        and math.isfinite(row['reciprocity_relative_error']) and 0 <= row['reciprocity_relative_error'] <= 1e-7,
        'FVM actual runtime/reciprocity observation differs')


def one(inputs, digest, index, output):
    plan = verify(inputs, digest); snapshot(); calls = jobs(plan)
    P.need(type(index) is int and 0 <= index < 32 and not output.exists() and output.parent.is_dir(), 'Undeclared FVM leaf/fresh output')
    job = calls[index]; case = next(c for c in plan['cases'] if c['name'] == job['case'])
    result = {'schema': 'pinwheel.streaming-8x4-rc-reference-only-leaf.v1', 'plan_sha256': digest,
        'index': index, 'job': job, 'qualified': False, 'model_qualified': False, 'qualified_timing': False,
        'finite_BEM_passed': False, 'numeric_passed': False, 'kernel_row': None}
    try:
        result['kernel_row'] = F.solve([{'name': r['name'], 'bounds_um': list(map(float, r['bounds_um']))} for r in case['rectangles']],
            [list(map(float, slab)) for slab in case['epsilon_layers']], float(job['extent']), float(job['step']),
            tolerance=1e-9, maximum_iterations=6000, maximum_nodes=65000)
        validate_row(plan, job, result['kernel_row']); result['numeric_passed'] = True
    except (ValueError, KeyError, TypeError, ArithmeticError, MemoryError) as error:
        result['error'] = type(error).__name__ + ': ' + str(error)
    verify(inputs, digest); snapshot(); W.write(output, result); return result


def dispatch_argv(inputs, digest, index, output):
    return [PYTHON, '-I', '-B', '/rc-source/' + NEW[0], 'one', '--inputs', str(inputs),
        '--plan-sha256', digest, '--index', str(index), '--output', str(output)]


def resource_feasible(row):
    differences = deltas(row['cgroup_before'], row['cgroup_after'])
    P.need(row['counter_deltas'] == differences
        and type(row['maximum_polled_memory_current']) is int
        and row['cgroup_before']['memory_current'] <= row['maximum_polled_memory_current'] <= row['cgroup_after']['memory_peak'],
        'FVM polled/kernel peak or counter join differs')
    return (row['process_tree_reaped'] is True and row['timed_out'] is False and row['memory_guard_triggered'] is False
        and type(row['exit_code']) is int and row['exit_code'] in (0, 2)
        and row['maximum_polled_memory_current'] < row['cgroup_after']['memory_max'] * 95 // 100
        and row['cgroup_after']['memory_peak'] < row['cgroup_after']['memory_max'] * 95 // 100
        and all(v == 0 for n in differences.values() for k, v in n.items() if k == 'max' or k.startswith('oom')))


def dispatch(inputs, digest, index, owner):
    owner.mkdir(); target = owner / 'leaf.json'; before = snapshot(); child = None; started = time.monotonic()
    row = {'schema': 'pinwheel.streaming-8x4-rc-reference-only-dispatch.v1', 'index': index,
        'plan_sha256': digest, 'argv': dispatch_argv(inputs, digest, index, target), 'timeout_seconds': 120,
        'cgroup_before': before, 'maximum_polled_memory_current': before['memory_current'],
        'timed_out': False, 'memory_guard_triggered': False, 'process_tree_reaped': False, 'exit_code': None,
        'numeric_passed': False, 'resource_feasible': False, 'leaf_sha256': None, 'native_log_empty': False}
    try:
        with (owner / 'native.log').open('xb') as stream:
            child = subprocess.Popen(row['argv'], stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            while child.poll() is None:
                current = snapshot()['memory_current']; row['maximum_polled_memory_current'] = max(current, row['maximum_polled_memory_current'])
                if current >= before['memory_max'] * 95 // 100:
                    row['memory_guard_triggered'] = True; break
                if time.monotonic() - started >= 120:
                    row['timed_out'] = True; break
                time.sleep(.25)
            if child.poll() is None: os.killpg(child.pid, signal.SIGKILL)
            row['exit_code'] = child.wait(timeout=2)
        try: os.killpg(child.pid, 0)
        except ProcessLookupError: row['process_tree_reaped'] = True
        else: os.killpg(child.pid, signal.SIGKILL); raise ValueError('FVM child process group remained live')
        if target.exists():
            leaf = json.loads(target.read_text()); row['leaf_sha256'] = E.sha(target)
            row['numeric_passed'] = leaf['numeric_passed'] is True and row['exit_code'] == 0
    except BaseException as error:
        row['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if child is not None and child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
        row['cgroup_after'] = snapshot(); row['counter_deltas'] = deltas(before, row['cgroup_after'])
        row['resource_feasible'] = resource_feasible(row) and row['leaf_sha256'] is not None
        row['log_sha256'] = E.sha(owner / 'native.log') if (owner / 'native.log').exists() else None
        row['native_log_empty'] = (owner / 'native.log').is_file() and (owner / 'native.log').stat().st_size == 0
        row['numeric_passed'] = row['numeric_passed'] and row['native_log_empty']
        row['wall_seconds'] = time.monotonic() - started; W.write(owner / 'dispatch.json', row)
    return row


def run(inputs, digest, output):
    started = time.monotonic(); plan = verify(inputs, digest); snapshot()
    P.need(not output.exists() and output.parent.is_dir(), 'Reference-only run output must be fresh'); output.mkdir()
    row = {'schema': 'pinwheel.streaming-8x4-rc-reference-only-execution.v1', 'plan_sha256': digest,
        'policy': policy(), 'qualified': False, 'model_qualified': False, 'qualified_timing': False,
        'finite_BEM_passed': False, 'reference_stability_passed': False, 'measurement_packet_completed': False,
        'all_numeric_leaves_passed': False, 'resource_feasible': False, 'passed': False, 'jobs': []}
    try:
        for index, job in enumerate(jobs(plan)):
            P.need(time.monotonic() - started < 1670, 'Reference-only lacks full next-leaf budget')
            dispatch_row = dispatch(inputs, digest, index, output / ('job-' + str(index).zfill(3)))
            row['jobs'].append(dict(job, index=index, dispatch_sha256=E.sha(output / ('job-' + str(index).zfill(3)) / 'dispatch.json'),
                numeric_passed=dispatch_row['numeric_passed'], resource_feasible=dispatch_row['resource_feasible']))
            verify(inputs, digest)
            P.need(dispatch_row['resource_feasible'], 'Reference-only resource/custody failure stops suffix')
    except BaseException as error: row['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        verify(inputs, digest); row['inputs_sources_unchanged'] = True
        row['measurement_packet_completed'] = len(row['jobs']) == 32 and all(j['resource_feasible'] for j in row['jobs'])
        row['resource_feasible'] = row['measurement_packet_completed']
        row['all_numeric_leaves_passed'] = row['measurement_packet_completed'] and all(j['numeric_passed'] for j in row['jobs'])
        row['passed'] = row['all_numeric_leaves_passed']; row['wall_seconds'] = time.monotonic() - started
        W.write(output / 'report.json', row)
    return row


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare')
    for n in ('original', 'original-reference', 'output'): q.add_argument('--' + n, type=Path, required=True)
    for action in ('verify', 'proposal', 'one', 'run'):
        q = sub.add_parser(action); q.add_argument('--inputs', type=Path, required=True); q.add_argument('--plan-sha256', required=True)
        if action in ('proposal', 'one', 'run'): q.add_argument('--output', type=Path, required=True)
        if action == 'one': q.add_argument('--index', type=int, required=True)
    a = p.parse_args()
    if a.action == 'prepare':
        prepare(a.original, a.original_reference, a.output); print(E.sha(a.output / 'plan.json')); return 0
    if a.action == 'verify': verify(a.inputs, a.plan_sha256); print('verified'); return 0
    if a.action == 'proposal': W.write(a.output, proposal(a.inputs, a.plan_sha256, a.output.parent / 'rc-native-outputs')); return 0
    result = one(a.inputs, a.plan_sha256, a.index, a.output) if a.action == 'one' else run(a.inputs, a.plan_sha256, a.output)
    return 0 if result['numeric_passed' if a.action == 'one' else 'passed'] else 2


if __name__ == '__main__': raise SystemExit(main())
