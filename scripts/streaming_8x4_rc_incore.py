"""New two-leaf -f0 resource diagnostic; Root alone authorizes Native."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_full_policy as W
import streaming_8x4_rc_full_execute as X
import streaming_8x4_rc_full_readback as F

P, E = W.P, W.E
NEW = ('streaming_8x4_rc_incore.py', 'streaming_8x4_rc_incore_readback.py')
OUTPUT = 'rc-incore-two-leaf-01'
CONTAINER = 'pinwheel-8x4-' + OUTPUT
SCALING_MANIFEST = 'd6960d37af68a21544bf1ed3654c5ed271fb4445ca1c4c96b8ccd2559a8bd8f8'
FIXED = [
    {'profile': W.PROFILES[0], 'case': 'TYP-w.16-self-L10-E20', 'mesh': '0.000086349', 'job': 3,
     'preparation': 'rc-full-m1-d025-preparation-03', 'proposal': 'rc-full-layered-m1-jacobi-d025-command-proposal-02.json',
     'plan_sha256': 'b8b525dcccdf0de366c42da573ec89211f149a2b32a2f846cbb110eb01336d68',
     'parent_sha256': 'e86db1cbc822c737e85e07fe0b26d1e6fda1ff6614717e127fef77acef2343ae',
     'resource_sha256': '7ed1b4a6254a57cbd4ad2bc2e282c87653747df62c7aae7259c0b1c86af9e289',
     'leaf_sha256': '659fd1419396e1cfb212ceaed71f2e926a6d044cb1e0195c811260d4357a65b6',
     'log_sha256': '08439320c3ce3b8d8e8525e48eef7200aba73e5524b28d33d6cce1e7156f0ab5',
     'links': 149944592, 'panels': 47709, 'old_allocated_KiB': 1428226},
    {'profile': W.PROFILES[1], 'case': 'historical_U_new_manual', 'mesh': '0.0000431745', 'job': 4,
     'preparation': 'rc-full-uniform-d025-preparation-01', 'proposal': 'rc-full-uniform-two-level-d025-command-proposal-01.json',
     'plan_sha256': '1981b870525ef5253da1cb78612976ebe18306392f1bfe6480cffef7575c82ff',
     'parent_sha256': '9313b98a93f680a182fd187b89cf6369a724e9134445aa154770cc46b65de996',
     'resource_sha256': '1f67c9faac9dcbf51f405a22ca1170a0f62ae85809b91aeb64340668c3c337b2',
     'leaf_sha256': 'b0edd854c8ce293fd1a4bb39fccd9c4b6b341b8d0b5e9157848cc9cfc47a748c',
     'log_sha256': '5e2441e42283e082c609e7bbc3cd4e9cd39e23ab6b4fe913b84790148b3c1131',
     'links': 124202962, 'panels': 54140, 'old_allocated_KiB': 1430661}]


def policy():
    return {'schema': 'pinwheel.streaming-8x4-rc-incore-policy.v1', 'maximum_calls': 2,
        'only_solver_delta': ['-f0'], 'work_seconds': 270, 'outer_seconds': 330, 'seconds_per_leaf': 120,
        'cpus': 1, 'memory_bytes': 6442450944, 'no_extra_swap': True, 'pids': 128, 'scratch_bytes': 536870912,
        'memory_preempt_fraction': '0.95', 'memory_poll_seconds': '0.25', 'mandatory_actual_f_header': '0',
        'capture': ['memory.current', 'memory.peak', 'memory.events', 'memory.events.local', 'memory.max', 'memory.swap.max'],
        'peak_scope': 'cumulative container cgroup; not reset or claimed as isolated leaf peak',
        'stop_suffix_on_resource_or_custody_failure': True, 'root_go_required': True,
        'model_qualified': False, 'full_pilot_passed': False, 'qualified_timing': False,
        'scope': 'two exact failed leaves only; resource feasibility and point numerical outcomes are separate'}


def estimate(fixed):
    n = fixed['panels']; links = math.ceil(fixed['links'] / 1048576) * 1048576 * 16
    rows = {'old_allocated_bytes_including_existing_link_buffers': fixed['old_allocated_KiB'] * 1024,
        'complete_rounded_link_bytes': links, 'two_worst_1001_vector_arrays_bytes': 2 * 1001 * n * 8,
        'work_vectors_bytes': 24 * n * 8, 'Hessenberg_reserve_bytes': 8016000,
        'maximum_SUPER_matrices_bytes': 2 * 4096 ** 2 * 8 if fixed['profile'] == W.PROFILES[1] else 0,
        'additional_untracked_reserve_bytes': 536870912}
    return {'terms': rows, 'planning_total_bytes': sum(rows.values()), 'not_a_proven_malloc_bound': True,
        'deliberate_double_count_of_old_link_buffers': True,
        'admission': sum(rows.values()) < 6442450944 * 95 // 100}


def sources():
    return dict(W.source_closure(), **{n: E.sha(Path(__file__).with_name(n)) for n in NEW})


def source_evidence(inputs):
    iterative = inputs / 'iterative-source'; scaling = inputs / 'refinement-source'
    W.C.D.source_evidence(iterative)
    P.need(E.sha(scaling / 'manifest.json') == SCALING_MANIFEST, 'Pinned refinement source manifest differs')
    manifest = json.loads((scaling / 'manifest.json').read_text())
    P.need(manifest['fastercap_commit'] == 'b42179a8fdd25ab42fe45527282b4a738d7e7f87' and manifest['native_executed'] is False,
           'Wrong refinement source provenance')
    for row in manifest['files']:
        path = scaling / row['name']; raw = path.read_bytes()
        P.need(Path(row['name']).name == row['name'] and not path.is_symlink() and len(raw) == row['bytes']
            and E.sha(path) == row['sha256'] and hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == row['git_blob'],
            'Pinned refinement source blob differs')
    return {'iterative': E.tree(iterative), 'refinement': E.tree(scaling)}


def original(inputs, index):
    fixed = FIXED[index]; owner = inputs / ('original-' + str(index))
    plan = W.verify(owner / 'preparation', fixed['plan_sha256'])
    for name, pin in [('parent.json', fixed['parent_sha256']), ('resource.json', fixed['resource_sha256']),
                      ('failed/report.json', fixed['leaf_sha256']), ('failed/native.log', fixed['log_sha256'])]:
        P.need(E.sha(owner / name) == pin, 'Exact failed original authority differs')
    parent = json.loads((owner / 'parent.json').read_text()); leaf = json.loads((owner / 'failed/report.json').read_text())
    resource = json.loads((owner / 'resource.json').read_text()); proposal = json.loads((owner / 'proposal.json').read_text())
    P.need(parent['plan_sha256'] == fixed['plan_sha256'] and parent['passed'] is False
        and parent['jobs'][fixed['job']]['report_sha256'] == fixed['leaf_sha256'] and len(parent['jobs']) == fixed['job'] + 1
        and leaf['exit_code'] == 74 and leaf['passed'] is False and leaf['numeric'] is None
        and leaf['case'] == fixed['case'] and leaf['mesh'] == fixed['mesh']
        and leaf['argv'] == W.solver_argv(plan['policy'], fixed['mesh'])
        and resource['argv'] == proposal['argv'] and resource['status'] == 'failed' and resource['exit_code'] == 2
        and resource['cleanup_confirmed'] is True and resource['inputs_unchanged'] is True
        and resource['owned_processes_remaining'] == [] and resource['containers_remaining'] == [],
        'Original file-allocation failure/terminal custody differs')
    X.closed(leaf); case = next(c for c in plan['cases'] if c['name'] == fixed['case'])
    P.need(E.tree(owner / 'failed/work') == case['files'], 'Original failed copied geometry differs')
    raw = (owner / 'failed/native.log').read_text()
    P.need(re.findall(r'^Number of links to be computed: (\d+)$', raw, re.M) == [str(fixed['links'])]
        and re.findall(r'^Number of panels after refinement: (\d+)$', raw, re.M) == [str(fixed['panels'])]
        and 'Cannot go out-of-core, trying to continue in-core' in raw and 'Error: File error, program execution stopped!' in raw,
        'Exact resource failure observation differs')
    return plan, case


def prepare(campaign, runtime, output):
    P.need(campaign.resolve() == W.ROOT / 'build/campaigns/8x4-20261022-01' and not output.exists() and output.parent.is_dir(),
           'Wrong campaign/fresh in-core owner')
    # Full frozen HOST reopens establish the actual parent resource/source joins.
    for fixed in FIXED:
        pp = campaign / fixed['proposal']; p = json.loads(pp.read_text())
        result = F.readback(campaign / fixed['preparation'], fixed['plan_sha256'], campaign / 'rc-native-outputs' / p['output_name'], runtime,
            W.ROOT / 'build/streaming-tt-resources' / ('8x4-' + p['output_name']) / 'report.json', pp)
        P.need(result['limited_pilot_passed'] is False, 'Original failed pilot was promoted')
    output.mkdir()
    shutil.copytree(campaign / 'rc-solver-diagnostic-preparation-01/source-evidence', output / 'iterative-source')
    shutil.copytree(campaign / 'rc-fastercap-scale-source-intake-03', output / 'refinement-source')
    cases = []
    for index, fixed in enumerate(FIXED):
        owner = output / ('original-' + str(index)); owner.mkdir()
        p = json.loads((campaign / fixed['proposal']).read_text()); run = campaign / 'rc-native-outputs' / p['output_name']
        shutil.copytree(campaign / fixed['preparation'], owner / 'preparation')
        shutil.copytree(run / ('job-' + str(fixed['job']).zfill(3)), owner / 'failed')
        for source, name in [(run / 'report.json', 'parent.json'), (campaign / fixed['proposal'], 'proposal.json'),
            (W.ROOT / 'build/streaming-tt-resources' / ('8x4-' + p['output_name']) / 'report.json', 'resource.json')]:
            shutil.copyfile(source, owner / name)
        old, case = original(output, index); P.need(E.tree(runtime) == old['runtime'], 'Original in-core runtime differs')
        cases.append(case)
    result = {'schema': 'pinwheel.streaming-8x4-rc-incore-plan.v1', 'qualified': False, 'model_qualified': False,
        'full_pilot_passed': False, 'qualified_timing': False, 'native_executed': False,
        'fixed_leaves': FIXED, 'cases': cases, 'policy': policy(), 'source_evidence': source_evidence(output),
        'memory_estimates': [estimate(f) for f in FIXED], 'runtime': E.tree(runtime), 'producer_sha256': sources(),
        'files': W.input_files(output)}
    W.write(output / 'plan.json', result); verify(output, E.sha(output / 'plan.json')); return result


def verify(inputs, digest):
    P.need(E.sha(inputs / 'plan.json') == digest, 'New in-core plan hash differs')
    row = json.loads((inputs / 'plan.json').read_text())
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-incore-plan.v1'
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'full_pilot_passed', 'qualified_timing', 'native_executed'))
        and row['policy'] == policy() and row['fixed_leaves'] == FIXED and row['producer_sha256'] == sources()
        and row['files'] == W.input_files(inputs) and row['source_evidence'] == source_evidence(inputs)
        and row['memory_estimates'] == [estimate(f) for f in FIXED] and all(e['admission'] for e in row['memory_estimates']),
        'In-core typed scope/input/source/resource policy differs')
    for i, case in enumerate(row['cases']):
        old, observed = original(inputs, i)
        P.need(case == observed and row['runtime'] == old['runtime'], 'Exact failed leaf geometry/runtime differs')
    P.need(len(row['cases']) == 2, 'Exactly two failed resource leaves required')
    return row


def argv(inputs, index):
    old, _ = original(inputs, index)
    return W.solver_argv(old['policy'], FIXED[index]['mesh']) + ['-f0']


def proposal(inputs, digest, runtime, parent, require_fresh=True):
    inputs, runtime, parent = (x.resolve() for x in (inputs, runtime, parent)); plan = verify(inputs, digest)
    P.need(E.tree(runtime) == plan['runtime'] and parent.is_dir() and (not require_fresh or not (parent / OUTPUT).exists()), 'In-core runtime/output differs')
    command = ['docker', 'run', '--name', CONTAINER, '--rm', '--pull', 'never', '--network', 'none', '--read-only',
        '--cpus', '1', '--memory', '6g', '--memory-swap', '6g', '--pids-limit', '128', '--tmpfs', '/tmp:rw,nosuid,noexec,size=536870912',
        '--mount', f'type=bind,src={Path(__file__).resolve().parent},dst=/rc-source,readonly',
        '--mount', f'type=bind,src={inputs},dst=/rc-inputs,readonly', '--mount', f'type=bind,src={runtime},dst=/solver/runtime,readonly',
        '--mount', f'type=bind,src={parent},dst=/rc-output-parent',
        '--entrypoint', '/nix/store/lqn6mbgzzdrqq2qkwddcmxj9z6amdd86-python3-3.13.13/bin/python3', W.C.D.IMAGE,
        '-I', '-B', '/rc-source/streaming_8x4_rc_incore.py', 'run', '--inputs', '/rc-inputs', '--plan-sha256', digest,
        '--runtime', '/solver/runtime', '--output', '/rc-output-parent/' + OUTPUT]
    return {'schema': 'pinwheel.streaming-8x4-rc-incore-command-proposal.v1', 'root_go_required': True, 'admitted': False,
        'native_executed': False, 'model_qualified': False, 'full_pilot_passed': False, 'qualified_timing': False,
        'plan_path': str(inputs / 'plan.json'), 'plan_sha256': digest, 'runtime_path': str(runtime),
        'timeout_seconds': 330, 'policy': policy(), 'container_name': CONTAINER, 'producer_sha256': sources(), 'argv': command}


def cgroup_snapshot(root=Path('/sys/fs/cgroup')):
    result = {n.replace('.', '_'): (root / n).read_text().strip() for n in policy()['capture']}
    for n in ('memory_current', 'memory_peak', 'memory_max', 'memory_swap_max'):
        P.need(result[n].isdigit(), 'Unsupported cgroup numeric field: ' + n); result[n] = int(result[n])
    P.need(0 < result['memory_max'] <= 6442450944 and result['memory_swap_max'] == 0, 'Actual in-core cgroup memory/swap differs')
    for n in ('memory_events', 'memory_events_local'):
        pairs = [line.split() for line in result[n].splitlines()]
        P.need(all(len(r) == 2 and r[1].isdigit() for r in pairs) and len({r[0] for r in pairs}) == len(pairs), 'Unsupported cgroup event grammar')
        result[n] = {k: int(v) for k, v in pairs}
        P.need({'max', 'oom', 'oom_kill'} <= set(result[n]), 'Actual cgroup lacks required max/OOM counters')
    return result


def counters(before, after):
    result = {}
    for n in ('memory_events', 'memory_events_local'):
        P.need({'max', 'oom', 'oom_kill'} <= set(before[n]) == set(after[n]) and all(after[n][k] >= before[n][k] for k in before[n]), 'Cgroup event counters missing/reset/change membership')
        result[n] = {k: after[n][k] - v for k, v in before[n].items()}
    return result


def mode_observed(raw):
    values = re.findall(r'^Out-of-core free memory to link memory condition \(-f\):\s*(\S+)\s*$', raw, re.M)
    try: zero = len(values) == 1 and P.number(values[0]) == 0
    except (ValueError, TypeError): zero = False
    return zero and 'Going out-of-core' not in raw and 'Out-of-core temporary files folder:' not in raw


def parse(raw, inputs, index):
    P.need(mode_observed(raw), 'Actual Native -f0 mode missing/different/duplicated or OOC observed')
    old, case = original(inputs, index)
    return X.parse(raw, old, case, FIXED[index]['mesh'])


def resource_feasible(row):
    delta = counters(row['cgroup_before'], row['cgroup_after'])
    oom = any(v for name, values in delta.items() for k, v in values.items() if k.startswith('oom'))
    return row['exit_code'] == 0 and not row['timed_out'] and row['memory_guard_triggered'] is False and not oom and row['actual_f0_observed'] is True and row['cgroup_after']['memory_peak'] < row['cgroup_after']['memory_max'] * 95 // 100 and all(values['max'] == 0 for values in delta.values())


def guard_reason(current, limit, elapsed):
    if current >= limit * 95 // 100: return 'memory'
    return 'timeout' if elapsed >= 120 else None


def leaf(inputs, digest, plan, index, runtime, output):
    P.need(str(runtime) == '/solver/runtime' and E.tree(runtime) == plan['runtime'] and not output.exists(), 'In-core leaf/runtime owner differs')
    output.mkdir(); work = output / 'work'; work.mkdir(); case = plan['cases'][index]
    for n, info in case['files'].items():
        P.need(Path(n).name == n and info['kind'] == 'file', 'Only flat in-core geometry admitted')
        shutil.copyfile(inputs / ('original-' + str(index)) / 'failed/work' / n, work / n); (work / n).chmod(0o444)
    row = {'schema': 'pinwheel.streaming-8x4-rc-incore-native-leaf.v1', 'plan_sha256': digest, 'leaf_index': index,
        'qualified': False, 'model_qualified': False, 'full_pilot_passed': False, 'qualified_timing': False,
        'argv': argv(inputs, index), 'environment': W.C.ENVIRONMENT, 'timeout_seconds': 120,
        'cgroups': E.verify_cgroups(), 'cgroup_before': cgroup_snapshot(), 'memory_guard_triggered': False,
        'memory_poll_seconds': '0.25', 'solver_executed': False, 'exit_code': None, 'timed_out': False,
        'process_tree_reaped': False, 'numeric': None, 'numeric_passed': False, 'passed': False}
    child = None; started = time.monotonic(); raw = ''; peak_poll = row['cgroup_before']['memory_current']
    try:
        with (output / 'native.log').open('xb') as stream:
            child = subprocess.Popen(row['argv'], cwd=work, env=dict(W.C.ENVIRONMENT), stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            row['solver_executed'] = True
            while child.poll() is None:
                current = int(Path('/sys/fs/cgroup/memory.current').read_text()); peak_poll = max(peak_poll, current)
                reason = guard_reason(current, row['cgroup_before']['memory_max'], time.monotonic() - started)
                if reason is not None:
                    row['memory_guard_triggered'] = reason == 'memory'
                    row['timed_out'] = not row['memory_guard_triggered']; os.killpg(child.pid, signal.SIGTERM)
                    try: child.wait(timeout=2)
                    except subprocess.TimeoutExpired: os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
                    break
                try: child.wait(timeout=min(.25, max(.001, 120 - (time.monotonic() - started))))
                except subprocess.TimeoutExpired: pass
            row['exit_code'] = child.returncode
        try: os.killpg(child.pid, 0)
        except ProcessLookupError: row['process_tree_reaped'] = True
        else: os.killpg(child.pid, signal.SIGKILL); raise ValueError('In-core child group remains live')
        raw = (output / 'native.log').read_text()
        P.need(row['exit_code'] == 0 and not row['timed_out'] and not row['memory_guard_triggered'], 'In-core solver exit/timeout/memory guard failed')
        row['numeric'] = parse(raw, inputs, index); row['numeric_passed'] = True
    except BaseException as error: row['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if child is not None and child.poll() is None: os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
        row['cgroup_after'] = cgroup_snapshot(); row['cgroup_counter_deltas'] = counters(row['cgroup_before'], row['cgroup_after'])
        row['peak_scope'] = policy()['peak_scope']; row['maximum_polled_memory_current'] = peak_poll
        row['copied_inputs_unchanged'] = E.tree(work) == case['files']
        row['source_runtime_unchanged'] = E.tree(runtime) == plan['runtime']
        row['producer_plan_unchanged'] = verify(inputs, digest) == plan
        raw = (output / 'native.log').read_text() if (output / 'native.log').exists() else raw
        row['actual_f0_observed'] = mode_observed(raw); row['log_sha256'] = E.sha(output / 'native.log') if (output / 'native.log').exists() else None
        row['resource_feasible'] = resource_feasible(row); row['observations'] = X.O.observations(raw, case['matrix_names'])
        row['wall_seconds'] = time.monotonic() - started; row['passed'] = row['numeric_passed'] and row['resource_feasible']
        W.write(output / 'report.json', row)
    return row


def run(inputs, digest, runtime, output):
    plan = verify(inputs, digest); P.need(output.name == OUTPUT and not output.exists() and output.parent.is_dir(), 'Fresh in-core output owner required')
    output.mkdir(); jobs = []; started = time.monotonic(); closed_count = 0
    report = {'schema': 'pinwheel.streaming-8x4-rc-incore-execution.v1', 'plan_sha256': digest, 'policy': policy(),
        'qualified': False, 'model_qualified': False, 'full_pilot_passed': False, 'qualified_timing': False,
        'measurement_packet_completed': False, 'resource_feasible': False, 'numeric_passed': False, 'passed': False, 'jobs': jobs}
    try:
        for index in range(2):
            P.need(time.monotonic() - started <= 140, 'Insufficient in-core next-leaf/cleanup allowance')
            owner = output / ('job-' + str(index).zfill(3)); result = leaf(inputs, digest, plan, index, runtime, owner)
            jobs.append({'leaf_index': index, 'report_sha256': E.sha(owner / 'report.json'), 'resource_feasible': result['resource_feasible'], 'numeric_passed': result['numeric_passed']})
            X.closed(result); closed_count += 1
            P.need(result['resource_feasible'] is True, 'In-core resource failure; later suffix not executed')
    except BaseException as error: report['error'] = type(error).__name__ + ': ' + str(error)
    report['inputs_runtime_unchanged'] = verify(inputs, digest) == plan and E.tree(runtime) == plan['runtime']
    report['measurement_packet_completed'] = len(jobs) == closed_count == 2
    report['resource_feasible'] = report['measurement_packet_completed'] and all(r['resource_feasible'] is True for r in jobs)
    report['numeric_passed'] = report['measurement_packet_completed'] and all(r['numeric_passed'] is True for r in jobs)
    report['passed'] = report['resource_feasible'] and report['numeric_passed'] and report['inputs_runtime_unchanged']
    report['wall_seconds'] = time.monotonic() - started; W.write(output / 'report.json', report); return report


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare')
    for n in ('campaign', 'runtime', 'output'): q.add_argument('--' + n, type=Path, required=True)
    for action in ('verify', 'proposal', 'run'):
        q = sub.add_parser(action); q.add_argument('--inputs', type=Path, required=True); q.add_argument('--plan-sha256', required=True)
        if action != 'verify': q.add_argument('--runtime', type=Path, required=True); q.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if a.action == 'prepare':
        prepare(a.campaign, a.runtime, a.output); result = {'plan_sha256': E.sha(a.output / 'plan.json'), 'native_executed': False}
    elif a.action == 'verify': result = {'verified': bool(verify(a.inputs, a.plan_sha256)), 'native_executed': False}
    elif a.action == 'proposal': result = proposal(a.inputs, a.plan_sha256, a.runtime, a.output.parent); W.write(a.output, result)
    else: result = run(a.inputs, a.plan_sha256, a.runtime, a.output)
    print(json.dumps(result, indent=2)); return 2 if a.action == 'run' and not result['passed'] else 0


if __name__ == '__main__': raise SystemExit(main())
