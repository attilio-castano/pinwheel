"""Fresh55 Native worker, original numerical parser plus reviewed-f0 guard."""
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
import streaming_8x4_rc_uniform_incore as W

G, X, P, E = W.G, W.X, W.P, W.E
verify, policy = W.verify, W.policy
cgroup_snapshot, counters, guard_reason = G.cgroup_snapshot, G.counters, G.guard_reason
mode_observed, resource_feasible = G.mode_observed, G.resource_feasible


def native_limits():
    row = E.verify_cgroups()
    P.need(0 < int(row['pids_max']) <= 128, 'Uniform in-core PID ceiling differs')
    return row


def parse(raw, plan, case, mesh):
    P.need(mode_observed(raw), 'Actual Native-f0 mode missing/different/duplicated or OOC observed')
    return X.parse(raw, plan['original_uniform_plan'], case, mesh)


def leaf(inputs, digest, plan, job, runtime, output):
    P.need(str(runtime) == '/solver/runtime' and E.tree(runtime) == plan['runtime'] and not output.exists(), 'In-core leaf/runtime owner differs')
    output.mkdir(); work = output / 'work'; work.mkdir(); case = next(c for c in plan['cases'] if c['name'] == job['case'])
    for n, info in case['files'].items():
        P.need(Path(n).name == n and info['kind'] == 'file', 'Only flat in-core geometry admitted')
        shutil.copyfile(W.geometry(inputs, case) / n, work / n); (work / n).chmod(0o444)
    row = {'schema': 'pinwheel.streaming-8x4-rc-uniform-incore-full-native-leaf.v1', 'plan_sha256': digest, 'case': job['case'], 'mesh': job['mesh'],
        'qualified': False, 'model_qualified': False, 'full_pilot_passed': False, 'qualified_timing': False,
        'argv': W.solver_argv(plan, job['mesh']), 'environment': W.C.ENVIRONMENT, 'timeout_seconds': 120,
        'cgroups': native_limits(), 'cgroup_before': cgroup_snapshot(), 'memory_guard_triggered': False,
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
        row['numeric'] = parse(raw, plan, case, job['mesh']); row['numeric_passed'] = True
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
    plan = verify(inputs, digest); expected = W.jobs(plan)
    P.need(str(runtime) == '/solver/runtime' and E.tree(runtime) == plan['runtime'] and output.name == W.OUTPUT
        and not output.exists() and output.parent.is_dir(), 'Fresh full55 owner/exact runtime required')
    native_limits(); output.mkdir(); jobs = []; started = time.monotonic(); closed_count = 0
    report = dict(schema='pinwheel.streaming-8x4-rc-uniform-incore-full-execution.v1', plan_sha256=digest, policy=policy(),
        qualified=False, model_qualified=False, qualified_timing=False, limited_pilot_passed=False,
        measurement_packet_completed=False, resource_feasible=False, numeric_passed=False, passed=False, jobs=jobs)
    try:
        for index, job in enumerate(expected):
            P.need(time.monotonic() - started <= 1670, 'Insufficient130s full55 next-leaf/closeout allowance')
            owner = output / ('job-' + str(index).zfill(3))
            result = leaf(inputs, digest, plan, job, runtime, owner)
            jobs.append(dict(job, report_sha256=E.sha(owner / 'report.json'), resource_feasible=result['resource_feasible'], numeric_passed=result['numeric_passed']))
            X.closed(result); closed_count += 1
            P.need(time.monotonic() - started <= 1800, 'Full55 work budget exceeded')
            P.need(result['resource_feasible'] is True, 'Full55 resource failure; later suffix not executed')
            P.need(result['numeric_passed'] is True, 'Full55 numeric failure; later suffix not executed')
    except BaseException as error: report['error'] = type(error).__name__ + ': ' + str(error)
    report['work_wall_seconds'] = time.monotonic() - started
    report['work_budget_satisfied'] = report['work_wall_seconds'] <= 1800
    report['inputs_runtime_unchanged'] = verify(inputs, digest) == plan and E.tree(runtime) == plan['runtime']
    report['measurement_packet_completed'] = len(jobs) == closed_count == len(expected) == 55
    report['resource_feasible'] = report['measurement_packet_completed'] and report['work_budget_satisfied'] and all(j['resource_feasible'] is True for j in jobs)
    report['numeric_passed'] = report['measurement_packet_completed'] and all(j['numeric_passed'] is True for j in jobs)
    report['passed'] = report['resource_feasible'] and report['numeric_passed'] and report['inputs_runtime_unchanged']
    report['wall_seconds'] = time.monotonic() - started; W.write(output / 'report.json', report); return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for n in ('inputs', 'runtime', 'output'): p.add_argument('--' + n, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    result = run(a.inputs, a.plan_sha256, a.runtime, a.output)
    print(json.dumps({k: result[k] for k in ('measurement_packet_completed', 'resource_feasible', 'numeric_passed', 'limited_pilot_passed')}, indent=2))
    return 0 if result['passed'] else 2


if __name__ == '__main__': raise SystemExit(main())
