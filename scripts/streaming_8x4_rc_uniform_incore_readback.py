"""Independent full55 -f0 raw/resource/reference gates; failed prefixes stay failed."""
import argparse
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_uniform_incore as W
import streaming_8x4_rc_uniform_incore_execute as X

P, E = W.P, W.E
validate_poll_peak = W.GR.validate_poll_peak


def bound(path):
    P.need(path.is_file() and not path.is_symlink(), 'Missing/aliased uniform in-core evidence')
    return dict(path=str(path.resolve()), sha256=E.sha(path))


def leaf(inputs, digest, plan, job, owner):
    row = json.loads((owner / 'report.json').read_text()); W.X.closed(row); case = next(c for c in plan['cases'] if c['name'] == job['case'])
    raw = (owner / 'native.log').read_text(); before = row['cgroup_before']; after = row['cgroup_after']
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-uniform-incore-full-native-leaf.v1' and row['plan_sha256'] == digest
        and row['case'] == job['case'] and row['mesh'] == job['mesh'] and row['argv'] == W.solver_argv(plan, job['mesh']) and row['environment'] == W.W.C.ENVIRONMENT
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'full_pilot_passed', 'qualified_timing'))
        and row['timeout_seconds'] == 120 and row['memory_poll_seconds'] == '0.25'
        and row['peak_scope'] == W.policy()['peak_scope'] and E.sha(owner / 'native.log') == row['log_sha256']
        and E.tree(owner / 'work') == case['files'] and row['actual_f0_observed'] is W.G.mode_observed(raw),
        'In-core exact leaf mode/authority/raw geometry differs')
    for snapshot in (before, after):
        P.need(all(type(snapshot[n]) is int and snapshot[n] >= 0 for n in ('memory_current', 'memory_peak', 'memory_max', 'memory_swap_max'))
            and 0 < snapshot['memory_max'] <= 6442450944 and snapshot['memory_swap_max'] == 0
            and snapshot['memory_peak'] >= snapshot['memory_current']
            and all({'max', 'oom', 'oom_kill'} <= set(snapshot[n]) for n in ('memory_events', 'memory_events_local'))
            and all(type(v) is int and v >= 0 for n in ('memory_events', 'memory_events_local') for v in snapshot[n].values()),
            'In-core actual cgroup snapshot differs')
    P.need(before['memory_max'] == after['memory_max'] and row['cgroup_counter_deltas'] == W.G.counters(before, after)
        and after['memory_peak'] >= before['memory_peak']
        and type(row['maximum_polled_memory_current']) is int and row['maximum_polled_memory_current'] >= before['memory_current']
        and row['resource_feasible'] is W.G.resource_feasible(row), 'In-core cgroup counter/peak/resource assessment differs')
    validate_poll_peak(row)
    c = row['cgroups']; cpu = c['cpu_max'].split()
    P.need(c['memory_max'] == str(before['memory_max']) and c['memory_swap_max'] == '0'
        and len(cpu) == 2 and all(x.isdigit() for x in cpu) and 0 < int(cpu[0]) <= int(cpu[1])
        and c['pids_max'].isdigit() and 0 < int(c['pids_max']) <= 128, 'Actual in-core cgroup CPU/PID ceiling differs')
    numeric = None; passed = False; error = None
    try:
        P.need(row['exit_code'] == 0 and not row['timed_out'] and not row['memory_guard_triggered'], 'In-core solver exit/timeout/memory guard failed')
        numeric = X.parse(raw, plan, case, job['mesh']); passed = True
    except (ValueError, KeyError, TypeError) as failure: error = type(failure).__name__ + ': ' + str(failure)
    P.need(row['numeric_passed'] is passed and row['numeric'] == numeric and (error is None or row['error'] == error)
        and row['passed'] is (passed and row['resource_feasible'])
        and row['observations'] == W.X.O.observations(raw, case['matrix_names']), 'Independent in-core numeric/error evidence differs')
    deltas = row['cgroup_counter_deltas']; oom = any(v for n in deltas for k, v in deltas[n].items() if k.startswith('oom'))
    return {'case': job['case'], 'mesh': job['mesh'], 'report_sha256': E.sha(owner / 'report.json'), 'log_sha256': E.sha(owner / 'native.log'),
        'numeric_passed': passed, 'resource_feasible': row['resource_feasible'], 'error': error,
        'exit_code': row['exit_code'], 'timed_out': row['timed_out'], 'memory_guard_triggered': row['memory_guard_triggered'],
        'cgroup_oom_observed': bool(oom), 'child_SIGKILL_observed': row['exit_code'] == -9,
        'cgroup_before': before, 'cgroup_after': after, 'cgroup_counter_deltas': deltas,
        'actual_f0_observed': row['actual_f0_observed'], 'numeric': numeric, 'observations': row['observations']}


def raw_readback(inputs, digest, directory, plan):
    report = json.loads((directory / 'report.json').read_text()); jobs = report['jobs']; expected = W.jobs(plan)
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-uniform-incore-full-execution.v1' and report['plan_sha256'] == digest
        and report['policy'] == W.policy() and all(report[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing', 'limited_pilot_passed'))
        and report['inputs_runtime_unchanged'] is True and type(report['passed']) is bool and len(jobs) <= 55
        and [{k: j[k] for k in ('case', 'mesh')} for j in jobs] == expected[:len(jobs)]
        and {p.name for p in directory.iterdir()} == {'report.json'} | {'job-' + str(i).zfill(3) for i in range(len(jobs))},
        'Uniform in-core exact ordered complete/prefix authority differs')
    rows = []
    for i, job in enumerate(jobs):
        owner = directory / ('job-' + str(i).zfill(3))
        P.need({p.name for p in owner.iterdir()} == {'report.json', 'native.log', 'work'}
            and E.sha(owner / 'report.json') == job['report_sha256'], 'Uniform in-core exact leaf membership/seal differs')
        row = leaf(inputs, digest, plan, job, owner)
        P.need(all(row[k] == job[k] for k in ('resource_feasible', 'numeric_passed')), 'Uniform in-core job status differs')
        rows.append(row)
    P.need(all(r['resource_feasible'] is True and r['numeric_passed'] is True for r in rows[:-1]),
        'Uniform in-core continued after a failed leaf')
    work = report['work_wall_seconds']; wall = report['wall_seconds']
    P.need(type(work) in (int, float) and type(wall) in (int, float) and math.isfinite(work) and math.isfinite(wall)
        and 0 <= work <= wall and report['work_budget_satisfied'] is (work <= 1800), 'Uniform work/outer observation differs')
    complete = len(rows) == 55
    feasible = complete and report['work_budget_satisfied'] and all(r['resource_feasible'] is True for r in rows)
    numeric = complete and all(r['numeric_passed'] is True for r in rows)
    P.need(report['measurement_packet_completed'] is complete and report['resource_feasible'] is feasible
        and report['numeric_passed'] is numeric and report['passed'] is (feasible and numeric), 'Uniform full55 resource/numeric aggregate differs')
    analysis = dict(passed=False, error='Incomplete or failed strict full55 raw/resource universe')
    if feasible and numeric:
        mathematics = [dict(case=r['case'], mesh=r['mesh'], passed=True, numeric=r['numeric']) for r in rows]
        try: analysis = W.F.mathematical_analysis(plan['original_uniform_plan'], mathematics)
        except (ValueError, KeyError, TypeError) as failure: analysis = dict(passed=False, error=type(failure).__name__ + ': ' + str(failure))
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-incore-full-raw-readback.v1', measurement_packet_completed=complete,
        resource_feasible=feasible, numeric_passed=numeric, analysis=analysis, leaves=rows, execution_report=bound(directory / 'report.json'))


def readback(inputs, digest, directory, runtime, resource_path, proposal_path):
    plan = W.verify(inputs, digest); proposal = json.loads(proposal_path.read_text())
    P.need(proposal == W.proposal(inputs, digest, runtime, directory.parent, require_fresh=False) and directory.name == W.OUTPUT,
        'Uniform in-core exact new command/output differs')
    report = json.loads((directory / 'report.json').read_text())
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-uniform-incore-full-execution.v1'
        and report['plan_sha256'] == digest and type(report['passed']) is bool and report['model_qualified'] is False,
        'Uniform in-core worker scope differs')
    resource = W.F.resource_join(resource_path, proposal_path, proposal, plan, report)
    try: raw = raw_readback(inputs, digest, directory, plan)
    except (ValueError, KeyError, TypeError, OSError) as error:
        raw = dict(schema='pinwheel.streaming-8x4-rc-uniform-incore-full-raw-failure.v1', measurement_packet_completed=False,
            resource_feasible=False, numeric_passed=False, analysis=dict(passed=False, error=type(error).__name__ + ': ' + str(error)),
            execution_report=bound(directory / 'report.json'))
    W.verify(inputs, digest); P.need(E.tree(runtime) == plan['runtime'], 'Uniform in-core runtime changed during HOST readback')
    passed = raw['resource_feasible'] and raw['numeric_passed'] and raw['analysis']['passed'] is True and resource['status'] == 'completed'
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-incore-full-independent-readback.v1',
        qualified=False, model_qualified=False, qualified_timing=False, continuum_error_enclosure=False,
        limited_uniform_finite_wire_pilot_passed=passed, limited_layered_M1_pilot_passed=False,
        measurement_packet_completed=raw['measurement_packet_completed'], resource_feasible=raw['resource_feasible'], numeric_passed=raw['numeric_passed'],
        new_policy_plan=bound(inputs / 'plan.json'), original_uniform_plan_sha256=W.UNIFORM,
        original_probe_intake=plan['source_probe_intake'], native_report=bound(directory / 'report.json'),
        runtime_path=str(runtime.resolve()), command_proposal=bound(proposal_path), resource_cleanup_join=resource,
        raw_readback=raw, native_executed_by_readback=False, scope=W.policy()['scope'])


def closed_authority(path):
    row = json.loads(path.read_text())
    for pin in (row['new_policy_plan'], row['native_report'], row['command_proposal'], row['resource_cleanup_join']['resource_report']):
        P.need(E.sha(Path(pin['path'])) == pin['sha256'], 'Uniform in-core authority dependency changed')
    result = readback(Path(row['new_policy_plan']['path']).parent, row['new_policy_plan']['sha256'],
        Path(row['native_report']['path']).parent, Path(row['runtime_path']),
        Path(row['resource_cleanup_join']['resource_report']['path']), Path(row['command_proposal']['path']))
    P.need(row == result and row['limited_uniform_finite_wire_pilot_passed'] is True, 'Incomplete/failed/foreign uniform authority cannot be promoted')
    return row


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for n in ('inputs', 'directory', 'runtime', 'resource-report', 'command-proposal', 'output'): p.add_argument('--' + n, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    result = readback(a.inputs, a.plan_sha256, a.directory, a.runtime, a.resource_report, a.command_proposal)
    W.write(a.output, result)
    print(json.dumps({k: result[k] for k in ('measurement_packet_completed', 'resource_feasible', 'numeric_passed', 'limited_uniform_finite_wire_pilot_passed', 'model_qualified')}, indent=2))
    return 0 if result['limited_uniform_finite_wire_pilot_passed'] else 2


if __name__ == '__main__': raise SystemExit(main())
