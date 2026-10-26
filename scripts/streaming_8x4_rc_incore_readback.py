"""Independent HOST raw/header/cgroup/resource readback of two -f0 leaves."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_incore as W
P, E = W.P, W.E


def validate_poll_peak(row):
    value = row['maximum_polled_memory_current']; after = row['cgroup_after']
    P.need(type(value) is int and row['cgroup_before']['memory_current'] <= value <= after['memory_peak']
        and (row['resource_feasible'] is False or value < after['memory_max'] * 95 // 100),
        'In-core polled memory differs from actual cumulative cgroup peak/guard')


def leaf(inputs, digest, index, owner):
    row = json.loads((owner / 'report.json').read_text()); W.X.closed(row); old, case = W.original(inputs, index)
    raw = (owner / 'native.log').read_text(); before = row['cgroup_before']; after = row['cgroup_after']
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-incore-native-leaf.v1' and row['plan_sha256'] == digest
        and row['leaf_index'] == index and row['argv'] == W.argv(inputs, index) and row['environment'] == W.W.C.ENVIRONMENT
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'full_pilot_passed', 'qualified_timing'))
        and row['timeout_seconds'] == 120 and row['memory_poll_seconds'] == '0.25'
        and row['peak_scope'] == W.policy()['peak_scope'] and E.sha(owner / 'native.log') == row['log_sha256']
        and E.tree(owner / 'work') == case['files'] and row['actual_f0_observed'] is W.mode_observed(raw),
        'In-core exact leaf mode/authority/raw geometry differs')
    for snapshot in (before, after):
        P.need(all(type(snapshot[n]) is int and snapshot[n] >= 0 for n in ('memory_current', 'memory_peak', 'memory_max', 'memory_swap_max'))
            and 0 < snapshot['memory_max'] <= 6442450944 and snapshot['memory_swap_max'] == 0
            and snapshot['memory_peak'] >= snapshot['memory_current']
            and all({'max', 'oom', 'oom_kill'} <= set(snapshot[n]) for n in ('memory_events', 'memory_events_local'))
            and all(type(v) is int and v >= 0 for n in ('memory_events', 'memory_events_local') for v in snapshot[n].values()),
            'In-core actual cgroup snapshot differs')
    P.need(before['memory_max'] == after['memory_max'] and row['cgroup_counter_deltas'] == W.counters(before, after)
        and after['memory_peak'] >= before['memory_peak']
        and type(row['maximum_polled_memory_current']) is int and row['maximum_polled_memory_current'] >= before['memory_current']
        and row['resource_feasible'] is W.resource_feasible(row), 'In-core cgroup counter/peak/resource assessment differs')
    validate_poll_peak(row)
    c = row['cgroups']; cpu = c['cpu_max'].split()
    P.need(c['memory_max'] == str(before['memory_max']) and c['memory_swap_max'] == '0'
        and len(cpu) == 2 and all(x.isdigit() for x in cpu) and 0 < int(cpu[0]) <= int(cpu[1])
        and c['pids_max'].isdigit() and 0 < int(c['pids_max']) <= 128, 'Actual in-core cgroup CPU/PID ceiling differs')
    numeric = None; passed = False; error = None
    try:
        P.need(row['exit_code'] == 0 and not row['timed_out'] and not row['memory_guard_triggered'], 'In-core solver exit/timeout/memory guard failed')
        numeric = W.parse(raw, inputs, index); passed = True
    except (ValueError, KeyError, TypeError) as failure: error = type(failure).__name__ + ': ' + str(failure)
    P.need(row['numeric_passed'] is passed and row['numeric'] == numeric and (error is None or row['error'] == error)
        and row['passed'] is (passed and row['resource_feasible'])
        and row['observations'] == W.X.O.observations(raw, case['matrix_names']), 'Independent in-core numeric/error evidence differs')
    deltas = row['cgroup_counter_deltas']; oom = any(v for n in deltas for k, v in deltas[n].items() if k.startswith('oom'))
    return {'leaf_index': index, 'report_sha256': E.sha(owner / 'report.json'), 'log_sha256': E.sha(owner / 'native.log'),
        'numeric_passed': passed, 'resource_feasible': row['resource_feasible'], 'error': error,
        'exit_code': row['exit_code'], 'timed_out': row['timed_out'], 'memory_guard_triggered': row['memory_guard_triggered'],
        'cgroup_oom_observed': bool(oom), 'child_SIGKILL_observed': row['exit_code'] == -9,
        'cgroup_before': before, 'cgroup_after': after, 'cgroup_counter_deltas': deltas,
        'actual_f0_observed': row['actual_f0_observed'], 'numeric': numeric, 'observations': row['observations']}


def readback(inputs, digest, directory, runtime, resource_path, proposal_path):
    plan = W.verify(inputs, digest); proposal = json.loads(proposal_path.read_text())
    P.need(proposal == W.proposal(inputs, digest, runtime, directory.parent, require_fresh=False) and directory.name == W.OUTPUT,
           'In-core exact new command/output differs')
    report = json.loads((directory / 'report.json').read_text()); jobs = report['jobs']
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-incore-execution.v1' and report['plan_sha256'] == digest
        and report['policy'] == W.policy() and all(report[k] is False for k in ('qualified', 'model_qualified', 'full_pilot_passed', 'qualified_timing'))
        and report['inputs_runtime_unchanged'] is True and len(jobs) <= 2 and [j['leaf_index'] for j in jobs] == list(range(len(jobs)))
        and {p.name for p in directory.iterdir()} == {'report.json'} | {'job-' + str(i).zfill(3) for i in range(len(jobs))},
        'In-core actual complete/prefix membership/scope differs')
    rows = []
    for i, job in enumerate(jobs):
        owner = directory / ('job-' + str(i).zfill(3))
        P.need({p.name for p in owner.iterdir()} == {'report.json', 'native.log', 'work'}
            and E.sha(owner / 'report.json') == job['report_sha256'], 'In-core exact leaf membership/seal differs')
        row = leaf(inputs, digest, i, owner)
        P.need(all(row[k] == job[k] for k in ('resource_feasible', 'numeric_passed')), 'In-core job status differs'); rows.append(row)
    complete = len(rows) == 2; feasible = complete and all(r['resource_feasible'] for r in rows); numeric = complete and all(r['numeric_passed'] for r in rows)
    P.need(report['measurement_packet_completed'] is complete and report['resource_feasible'] is feasible
        and report['numeric_passed'] is numeric and report['passed'] is (feasible and numeric), 'In-core resource/numeric aggregate differs')
    # The generic outer schema/command/source/lease checks are unchanged; the
    # selected plan and report passed here are the actual new in-core objects.
    resource = W.F.resource_join(resource_path, proposal_path, proposal, plan, report)
    W.verify(inputs, digest); P.need(E.tree(runtime) == plan['runtime'], 'In-core runtime changed during HOST readback')
    return {'schema': 'pinwheel.streaming-8x4-rc-incore-independent-readback.v1', 'plan_sha256': digest,
        'qualified': False, 'model_qualified': False, 'full_pilot_passed': False, 'qualified_timing': False,
        'measurement_packet_completed': complete, 'resource_feasible': feasible, 'numeric_passed': numeric,
        'execution_report_sha256': E.sha(directory / 'report.json'), 'resource_cleanup_join': resource, 'leaves': rows,
        'native_executed_by_readback': False, 'scope': W.policy()['scope']}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for n in ('inputs', 'directory', 'runtime', 'resource-report', 'command-proposal', 'output'): p.add_argument('--' + n, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    result = readback(a.inputs, a.plan_sha256, a.directory, a.runtime, a.resource_report, a.command_proposal)
    W.W.write(a.output, result); print(json.dumps({k: result[k] for k in ('measurement_packet_completed', 'resource_feasible', 'numeric_passed', 'model_qualified')}, indent=2))
    return 0 if result['resource_feasible'] and result['numeric_passed'] else 2


if __name__ == '__main__': raise SystemExit(main())
