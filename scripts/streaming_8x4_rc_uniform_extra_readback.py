"""Independent fixed extra-fine point readback; original55 failure stays false."""
import argparse
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_uniform_extra as X
import streaming_8x4_rc_ooc_readback as CR
P, E = X.P, X.E


def leaf(inputs, digest, plan, stage, owner):
    row = json.loads((owner / 'report.json').read_text()); raw = (owner / 'native.log').read_text()
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-uniform-extra-leaf.v1'
        and row['plan_sha256'] == digest and row['stage'] == stage and row['argv'] == X.solver_argv(plan, stage)
        and row['environment'] == X.environment(stage) and row['timeout_seconds'] == 120
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing', 'full55_limited_pilot_passed'))
        and row['inputs_runtime_unchanged'] is True and row['log_sha256'] == E.sha(owner / 'native.log')
        and row['meminfo_sha256'] == E.sha(owner / 'meminfo.txt') and E.tree(owner / 'work') == plan['case']['files']
        and {p.name for p in owner.iterdir()} == {'report.json', 'native.log', 'meminfo.txt', 'work'}
        and math.isfinite(row['wall_seconds']) and 0 <= row['wall_seconds'] < 130,
        'Extra-point actual leaf/raw/source/geometry/budget differs')
    X.C.memtotal((owner / 'meminfo.txt').read_text())
    for name in ('cgroup_before', 'cgroup_after'): CR.validate_snapshot(row[name])
    CR.validate_cleanup(row)
    P.need(row['resource_feasible'] is X.resource_pass(row), 'Extra-point resource feasibility differs')
    c = row['cgroups']; cpu = c['cpu_max'].split()
    P.need(c['memory_max'] == str(row['cgroup_before']['memory_max']) and c['memory_swap_max'] == '0'
        and len(cpu) == 2 and all(v.isdigit() for v in cpu) and 0 < int(cpu[0]) <= int(cpu[1])
        and c['pids_max'].isdigit() and 0 < int(c['pids_max']) <= 128, 'Extra-point CPU/PID/cgroup policy differs')
    count = None; numeric = None; expected = False; passed = False; error = None
    try:
        if stage == 'count97':
            P.need(row['exit_code'] == 97, 'Extra count probe expected97 exit missing'); count = X.parse_count(raw); expected = True
        else:
            P.need(row['exit_code'] == 0, 'Extra-fine solve exit failure'); X.header(raw, '0')
            P.need(X.U.G.mode_observed(raw), 'Extra-fine actual f0 mode differs')
            count = X.C.counts(raw); numeric = X.U.X.parse(raw, dict(policy=plan['original_solver_policy']), plan['case'], X.MESH); passed = True
    except (ValueError, KeyError, TypeError) as failure: error = type(failure).__name__ + ': ' + str(failure)
    P.need(row['counts'] == count and row['numeric'] == numeric and row['expected_count97_observed'] is expected
        and row['numerical_passed'] is passed and (error is None or row['error'] == error),
        'Extra-point independently parsed numeric/expected-count/error differs')
    return row


def resource_join(path, proposal_path, proposal, plan, report):
    result = X.U.F.resource_join(path, proposal_path, proposal, plan, report)
    resource = json.loads(path.read_text()); owner = Path(plan['scratch_host_path']) / 'owner.json'
    P.need(resource['campaign_boundary']['shared_lease'] == dict(heavy_lock=str(X.ROOT / 'build/streaming-tt-resources/heavy.lock'),
        cleanup_sentinel=str(X.ROOT / 'build/streaming-tt-resources/cleanup-unconfirmed.json'))
        and resource['input_sha256'][str(owner)] == proposal['scratch_owner_sha256'] == E.sha(owner),
        'Extra-point full shared lease/scratch-owner input seal differs')
    return result


def continuity(prior, new):
    old_change = P.cellwise_change(prior[0]['numeric'], prior[1]['numeric'])
    new_change = P.cellwise_change(prior[1]['numeric'], new['numeric'])
    return dict(prior_final_pair_change=str(old_change), new_finer_pair_change=str(new_change),
        both_consecutive_pairs_at_most_two_percent=old_change <= P.number('.02') and new_change <= P.number('.02'),
        old55_limited_pilot_passed=False, new_extended_universe_authority=False,
        scope='Fixed geometry continuity observation only; old55 five-level failure is preserved')


def readback(inputs, digest, directory, runtime, resource_path, proposal_path):
    plan = X.verify(inputs, digest); proposal = json.loads(proposal_path.read_text())
    P.need(proposal == X.proposal(inputs, digest, runtime, directory.parent, require_fresh=False) and directory.name == X.OUTPUT,
        'Extra-point exact command/source/runtime/output differs')
    report = json.loads((directory / 'report.json').read_text()); jobs = report['jobs']
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-uniform-extra-execution.v1' and report['plan_sha256'] == digest
        and report['policy'] == X.policy() and report['inputs_runtime_unchanged'] is True
        and all(report[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing', 'full55_limited_pilot_passed'))
        and len(jobs) <= 2 and [j['stage'] for j in jobs] == X.STAGES[:len(jobs)],
        'Extra-point actual ordered execution/scope differs')
    rows = []
    for job in jobs:
        owner = directory / job['stage']; P.need(E.sha(owner / 'report.json') == job['report_sha256'], 'Extra-point raw leaf hash differs')
        rows.append(leaf(inputs, digest, plan, job['stage'], owner))
    admission = None
    if rows and rows[0]['resource_feasible'] and rows[0]['expected_count97_observed']:
        admission = X.memory_admission(rows[0]['counts'], rows[0]['cgroup_after']['memory_peak'])
    P.need(report['memory_admission'] == admission, 'Extra-point source/count memory admission differs')
    if len(rows) == 2:
        P.need(admission is not None and admission['admitted']
            and X.memory_admission(rows[0]['counts'], rows[1]['cgroup_before']['memory_peak'])['admitted']
            and report['solve_counts_match_probe'] is (rows[0]['counts'] == rows[1]['counts']),
            'Extra-point solve skipped actual count-derived memory admission or counts changed')
    complete = len(rows) == 2 and all(r['process_tree_reaped'] is True for r in rows)
    work = report['work_wall_seconds']
    P.need(type(work) in (int, float) and math.isfinite(work) and work >= 0 and report['wall_seconds'] == work
        and report['work_budget_satisfied'] is (work <= 270), 'Extra-point actual270s work budget differs')
    feasible = complete and report['work_budget_satisfied'] and all(r['resource_feasible'] is True for r in rows)
    numeric = complete and rows[1]['numerical_passed'] and rows[0]['counts'] == rows[1]['counts']
    P.need(report['measurement_packet_completed'] is complete and report['resource_feasible'] is feasible
        and report['numerical_passed'] is numeric and report['passed'] is (feasible and numeric), 'Extra-point resource/numeric/measurement aggregate differs')
    resource = resource_join(resource_path, proposal_path, proposal, plan, report)
    root = Path(plan['scratch_host_path']); X.verify_owner(root, plan, digest)
    P.need(report['scratch_terminal_entries'] == sorted(p.name for p in root.iterdir())
        and report['scratch_stage_directories_empty'] is True and all(not list(p.iterdir()) for p in root.iterdir() if p.is_dir())
        and {p.name for p in directory.iterdir()} == {'report.json', *X.STAGES[:len(jobs)]}, 'Extra-point owned scratch/output residue differs')
    _, _, prior = X.original(inputs)
    math_result = continuity(prior, rows[1]) if feasible and numeric else dict(both_consecutive_pairs_at_most_two_percent=False, error='Incomplete/failed point packet')
    X.verify(inputs, digest); P.need(E.tree(runtime) == plan['runtime'], 'Extra-point runtime changed during HOST reopening')
    return dict(schema='pinwheel.streaming-8x4-rc-uniform-extra-independent-readback.v1', qualified=False,
        model_qualified=False, qualified_timing=False, full55_limited_pilot_passed=False, extended_universe_authority=False,
        point_continuity_passed=feasible and numeric and math_result['both_consecutive_pairs_at_most_two_percent'] and resource['status'] == 'completed',
        measurement_packet_completed=complete, resource_feasible=feasible, numerical_passed=numeric,
        new_point_plan=X.U.F.bound(inputs / 'plan.json'), execution_report=X.U.F.bound(directory / 'report.json'),
        command_proposal=X.U.F.bound(proposal_path), resource_cleanup_join=resource, memory_admission=admission,
        original55_failed_readback_sha256=X.FULL_READBACK, original55_failure_unchanged=True,
        leaves=rows, continuity=math_result, native_executed_by_readback=False, scope=X.policy()['scope'])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for n in ('inputs', 'directory', 'runtime', 'resource-report', 'command-proposal', 'output'): p.add_argument('--' + n, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    result = readback(a.inputs, a.plan_sha256, a.directory, a.runtime, a.resource_report, a.command_proposal)
    X.write(a.output, result); print(json.dumps({k: result[k] for k in ('measurement_packet_completed', 'resource_feasible', 'numerical_passed', 'point_continuity_passed', 'full55_limited_pilot_passed')}, indent=2))
    return 0 if result['point_continuity_passed'] else 2


if __name__ == '__main__': raise SystemExit(main())
