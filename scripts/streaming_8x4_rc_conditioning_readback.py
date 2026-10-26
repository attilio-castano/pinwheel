"""Independent HOST raw-log/resource reopening of fixed conditioning packets."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_conditioning as W
import streaming_8x4_rc_conditioning_parser as Q
import streaming_8x4_rc_execute as E
import streaming_8x4_rc_protocol as P


def membership(report, plan_hash, profile):
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-conditioning-execution.v1'
        and report['profile'] == profile and report['plan_sha256'] == plan_hash
        and report['policy'] == W.policy(profile)
        and all(report[k] is False for k in ('qualified', 'model_qualified', 'full_pilot_passed'))
        and report['measurement_packet_completed'] is True and report['inputs_runtime_unchanged'] is True
        and type(report['passed']) is bool and [r['branch'] for r in report['jobs']] == Q.branches(profile),
        'Incomplete/reordered/promoted conditioning packet')


def numeric_readback(log, row, plan, branch):
    profile = plan['profile']
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-conditioning-leaf.v1'
        and row['profile'] == profile and row['branch'] == branch and row['case'] == plan['case']['name']
        and row['argv'] == Q.argv(branch, profile) and row['environment'] == W.ENVIRONMENT
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'full_pilot_passed'))
        and row['timeout_seconds'] == 120 and type(row['exit_code']) is int and type(row['timed_out']) is bool,
        'Conditioning actual arguments/scope/branch differ')
    numeric = None; passed = False; error = None
    try:
        P.need(row['exit_code'] == 0 and not row['timed_out'], 'Conditioning solver exit/timeout failed')
        numeric = Q.parse(log, plan['case']['matrix_names'], branch, profile, plan['case']['coordinate_unit_m']); passed = True
    except (ValueError, KeyError, TypeError) as failure: error = type(failure).__name__ + ': ' + str(failure)
    P.need(row['passed'] is passed and row['numeric'] == numeric
        and (error is None or row['error'] == error) and row['observations'] == Q.observations(log, plan['case']['matrix_names']),
        'Conditioning independent numeric/error/raw observation differs')
    return {'branch': branch, 'passed': passed, 'numeric': numeric, 'error': error,
            'observations': row['observations'], 'exit_code': row['exit_code'], 'timed_out': row['timed_out']}


def resource_join(path, proposal_path, proposal, inputs, plan, report):
    resource = json.loads(path.read_text())
    P.need(resource['schema'] == 'pinwheel.streaming-tt-resource-job.v1'
        and resource['cleanup_confirmed'] is True and resource['inputs_unchanged'] is True
        and resource['containers_remaining'] == [] and resource['owned_processes_remaining'] == []
        and resource['cleanup_errors'] == [] and resource['argv'] == proposal['argv']
        and resource['timeout_seconds'] == plan['policy']['outer_seconds']
        and type(resource['exit_code']) is int and resource['exit_code'] == (0 if report['passed'] else 2)
        and resource['status'] == ('completed' if report['passed'] else 'failed'),
        'Conditioning exact resource policy/terminal/cleanup differs')
    seals = resource['input_sha256']
    P.need(seals[str(proposal_path.resolve())] == E.sha(proposal_path)
        and seals[str((inputs / 'plan.json').resolve())] == proposal['plan_sha256']
        and all(seals[str(Path(W.__file__).with_name(n).resolve())] == value for n, value in plan['producer_sha256'].items()),
        'Conditioning resource input source/plan/proposal seals differ')
    return {'resource_report_sha256': E.sha(path), 'proposal_sha256': E.sha(proposal_path),
        'cleanup_confirmed': True, 'inputs_unchanged': True, 'containers_remaining': [],
        'owned_processes_remaining': [], 'exit_code': resource['exit_code']}


def readback(inputs, plan_hash, directory, runtime, resource_path, proposal_path):
    plan = W.verify(inputs, plan_hash); profile = plan['profile']
    report = json.loads((directory / 'report.json').read_text()); membership(report, plan_hash, profile)
    proposal = json.loads(proposal_path.read_text())
    P.need(proposal == W.container_proposal(inputs, plan_hash, runtime, directory.parent, require_fresh=False)
        and directory.name == W.BASELINES[profile]['output'], 'Exact conditioning proposal/output owner differs')
    resource = resource_join(resource_path, proposal_path, proposal, inputs, plan, report)
    P.need({p.name for p in directory.iterdir()} == {'report.json'} | {'job-' + str(i).zfill(3) for i in range(len(Q.branches(profile)))},
           'Conditioning complete output membership differs')
    rows = []
    for index, (job, branch) in enumerate(zip(report['jobs'], Q.branches(profile))):
        owner = directory / ('job-' + str(index).zfill(3)); path = owner / 'report.json'
        P.need({p.name for p in owner.iterdir()} == {'report.json', 'native.log', 'work'}
            and E.sha(path) == job['report_sha256'], 'Conditioning leaf receipt/membership differs')
        leaf = json.loads(path.read_text()); W.D.closed_leaf(leaf)
        P.need(leaf['plan_sha256'] == plan_hash and leaf['passed'] == job['passed']
            and E.sha(owner / 'native.log') == leaf['log_sha256'] and E.tree(owner / 'work') == plan['case']['files']
            and W.runtime_unchanged(plan, runtime), 'Conditioning leaf/raw geometry/runtime custody differs')
        c = leaf['cgroups']; cpu = c['cpu_max'].split()
        P.need(c['memory_max'].isdigit() and 0 < int(c['memory_max']) <= 6442450944 and c['memory_swap_max'] == '0'
            and len(cpu) == 2 and all(x.isdigit() for x in cpu) and 0 < int(cpu[0]) <= int(cpu[1])
            and c['pids_max'].isdigit() and 0 < int(c['pids_max']) <= 128,
            'Conditioning actual cgroup ceilings differ')
        numeric = numeric_readback((owner / 'native.log').read_text(), leaf, plan, branch)
        rows.append(dict(report_sha256=E.sha(path), raw_log_sha256=E.sha(owner / 'native.log'), **numeric))
    aggregate = Q.aggregate(profile, rows)
    P.need(all(report[k] == value for k, value in aggregate.items()), 'Conditioning numeric/mesh aggregate differs')
    W.verify(inputs, plan_hash); P.need(W.runtime_unchanged(plan, runtime), 'Conditioning runtime changed during HOST readback')
    return {'schema': 'pinwheel.streaming-8x4-rc-conditioning-independent-readback.v1', 'profile': profile,
        'plan_sha256': plan_hash, 'qualified': False, 'model_qualified': False, 'full_pilot_passed': False,
        'continuum_error_enclosure': False, 'measurement_packet_completed': True,
        'execution_report_sha256': E.sha(directory / 'report.json'), 'resource_cleanup_join': resource,
        'branches': rows, 'numeric_and_mesh_outcome': aggregate, 'scope': plan['policy']['scope'],
        'native_executed_by_readback': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for n in ('inputs', 'directory', 'runtime', 'resource-report', 'command-proposal', 'output'):
        p.add_argument('--' + n, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    result = readback(a.inputs, a.plan_sha256, a.directory, a.runtime, a.resource_report, a.command_proposal)
    W.write(a.output, result); print(json.dumps({'measurement_packet_completed': True,
        'numeric_and_mesh_outcome': result['numeric_and_mesh_outcome'], 'model_qualified': False}, indent=2))


if __name__ == '__main__': main()
