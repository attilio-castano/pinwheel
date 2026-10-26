"""Independent HOST raw-log/resource reopener of the fixed four-call packet."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_solver_diagnostic as W
import streaming_8x4_rc_solver_diagnostic_parser as Q
import streaming_8x4_rc_execute as E
import streaming_8x4_rc_protocol as P


def membership(report, plan_hash):
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-solver-diagnostic-execution.v1'
        and report['plan_sha256'] == plan_hash and report['protocol'] == W.protocol()
        and report['qualified'] is False and report['model_qualified'] is False
        and report['uniform_finite_wire_pilot_passed'] is False
        and report['measurement_packet_completed'] is True and report['inputs_runtime_unchanged'] is True
        and type(report['passed']) is bool and [r['branch'] for r in report['jobs']] == Q.BRANCHES,
        'Incomplete/reordered/duplicated/promoted four-call diagnostic packet')


def numeric_readback(log, report, plan, branch):
    P.need(report['argv'] == Q.argv(branch) and report['environment'] == W.ENVIRONMENT
        and report['branch'] == branch and report['case'] == W.CASE
        and type(report['exit_code']) is int and type(report['timed_out']) is bool,
        'Actual diagnostic arguments/branch/exit type differs')
    numeric = None; passed = False; error = None
    try:
        P.need(report['exit_code'] == 0 and not report['timed_out'], 'Diagnostic solver exit/timeout failed')
        numeric = Q.parse(log, plan['case']['matrix_names'], branch, plan['case']['coordinate_unit_m'])
        passed = True
    except (ValueError, KeyError, TypeError) as failure:
        error = type(failure).__name__ + ': ' + str(failure)
    P.need(report['passed'] is passed and report.get('numeric') == numeric
        and (error is None or report['error'] == error)
        and report['failure_evidence'] == Q.failure_evidence(log), 'Independent branch numeric/error readback differs')
    return {'numeric_passed': passed, 'numeric': numeric, 'failure_evidence': Q.failure_evidence(log),
            'error': error, 'exit_code': report['exit_code'], 'timed_out': report['timed_out']}


def resource_join(path, proposal_path, proposal, inputs, plan, report):
    resource = json.loads(path.read_text())
    P.need(resource['schema'] == 'pinwheel.streaming-tt-resource-job.v1'
        and resource['cleanup_confirmed'] is True and resource['inputs_unchanged'] is True
        and resource['containers_remaining'] == [] and resource['owned_processes_remaining'] == []
        and resource['cleanup_errors'] == [] and resource['argv'] == proposal['argv']
        and resource['timeout_seconds'] == 600 and type(resource['exit_code']) is int
        and resource['exit_code'] == (0 if report['passed'] else 2)
        and resource['status'] == ('completed' if report['passed'] else 'failed'),
        'Exact diagnostic resource argv/terminal exit/cleanup seal differs')
    seals = resource['input_sha256']
    P.need(seals[str(proposal_path.resolve())] == E.sha(proposal_path)
        and seals[str((inputs / 'plan.json').resolve())] == proposal['plan_sha256']
        and all(seals[str(Path(W.__file__).with_name(name).resolve())] == value
                for name, value in plan['producer_sha256'].items()),
        'Resource input seals omit/differ from admitted proposal/plan/producers')
    return {'resource_report_sha256': E.sha(path), 'proposal_sha256': E.sha(proposal_path),
            'cleanup_confirmed': True, 'inputs_unchanged': True,
            'containers_remaining': [], 'owned_processes_remaining': [], 'exit_code': resource['exit_code']}


def readback(inputs, plan_hash, directory, runtime, resource_path, proposal_path):
    plan = W.verify(inputs, plan_hash); report = json.loads((directory / 'report.json').read_text())
    membership(report, plan_hash); proposal = json.loads(proposal_path.read_text())
    P.need(proposal == W.command_proposal(inputs, plan_hash, runtime, directory.parent, require_fresh=False)
        and directory.name == W.OUTPUT, 'Exact diagnostic command proposal/output owner differs')
    resource = resource_join(resource_path, proposal_path, proposal, inputs, plan, report)
    P.need({p.name for p in directory.iterdir()} == {'report.json'} | {'job-' + str(i).zfill(3) for i in range(4)},
           'Diagnostic complete artifact membership differs')
    rows = []
    for index, (job, branch) in enumerate(zip(report['jobs'], Q.BRANCHES)):
        owner = directory / ('job-' + str(index).zfill(3)); leaf_path = owner / 'report.json'
        P.need({p.name for p in owner.iterdir()} == {'report.json', 'native.log', 'work'}
            and E.sha(leaf_path) == job['report_sha256'], 'Raw diagnostic leaf receipt/membership differs')
        leaf = json.loads(leaf_path.read_text()); W.closed_leaf(leaf)
        P.need(leaf['schema'] == 'pinwheel.streaming-8x4-rc-solver-diagnostic-leaf.v1'
            and leaf['plan_sha256'] == plan_hash and leaf['qualified'] is False and leaf['model_qualified'] is False
            and leaf['uniform_finite_wire_pilot_passed'] is False and type(leaf['passed']) is bool
            and job['passed'] == leaf['passed'] and E.sha(owner / 'native.log') == leaf['log_sha256']
            and E.tree(owner / 'work') == plan['case']['files']
            and E.tree(inputs / 'geometry') == plan['case']['files'] and W.runtime_unchanged(plan, runtime),
            'Diagnostic raw/copied/source/runtime custody differs')
        c = leaf['cgroups']; cpu = c['cpu_max'].split()
        P.need(c['memory_max'].isdigit() and 0 < int(c['memory_max']) <= 6442450944
            and c['memory_swap_max'] == '0' and len(cpu) == 2 and all(v.isdigit() for v in cpu)
            and 0 < int(cpu[0]) <= int(cpu[1]) and c['pids_max'].isdigit() and 0 < int(c['pids_max']) <= 256,
            'Actual leaf cgroup ceiling differs')
        numeric = numeric_readback((owner / 'native.log').read_text(), leaf, plan, branch)
        rows.append(dict(branch=branch, report_sha256=E.sha(leaf_path), raw_log_sha256=E.sha(owner / 'native.log'), **numeric))
    P.need(report['passed'] == all(r['numeric_passed'] for r in rows), 'Aggregate diagnostic numerical outcome differs')
    W.verify(inputs, plan_hash); P.need(W.runtime_unchanged(plan, runtime), 'Runtime changed during HOST readback')
    return {'schema': 'pinwheel.streaming-8x4-rc-solver-diagnostic-independent-readback.v1',
        'qualified': False, 'model_qualified': False, 'uniform_finite_wire_pilot_passed': False,
        'continuum_error_enclosure': False, 'plan_sha256': plan_hash,
        'measurement_packet_completed': True, 'all_four_numeric_branches_passed': report['passed'],
        'execution_report_sha256': E.sha(directory / 'report.json'), 'resource_cleanup_join': resource, 'branches': rows,
        'scope': W.protocol()['qualification_scope'], 'native_executed_by_readback': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('inputs', 'directory', 'runtime', 'resource-report', 'command-proposal', 'output'):
        p.add_argument('--' + name, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    result = readback(a.inputs, a.plan_sha256, a.directory, a.runtime, a.resource_report, a.command_proposal)
    W.write(a.output, result); print(json.dumps({'measurement_packet_completed': True,
        'all_four_numeric_branches_passed': result['all_four_numeric_branches_passed'], 'model_qualified': False}, indent=2))


if __name__ == '__main__': main()
