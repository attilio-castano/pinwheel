"""Independent HOST raw SPEF/resource readback; no Native/field solve.

Measurement controls and independently referenced physical accuracy are separate
states. Missing actual layered prerequisites leave accuracy unmeasured.
"""
import argparse
from decimal import Decimal as D
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer_cap as W
import streaming_8x4_rc_layered_analyze as H


def regular(path):
    W.need(path.is_file() and not path.is_symlink(), 'Missing/aliased cap evidence file')
    return path


def resource_join(resource_path, proposal_path, proposal, base, plan, report):
    r = json.loads(regular(resource_path).read_text()); expected_exit = 0 if report['passed'] else 2
    W.need(r['schema'] == 'pinwheel.streaming-tt-resource-job.v1' and r['cleanup_confirmed'] is True
        and r['inputs_unchanged'] is True and r['containers_remaining'] == [] and r['owned_processes_remaining'] == []
        and r['cleanup_errors'] == [] and r['argv'] == proposal['argv'] and r['timeout_seconds'] == 180
        and type(r['exit_code']) is int and r['exit_code'] == expected_exit
        and r['status'] == ('completed' if expected_exit == 0 else 'failed'), 'Cap exact resource terminal/argv/cleanup differs')
    seals = r['input_sha256']
    W.need(seals[str(proposal_path.resolve())] == W.P.sha(proposal_path)
        and seals[str((base / 'plan.json').resolve())] == proposal['plan_sha256']
        and all(seals[str(Path(W.__file__).with_name(n).resolve())] == h for n, h in plan['producer_sha256'].items()),
        'Cap resource proposal/plan/producer seals differ')
    return {'resource_report_sha256': W.P.sha(resource_path), 'proposal_sha256': W.P.sha(proposal_path),
            'cleanup_confirmed': True, 'inputs_unchanged': True, 'owned_processes_remaining': [], 'containers_remaining': []}


def raw_readback(base, plan_hash, directory):
    plan = W.verify(base, plan_hash); report_path = regular(directory / 'report.json')
    report = json.loads(report_path.read_text())
    W.need(report['schema'] == 'pinwheel.streaming-8x4-rc-consumer-cap-execution.v1'
        and report['plan_sha256'] == plan_hash and report['qualified'] is False and report['model_qualified'] is False
        and report['accuracy_status'] == 'unmeasured' and report['independent_accuracy_passed'] is False
        and type(report['passed']) is bool and report['measurement_packet_completed'] is True
        and report['inputs_unchanged'] is True and [j['job'] for j in report['jobs']] == W.JOBS,
        'Cap incomplete/reordered/promoted packet')
    cg = report['cgroups']; cpu = cg['cpu.max'].split()
    W.need(len(cpu) == 2 and cpu[0].isdigit() and 0 < int(cpu[0]) <= int(cpu[1])
        and cg['memory.max'].isdigit() and 0 < int(cg['memory.max']) <= 2147483648
        and cg['memory.swap.max'] == '0' and cg['pids.max'].isdigit() and 0 < int(cg['pids.max']) <= 128,
        'Actual cap cgroup ceiling differs')
    W.need({p.name for p in directory.iterdir()} == {'report.json'} | set(W.JOBS), 'Cap complete output membership differs')
    rows = []
    for job, record in zip(plan['jobs'], report['jobs']):
        owner = directory / job['job']; path = regular(owner / 'report.json'); leaf = json.loads(path.read_text())
        W.need(W.P.sha(path) == record['report_sha256'] and leaf['job'] == job['job']
            and leaf['passed'] is record['passed'] and leaf['argv'] == ['openroad', '-no_init', '-exit', 'run.tcl']
            and type(leaf['exit_code']) is int and type(leaf['timed_out']) is bool
            and leaf['process_tree_reaped'] is True and leaf['copied_inputs_unchanged'] is True
            and W.P.sha(regular(owner / 'native.log')) == leaf['native_log_sha256'], 'Cap raw leaf/exit/reap differs')
        expected_copies = {n: plan['files_sha256'][n] for n in ('tech.lef', 'rules.txt', 'run.tcl')}
        expected_copies['fixture.def'] = plan['files_sha256'][job['job'] + '.def']
        W.need(leaf['copied_input_sha256'] == expected_copies
            and all(W.P.sha(regular(owner / n)) == h for n, h in expected_copies.items()), 'Actual cap copied input custody differs')
        outputs = {n: W.P.sha(regular(owner / n)) for n in ('before.def', 'after.def', 'result.spef') if (owner / n).exists()}
        W.need(outputs == leaf['raw_output_sha256'], 'Cap retained output hashes differ')
        values = None; failure = None
        try:
            W.need(leaf['exit_code'] == 0 and not leaf['timed_out'], 'Cap OpenROAD exit/timeout failed')
            values = W.parse_leaf(owner, job)
        except (ValueError, OSError) as error:
            failure = type(error).__name__ + ': ' + str(error)
        W.need(leaf['passed'] is (failure is None) and leaf.get('values') == values
               and (failure is None or leaf['error'] == failure), 'Independent cap raw numeric/failure result differs')
        rows.append({'job': job['job'], 'values': values, 'numeric_passed': failure is None,
                     'error': failure, 'report_sha256': W.P.sha(path), 'raw_output_sha256': outputs})
    analysis = W.measurements(rows) if all(r['numeric_passed'] for r in rows) else None
    W.need(report.get('analysis') == analysis and report['passed'] is (analysis is not None and analysis['measurement_controls_passed']),
           'Cap aggregate measurement controls differ')
    W.verify(base, plan_hash)
    return plan, report, rows, analysis


def accuracy(base, plan, analysis, prerequisites):
    if not prerequisites:
        return {'accuracy_status': 'unmeasured', 'independent_accuracy_passed': False,
                'reason': 'No actual complete unchanged layered reference/BEM prerequisite packet supplied'}
    required = {'native_directory', 'reference_directory', 'geometry', 'runtime', 'layered_pass_report'}
    W.need(set(prerequisites) == required, 'Cap accuracy requires every actual reference/BEM evidence path')
    if analysis is None or not analysis['measurement_controls_passed']:
        return {'accuracy_status': 'blocked_by_measurement_failure', 'independent_accuracy_passed': False}
    native = base / 'native-plan.json'; reference = base / 'reference-plan.json'
    joined = H.analyze(native, W.NATIVE_HASH, prerequisites['native_directory'], prerequisites['geometry'],
                       prerequisites['runtime'], reference, prerequisites['reference_directory'])
    W.need(joined['limited_layered_M1_pilot_passed'] is True
           and json.loads(regular(prerequisites['layered_pass_report']).read_text()) == joined,
           'Cap complete unchanged independent layered prerequisite did not pass/recompute')
    ref_plan, ref_report = H.read_reference(reference, W.REFERENCE_HASH, prerequisites['reference_directory'])
    W.need([c for c in ref_plan['cases'] if c['name'] in W.CASES] == plan['reference_cases'],
           'Cap actual reference cross-section/materials differ')
    fine = {r['case_id']: r for r in ref_report['cases'] if r['declared_mesh'] == '.02' and r['declared_extent'] == '32'}
    results = []
    for row in analysis['jobs']:
        case = W.definition(row['job'])['case']; reference_row = fine[case]
        target = [D(str(x)) for v in reference_row['matrix_F_per_m'] for x in v]
        target += [D(str(x)) for x in reference_row['ground_C_F_per_m']]
        errors = [W.relative(W.vector(s), target) for s in row['slopes']]
        results.append({'job': row['job'], 'case': case, 'full_Maxwell_ground_coupling_relative_errors': list(map(str, errors)),
                        'passed': max(errors) <= D('.10')})
    return {'accuracy_status': 'pass' if all(r['passed'] for r in results) else 'fail',
            'independent_accuracy_passed': all(r['passed'] for r in results), 'comparisons': results,
            'layered_pass_report_sha256': W.P.sha(prerequisites['layered_pass_report']),
            'reference_report_sha256': W.P.sha(prerequisites['reference_directory'] / 'report.json'),
            'prerequisite_gates_unchanged': True, 'model_qualified': False}


def readback(base, plan_hash, directory, resource_path, proposal_path, prerequisites=None):
    plan, report, rows, analysis = raw_readback(base, plan_hash, directory)
    proposal = json.loads(regular(proposal_path).read_text())
    W.need(proposal == W.command_proposal(base, plan_hash, directory.parent, require_fresh=False)
           and directory.name == W.OUTPUT, 'Actual cap command proposal/output owner differs')
    resource = resource_join(resource_path, proposal_path, proposal, base, plan, report)
    physical = accuracy(base, plan, analysis, prerequisites)
    return {'schema': 'pinwheel.streaming-8x4-rc-consumer-cap-independent-readback.v1', 'qualified': False,
        'model_qualified': False, 'plan_sha256': plan_hash, 'execution_report_sha256': W.P.sha(directory / 'report.json'),
        'measurement_packet_completed': True, 'measurement_controls_passed': report['passed'], 'jobs': rows,
        'analysis': analysis, 'physical_accuracy': physical, 'resource_cleanup_join': resource,
        'spacing_control_is_physical_boundary_test': False, 'native_executed_by_readback': False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for n in ('inputs', 'directory', 'resource-report', 'command-proposal', 'output'):
        p.add_argument('--' + n, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True)
    for n in ('native-directory', 'reference-directory', 'geometry', 'runtime', 'layered-pass-report'):
        p.add_argument('--' + n, type=Path)
    a = p.parse_args(); names = ('native_directory', 'reference_directory', 'geometry', 'runtime', 'layered_pass_report')
    values = {n: getattr(a, n) for n in names if getattr(a, n) is not None}
    W.need(not values or set(values) == set(names), 'Provide all physical accuracy prerequisite paths or none')
    result = readback(a.inputs, a.plan_sha256, a.directory, a.resource_report, a.command_proposal, values or None)
    W.write(a.output, result); print(json.dumps({'measurement_controls_passed': result['measurement_controls_passed'],
        'physical_accuracy': result['physical_accuracy'], 'model_qualified': False}, indent=2))


if __name__ == '__main__': main()
