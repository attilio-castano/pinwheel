"""New typed limited-pilot authority from complete fresh logs and original FVM."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_full_policy as W
import streaming_8x4_rc_full_execute as X

P, E, L, U = W.P, W.E, W.L, W.U


def bound(path):
    path = Path(path).resolve(); P.need(path.is_file(), 'Missing full-policy authority file')
    return {'path': str(path), 'sha256': E.sha(path)}


def numeric_leaf(plan, digest, job, owner):
    row = json.loads((owner / 'report.json').read_text()); X.closed(row)
    case = next(c for c in plan['cases'] if c['name'] == job['case']); raw = (owner / 'native.log').read_text()
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-full-policy-native-leaf.v1'
        and row['profile'] == plan['profile'] and row['plan_sha256'] == digest
        and row['case'] == job['case'] and row['mesh'] == job['mesh'] and row['timeout_seconds'] == 120
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing'))
        and row['argv'] == W.solver_argv(plan['policy'], job['mesh']) and row['environment'] == W.C.ENVIRONMENT
        and E.sha(owner / 'native.log') == row['log_sha256'] and E.tree(owner / 'work') == case['files'],
        'Full-policy actual leaf scope/arguments/log/geometry differs')
    c = row['cgroups']; cpu = c['cpu_max'].split()
    P.need(c['memory_max'].isdigit() and 0 < int(c['memory_max']) <= 6442450944 and c['memory_swap_max'] == '0'
        and len(cpu) == 2 and all(x.isdigit() for x in cpu) and 0 < int(cpu[0]) <= int(cpu[1])
        and c['pids_max'].isdigit() and 0 < int(c['pids_max']) <= 128, 'Full-policy actual cgroup ceiling differs')
    numeric = None; passed = False; error = None
    try:
        P.need(row['exit_code'] == 0 and row['timed_out'] is False, 'Full-policy solver exit/timeout failed')
        numeric = X.parse(raw, plan, case, job['mesh']); passed = True
    except (ValueError, KeyError, TypeError) as failure: error = type(failure).__name__ + ': ' + str(failure)
    P.need(row['passed'] is passed and row['passed'] == job['passed'] and row['numeric'] == numeric
        and (error is None or row['error'] == error) and row['observations'] == X.O.observations(raw, case['matrix_names']),
        'Full-policy independent numeric/error/raw evidence differs')
    return {'case': case['name'], 'mesh': job['mesh'], 'passed': passed, 'numeric': numeric,
        'error': error, 'report_sha256': E.sha(owner / 'report.json'), 'log_sha256': E.sha(owner / 'native.log')}


def mathematical_analysis(plan, leaves):
    """Use unchanged numerical equations, without invoking old schema dispatch."""
    expected = W.jobs(plan)
    P.need([{'case': r['case'], 'mesh': r['mesh']} for r in leaves] == expected and all(r['passed'] is True for r in leaves),
           'Complete fresh numeric universe required for limited-pilot mathematics')
    groups = {c['name']: [r['numeric'] for r in leaves if r['case'] == c['name']] for c in plan['cases']}
    mesh_results = []
    for case in plan['cases']:
        values = groups[case['name']]; changes = [P.cellwise_change(a, b) for a, b in zip(values, values[1:])]
        stable = len(values) == 5 and all(x <= P.number('.02') for x in changes[-2:])
        mesh_results.append({'case': case['name'], 'changes': list(map(str, changes)), 'passed': stable})
    if not all(r['passed'] for r in mesh_results):
        return {'passed': False, 'mesh_results': mesh_results, 'comparisons': [], 'error': 'Complete-universe two-successive matrix mesh gate failed'}
    comparisons = []; old = plan['original_protocol']
    if plan['profile'] == W.PROFILES[0]:
        reference = plan['reference_join']['analysis']['cases']
        for row in reference:
            native = [c for c in plan['cases'] if c['case'] == row['name']]
            finite = {(c['length_um'], c['extension_um']): [r[1:] for r in groups[c['name']][-1]['matrix_F'][1:]] for c in native}
            count = len(row['fine_matrix_F_per_m']); names = ['W' + str(i + 1) for i in range(count)]
            result = L.compare_case(old, names, finite, row['fine_matrix_F_per_m'])
            comparisons.append(dict(case=row['name'], role=row['role'], **result))
    else:
        refs = plan['reference_join']['analysis']
        for width in ('0.16', '0.32'):
            def cap(length, margin):
                name = 'wire_w' + width.replace('.', 'p') + '_L' + length + '_M' + margin
                return P.number(groups[name][-1]['matrix_F'][1][1])
            a = (cap('20', '20') - cap('10', '20')) / P.number('.00001')
            b = (cap('30', '20') - cap('20', '20')) / P.number('.00001')
            extended = (cap('30', '30') - cap('20', '30')) / P.number('.00001')
            length = U.relative(a, b); boundary = U.relative(extended, b); error = U.relative(b, refs[width]['reference_F_per_m'])
            comparisons.append({'width_um': width, 'native_F_per_m': str(b), 'reference': refs[width],
                'length_slope_relative_change': str(length), 'ground_extension_relative_change': str(boundary),
                'independent_reference_relative_difference': str(error),
                'passed': length <= P.number('.05') and boundary <= P.number('.02') and error <= P.number('.10')})
    return {'passed': all(r['passed'] for r in comparisons), 'mesh_results': mesh_results, 'comparisons': comparisons}


def resource_join(path, proposal_path, proposal, plan, report):
    row = json.loads(path.read_text()); code = row['exit_code']; status = row['status']; b = row['campaign_boundary']
    P.need(type(code) is int and ((status == 'stopped' and code == 124) or
        (status in ('completed', 'failed') and code == (0 if report['passed'] else 2)
         and status == ('completed' if report['passed'] else 'failed'))), 'Full-policy actual resource terminal contract differs')
    P.need(row['schema'] == 'pinwheel.streaming-tt-resource-job.v1' and row['argv'] == proposal['argv']
        and row['timeout_seconds'] == plan['policy']['outer_seconds'] and row['cleanup_confirmed'] is True
        and row['inputs_unchanged'] is True and row['containers_remaining'] == []
        and row['owned_processes_remaining'] == [] and row['cleanup_errors'] == []
        and b['schema'] == 'pinwheel.streaming-8x4-resource-boundary.v1' and b['campaign_root'] == str(W.ROOT)
        and b['campaign_kind'] == 'rc_experiment' and b['shared_lease']['heavy_lock'] == str(W.ROOT / 'build/streaming-tt-resources/heavy.lock')
        and b['wrapper_sha256'] == E.sha(Path(__file__).with_name('streaming_8x4_acceptance_resources.py'))
        and b['inherited_supervisor_sha256'] == row['supervisor_sha256'] == E.sha(Path(__file__).with_name('streaming_tt_resources.py')),
        'Full-policy exact resource/shared-lock/process cleanup differs')
    seals = row['input_sha256']
    P.need(seals[str(proposal_path.resolve())] == E.sha(proposal_path) and seals[proposal['plan_path']] == proposal['plan_sha256']
        and all(seals[str(W.ROOT / 'scripts' / n)] == value for n, value in plan['producer_sha256'].items()),
        'Full-policy resource source/proposal/plan seals differ')
    return {'resource_report': bound(path), 'cleanup_confirmed': True, 'inputs_unchanged': True,
        'owned_processes_remaining': [], 'containers_remaining': [], 'exit_code': code, 'status': status}


def readback(inputs, digest, directory, runtime, resource_path, proposal_path):
    plan = W.verify(inputs, digest); proposal = json.loads(proposal_path.read_text())
    P.need(proposal == W.proposal(inputs, digest, runtime, directory.parent, require_fresh=False)
        and directory.name == proposal['output_name'], 'Full-policy exact new command/output differs')
    path = directory / 'report.json'; report = json.loads(path.read_text()); jobs = report['jobs']; expected = W.jobs(plan)
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-full-policy-native-execution.v1'
        and report['profile'] == plan['profile'] and report['plan_sha256'] == digest and report['policy'] == plan['policy']
        and all(report[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing', 'limited_pilot_passed'))
        and report['inputs_runtime_unchanged'] is True and type(report['passed']) is bool and len(jobs) <= len(expected)
        and [{k: r[k] for k in ('case', 'mesh')} for r in jobs] == expected[:len(jobs)],
        'Full-policy complete/prefix authority or promotion differs')
    P.need({p.name for p in directory.iterdir()} == {'report.json'} | {'job-' + str(i).zfill(3) for i in range(len(jobs))},
           'Full-policy actual output membership differs')
    leaves = []
    for index, job in enumerate(jobs):
        owner = directory / ('job-' + str(index).zfill(3))
        P.need({p.name for p in owner.iterdir()} == {'report.json', 'native.log', 'work'}
            and E.sha(owner / 'report.json') == job['report_sha256'], 'Full-policy actual leaf membership/seal differs')
        leaves.append(numeric_leaf(plan, digest, job, owner))
    complete = len(leaves) == len(expected); numeric = complete and all(r['passed'] is True for r in leaves)
    P.need(report['measurement_packet_completed'] is complete and report['all_numeric_leaves_passed'] is numeric
        and report['passed'] is numeric, 'Full-policy measurement/numeric aggregate differs')
    resource = resource_join(resource_path, proposal_path, proposal, plan, report)
    analysis = {'passed': False, 'error': 'Incomplete strict full-policy universe'}
    if numeric:
        try: analysis = mathematical_analysis(plan, leaves)
        except (ValueError, KeyError, TypeError) as error: analysis = {'passed': False, 'error': type(error).__name__ + ': ' + str(error)}
    # A stopped outer controller cannot confer authority, even if an inner
    # report had already finished all measurements before external cleanup.
    passed = numeric and analysis['passed'] is True and resource['status'] == 'completed'
    units = []
    if plan['profile'] == W.PROFILES[0]:
        units = [L.check_unit_witness(Path(plan['original_geometry_owner']), c['name']) for c in plan['cases']]
        P.need(units == plan['unit_witnesses'], 'Original full S20 witness changed')
    W.verify(inputs, digest); P.need(E.tree(runtime) == plan['runtime'], 'Full-policy runtime changed during HOST readback')
    return {'schema': 'pinwheel.streaming-8x4-rc-full-policy-independent-readback.v1', 'profile': plan['profile'],
        'qualified': False, 'model_qualified': False, 'qualified_timing': False, 'continuum_error_enclosure': False,
        'limited_pilot_passed': passed, 'limited_layered_M1_pilot_passed': passed and plan['profile'] == W.PROFILES[0],
        'uniform_finite_wire_pilot_passed': passed and plan['profile'] == W.PROFILES[1],
        'measurement_packet_completed': complete, 'all_numeric_leaves_passed': numeric,
        'new_policy_plan': bound(inputs / 'plan.json'), 'old_native_plan_sha256': plan['old_native_plan_sha256'],
        'native_report': bound(path), 'runtime_path': str(runtime.resolve()), 'command_proposal': bound(proposal_path),
        'resource_cleanup_join': resource, 'original_reference_authority': plan['reference_join'],
        'producer_sha256': plan['producer_sha256'], 'unit_witnesses': units, 'native_leaves': leaves, 'analysis': analysis,
        'native_executed_by_readback': False,
        'scope': 'Complete declared M1 layered self/lateral pilot only; full process model remains unqualified' if plan['profile'] == W.PROFILES[0] else 'Complete declared finite uniform-wire pilot only; full process model remains unqualified'}


def closed_authority(path):
    row = json.loads(Path(path).read_text()); plan = row['new_policy_plan']; native = row['native_report']
    for item in (plan, native, row['command_proposal'], row['resource_cleanup_join']['resource_report']):
        P.need(E.sha(Path(item['path'])) == item['sha256'], 'Full-policy authority dependency changed')
    actual = readback(Path(plan['path']).parent, plan['sha256'], Path(native['path']).parent, Path(row['runtime_path']),
        Path(row['resource_cleanup_join']['resource_report']['path']), Path(row['command_proposal']['path']))
    P.need(actual == row and row['limited_pilot_passed'] is True, 'A prefix/foreign/promoted/failed full-policy result cannot confer authority')
    return row


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for n in ('inputs', 'directory', 'runtime', 'resource-report', 'command-proposal', 'output'): p.add_argument('--' + n, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    result = readback(a.inputs, a.plan_sha256, a.directory, a.runtime, a.resource_report, a.command_proposal)
    W.write(a.output, result); print(json.dumps({k: result[k] for k in ('measurement_packet_completed', 'all_numeric_leaves_passed', 'limited_pilot_passed', 'model_qualified', 'qualified_timing')}, indent=2))
    return 0 if result['limited_pilot_passed'] else 2


if __name__ == '__main__': raise SystemExit(main())
