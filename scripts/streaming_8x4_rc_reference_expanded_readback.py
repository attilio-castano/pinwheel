"""Independent HOST readback of the new exact 32-grid FVM measurement packet."""
import argparse
import json
import math
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_reference_expanded as W
P, E = W.P, W.E


def numeric_leaf(plan, digest, index, owner):
    row = json.loads((owner / 'leaf.json').read_text()); job = W.jobs(plan)[index]
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-reference-expanded-leaf.v1'
        and row['plan_sha256'] == digest and row['index'] == index and row['job'] == job
        and all(row[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing', 'finite_BEM_passed'))
        and type(row['numeric_passed']) is bool, 'Expanded reference actual leaf authority differs')
    passed = False; error = None
    if row['kernel_row'] is not None:
        try: W.validate_row(plan, job, row['kernel_row']); passed = True
        except (ValueError, KeyError, TypeError, ArithmeticError) as failure:
            error = type(failure).__name__ + ': ' + str(failure)
    else:
        P.need(type(row.get('error')) is str and row['error'], 'Failed field kernel lacks retained error')
    P.need(row['numeric_passed'] is passed and (error is None or row['error'] == error),
           'Independent FVM raw numeric/failed evidence differs')
    return row


def dispatch(plan, digest, index, owner):
    row = json.loads((owner / 'dispatch.json').read_text()); expected = {'dispatch.json', 'native.log'}
    if row['leaf_sha256'] is not None: expected.add('leaf.json')
    P.need({p.name for p in owner.iterdir()} == expected and all(p.is_file() and not p.is_symlink() for p in owner.iterdir())
        and row['schema'] == 'pinwheel.streaming-8x4-rc-reference-expanded-dispatch.v1'
        and row['index'] == index and row['plan_sha256'] == digest and row['timeout_seconds'] == 120
        and row['argv'] == W.dispatch_argv(Path('/rc-inputs'), digest, index,
            Path('/rc-output-parent') / W.OUTPUT / owner.name / 'leaf.json')
        and row['log_sha256'] == E.sha(owner / 'native.log')
        and row['native_log_empty'] is ((owner / 'native.log').stat().st_size == 0)
        and math.isfinite(row['wall_seconds']) and 0 <= row['wall_seconds'] < 130,
        'FVM actual dispatch/log/output/budget authority differs')
    # A report with no leaf can be preserved as a closed failed resource prefix;
    # it can never be treated as a successful numerical observation.
    observed_resource = W.resource_feasible(row) and row['leaf_sha256'] is not None
    P.need(row['resource_feasible'] is observed_resource, 'FVM actual resource status differs')
    leaf = None
    if row['leaf_sha256'] is not None:
        P.need(E.sha(owner / 'leaf.json') == row['leaf_sha256'], 'FVM raw leaf hash differs')
        leaf = numeric_leaf(plan, digest, index, owner)
        P.need(row['numeric_passed'] is (leaf['numeric_passed'] and row['exit_code'] == 0 and row['native_log_empty'])
            and (row['exit_code'] not in (0, 2) or row['exit_code'] == (0 if leaf['numeric_passed'] else 2)),
            'FVM process/numeric result differs')
    else: P.need(row['numeric_passed'] is False, 'Missing FVM leaf cannot pass')
    return {'index': index, 'job': W.jobs(plan)[index], 'resource_feasible': observed_resource,
        'numeric_passed': row['numeric_passed'], 'dispatch_sha256': E.sha(owner / 'dispatch.json'),
        'leaf_sha256': row['leaf_sha256'], 'kernel_row': leaf['kernel_row'] if leaf else None,
        'error': leaf.get('error') if leaf else row.get('error'), 'actual_dispatch': row}


def analysis(plan, leaves):
    P.need(len(leaves) == 32 and [r['job'] for r in leaves] == W.jobs(plan)
        and all(r['resource_feasible'] and r['numeric_passed'] for r in leaves), 'Complete strict 32-grid observations required')
    groups = {(r['job']['case'], r['job']['step'], r['job']['extent']): r['kernel_row'] for r in leaves}
    results = []
    for case in plan['cases']:
        fine = groups[case['name'], '.02', '64']
        mesh = W.M.relative_change(W.M.flatten(groups[case['name'], '.04', '64']), W.M.flatten(fine))
        domain = W.M.relative_change(W.M.flatten(groups[case['name'], '.02', '32']), W.M.flatten(fine))
        results.append({'case': case['name'], 'fine_matrix_F_per_m': fine['matrix_F_per_m'],
            'fine_ground_C_F_per_m': fine['ground_C_F_per_m'], 'fine_coupling_C_F_per_m': fine['coupling_C_F_per_m'],
            'mesh_relative_change': mesh, 'domain_relative_change': domain,
            'passed': mesh <= .02 and domain <= .02})
    return {'cases': results, 'passed': all(r['passed'] for r in results),
        'no_continuum_error_enclosure': True, 'scope': 'empirical mesh/domain comparisons on the complete declared reference universe'}


def resource_join(path, proposal_path, proposal, plan, report):
    result = W.H.resource_join(path, proposal_path, proposal, plan, report)
    resource = json.loads(path.read_text()); boundary = resource['campaign_boundary']
    P.need(boundary['campaign_root'] == str(W.ROOT)
        and boundary['shared_lease']['cleanup_sentinel'] == str(W.ROOT / 'build/streaming-tt-resources/cleanup-unconfirmed.json'),
        'Expanded reference campaign/shared cleanup sentinel differs')
    return result


def work_state(report, rows):
    duration=report['actual_work_seconds']
    P.need(type(duration) in (int,float) and math.isfinite(duration) and duration>=0
        and report['wall_seconds']==duration
        and report['work_budget_passed'] is (duration<=W.policy()['work_seconds']),
        'Expanded actual terminal work duration/budget flag differs')
    complete=len(rows)==32
    leaf_resources=complete and all(r['resource_feasible'] for r in rows)
    numeric=complete and all(r['numeric_passed'] for r in rows)
    resources=leaf_resources and report['work_budget_passed']
    P.need(report['measurement_packet_completed'] is complete and report['resource_feasible'] is resources
        and report['all_numeric_leaves_passed'] is numeric and report['passed'] is (numeric and resources),
        'Expanded measurement/resource/numeric/actual-work aggregate differs')
    return complete,numeric,resources,leaf_resources


def readback(inputs, digest, directory, resource_path, proposal_path):
    plan = W.verify(inputs, digest); proposal = json.loads(proposal_path.read_text())
    P.need(proposal == W.proposal(inputs, digest, directory.parent, require_fresh=False)
        and directory.name == W.OUTPUT, 'Expanded reference exact command/output differs')
    report = json.loads((directory / 'report.json').read_text()); jobs = report['jobs']; expected = W.jobs(plan)
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-reference-expanded-execution.v1'
        and report['plan_sha256'] == digest and report['policy'] == W.policy()
        and all(report[k] is False for k in ('qualified', 'model_qualified', 'qualified_timing', 'finite_BEM_passed', 'reference_stability_passed'))
        and report['inputs_sources_unchanged'] is True and len(jobs) <= 32
        and [{k: j[k] for k in ('case', 'step', 'extent')} for j in jobs] == expected[:len(jobs)]
        and [j['index'] for j in jobs] == list(range(len(jobs)))
        and {p.name for p in directory.iterdir()} == {'report.json'} | {'job-' + str(i).zfill(3) for i in range(len(jobs))},
        'Expanded reference actual execution order/input/scope differs')
    rows = []
    for i, job in enumerate(jobs):
        owner = directory / ('job-' + str(i).zfill(3)); row = dispatch(plan, digest, i, owner)
        P.need(all(row[k] == job[k] for k in ('numeric_passed', 'resource_feasible', 'dispatch_sha256')),
            'Expanded reference actual job/dispatch differs'); rows.append(row)
        P.need(i == len(jobs) - 1 or row['resource_feasible'], 'Expanded reference suffix after failed resource/custody forbidden')
    complete,numeric,resources,leaf_resources=work_state(report,rows)
    resource = resource_join(resource_path, proposal_path, proposal, plan, report)
    math_result = analysis(plan, rows) if numeric and leaf_resources else {'passed': False, 'error': 'Incomplete or failed fixed reference universe'}
    passed = numeric and resources and math_result['passed'] and resource['status'] == 'completed'
    W.verify(inputs, digest)
    return {'schema': 'pinwheel.streaming-8x4-rc-reference-expanded-independent-readback.v1',
        'qualified': False, 'model_qualified': False, 'qualified_timing': False, 'finite_BEM_passed': False,
        'continuum_error_enclosure': False, 'expanded_reference_complete_passed': passed,
        'measurement_packet_completed': complete, 'all_numeric_leaves_passed': numeric,
        'resource_feasible': resources, 'actual_work_seconds': report['actual_work_seconds'],
        'work_budget_passed': report['work_budget_passed'],
        'new_expanded_reference_plan': W.H.bound(inputs / 'plan.json'), 'parent_reference_only_plan_sha256': W.BASELINE, 'historical_plan_sha256': plan['historical_plan_sha256'],
        'historical_plan_executed_or_admitted': False, 'execution_report': W.H.bound(directory / 'report.json'),
        'command_proposal': W.H.bound(proposal_path), 'resource_cleanup_join': resource,
        'original_failed_reference_authority': plan['original_failed_reference_authority'],
        'original_M1_FVM_control_authority': plan['original_M1_FVM_control_authority'],
        'producer_sha256': plan['producer_sha256'], 'leaves': rows, 'analysis': math_result,
        'native_executed_by_readback': False, 'scope': W.policy()['scope']}


def closed_authority(path):
    row = json.loads(path.read_text())
    for item in (row['new_expanded_reference_plan'], row['execution_report'], row['command_proposal'], row['resource_cleanup_join']['resource_report']):
        P.need(E.sha(Path(item['path'])) == item['sha256'], 'Expanded reference closed authority dependency changed')
    plan = row['new_expanded_reference_plan']
    actual = readback(Path(plan['path']).parent, plan['sha256'], Path(row['execution_report']['path']).parent,
        Path(row['resource_cleanup_join']['resource_report']['path']), Path(row['command_proposal']['path']))
    P.need(actual == row and row['expanded_reference_complete_passed'] is True, 'Failed/prefix/foreign expanded reference packet cannot confer authority')
    return row


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for n in ('inputs', 'directory', 'resource-report', 'command-proposal', 'output'): p.add_argument('--' + n, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    row = readback(a.inputs, a.plan_sha256, a.directory, a.resource_report, a.command_proposal)
    W.W.write(a.output, row)
    print(json.dumps({k: row[k] for k in ('measurement_packet_completed', 'all_numeric_leaves_passed', 'expanded_reference_complete_passed', 'model_qualified')}, indent=2))
    return 0 if row['expanded_reference_complete_passed'] else 2


if __name__ == '__main__': raise SystemExit(main())
