"""Independent marker lookup diagnostic; no physical accuracy authority."""
import argparse
from decimal import Decimal as D
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_cap_marker as W

ROOT = Path(__file__).resolve().parents[1]


def campaign_boundary(row):
    b = row['campaign_boundary']
    W.need(b['schema'] == 'pinwheel.streaming-8x4-resource-boundary.v1'
        and b['campaign_root'] == str(ROOT) and b['campaign_kind'] == 'rc_experiment'
        and b['shared_lease'] == {'heavy_lock': str(ROOT/'build/streaming-tt-resources/heavy.lock'),
                                 'cleanup_sentinel': str(ROOT/'build/streaming-tt-resources/cleanup-unconfirmed.json')}
        and b['wrapper_sha256'] == W.P.sha(regular(ROOT/'scripts/streaming_8x4_acceptance_resources.py'))
        and b['inherited_supervisor_sha256'] == row['supervisor_sha256']
            == W.P.sha(regular(ROOT/'scripts/streaming_tt_resources.py')),
        'Supplementary C exact campaign/shared-lock/wrapper/supervisor identity differs')
    return b


def regular(path):
    W.need(path.is_file() and not path.is_symlink(), 'Missing/aliased cap evidence file')
    return path


def resource_join(resource_path, proposal_path, proposal, base, plan, report):
    r = json.loads(regular(resource_path).read_text()); expected_exit = 0 if report['passed'] else 2
    boundary = campaign_boundary(r)
    W.need(r['schema'] == 'pinwheel.streaming-tt-resource-job.v1' and r['cleanup_confirmed'] is True
        and r['inputs_unchanged'] is True and r['containers_remaining'] == [] and r['owned_processes_remaining'] == []
        and r['cleanup_errors'] == [] and r['argv'] == proposal['argv'] and r['timeout_seconds'] == 120
        and type(r['exit_code']) is int and r['exit_code'] == expected_exit
        and r['status'] == ('completed' if expected_exit == 0 else 'failed'), 'Cap exact resource terminal/argv/cleanup differs')
    seals = r['input_sha256']
    W.need(seals[str(proposal_path.resolve())] == W.P.sha(proposal_path)
        and seals[str((base / 'plan.json').resolve())] == proposal['plan_sha256']
        and all(seals[str(Path(W.__file__).with_name(n).resolve())] == h for n, h in plan['producer_sha256'].items()),
        'Cap resource proposal/plan/producer seals differ')
    return {'resource_report_sha256': W.P.sha(resource_path), 'proposal_sha256': W.P.sha(proposal_path),
            'cleanup_confirmed': True, 'inputs_unchanged': True, 'owned_processes_remaining': [], 'containers_remaining': [],
            'campaign_boundary': boundary, 'supervisor_sha256': r['supervisor_sha256']}


def raw_readback(base, plan_hash, directory):
    plan = W.verify(base, plan_hash); report_path = regular(directory / 'report.json')
    report = json.loads(report_path.read_text())
    W.need(report['schema'] == 'pinwheel.streaming-8x4-rc-cap-marker-execution.v1'
        and report['plan_sha256'] == plan_hash and report['qualified'] is False and report['model_qualified'] is False
        and report['full_accuracy_status'] == 'unmeasured' and report['qualified_timing'] is False and report['finite_BEM_passed'] is False
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
        expected_copies = {n: plan['files_sha256'][n] for n in ('tech.lef', 'run.tcl')}
        expected_copies['rules.txt'] = plan['files_sha256'][job['job']+'-rules.txt']
        expected_copies['fixture.def'] = plan['files_sha256'][job['job'] + '.def']
        W.need(leaf['copied_input_sha256'] == expected_copies
            and all(W.P.sha(regular(owner / n)) == h for n, h in expected_copies.items()), 'Actual cap copied input custody differs')
        outputs = {n: W.P.sha(regular(owner / n)) for n in ('before.def', 'after.def', 'result.spef') if (owner / n).exists()}
        W.need(outputs == leaf['raw_output_sha256'], 'Cap retained output hashes differ')
        values = None; failure = None
        try:
            W.need(leaf['exit_code'] == 0 and not leaf['timed_out'], 'Marker OpenROAD exit/timeout failed')
            values = W.parse_leaf(owner, job)
        except (ValueError, OSError) as error:
            failure = type(error).__name__ + ': ' + str(error)
        W.need(leaf['passed'] is (failure is None) and leaf.get('values') == values
               and (failure is None or leaf['error'] == failure), 'Independent cap raw numeric/failure result differs')
        rows.append({'job': job['job'], 'values': values, 'numeric_passed': failure is None,
                     'error': failure, 'report_sha256': W.P.sha(path), 'raw_output_sha256': outputs})
    analysis = W.measurements(rows) if all(r['numeric_passed'] for r in rows) else None
    work=work_budget(report)
    W.need(report.get('analysis') == analysis and report['passed'] is (work and analysis is not None and analysis['lookup_marker_diagnostic_passed']),
           'Cap aggregate measurement controls differ')
    W.verify(base, plan_hash)
    return plan, report, rows, analysis




def work_budget(report):
    elapsed=report['actual_work_seconds']
    W.need(type(elapsed) in (int,float) and 0<=elapsed<float('inf') and report['wall_seconds']==elapsed
        and type(report['work_budget_passed']) is bool and report['work_budget_passed'] is (elapsed<=90),
        'Marker observed work budget/flag differs')
    return report['work_budget_passed']


def readback(base,digest,directory,resource_path,proposal_path):
    plan,report,rows,analysis=raw_readback(base,digest,directory)
    proposal=json.loads(regular(proposal_path).read_text())
    W.need(proposal==W.command_proposal(base,digest,directory.parent,require_fresh=False)
        and directory.name==W.OUTPUT,'Marker exact command/output owner differs')
    resource=resource_join(resource_path,proposal_path,proposal,base,plan,report)
    return dict(schema='pinwheel.streaming-8x4-rc-cap-marker-independent-readback.v1',qualified=False,
        model_qualified=False,qualified_timing=False,finite_BEM_passed=False,full_accuracy_status='unmeasured',
        plan_sha256=digest,execution_report_sha256=W.P.sha(directory/'report.json'),measurement_packet_completed=True,
        lookup_marker_diagnostic_passed=report['passed'],work_budget_passed=report['work_budget_passed'],
        actual_work_seconds=report['actual_work_seconds'],jobs=rows,analysis=analysis,resource_cleanup_join=resource,
        coefficient_fitted=False,baseline_Maxwell_matrix_claimed=False,native_executed_by_readback=False)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for n in ('inputs','directory','resource-report','command-proposal','output'):p.add_argument('--'+n,type=Path,required=True)
    p.add_argument('--plan-sha256',required=True);a=p.parse_args()
    result=readback(a.inputs,a.plan_sha256,a.directory,a.resource_report,a.command_proposal)
    W.write(a.output,result);print(json.dumps({k:result[k] for k in ('lookup_marker_diagnostic_passed','full_accuracy_status','model_qualified')},indent=2))


if __name__=='__main__':main()
