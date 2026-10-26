"""Independent HOST readback of the two-call supplementary five-layer C study.

Raw numeric and reference failures remain visible. Complete empirical reference
prerequisites remain mandatory; full physical accuracy is always unmeasured.
"""
import argparse
from decimal import Decimal as D
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_cap_all_layers as W

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
    W.need(report['schema'] == 'pinwheel.streaming-8x4-rc-cap-all-layers-execution.v1'
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
        expected_copies = {n: plan['files_sha256'][n] for n in ('tech.lef', 'run.tcl')}
        expected_copies['rules.txt'] = plan['files_sha256']['rules.txt']
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




def reference_targets(base,plan,authority):
    closed=W.R.closed_authority(authority)
    W.need(closed['new_reference_only_plan']['sha256']==W.REFERENCE32_HASH
        and closed['original_M1_FVM_control_authority']==plan['original_M1_FVM_control_authority'],
        'Supplementary C actual complete reference32/FVM25 authority differs')
    old=W.F.W.reference_join(base/'reference32-inputs',W.F.W.PROFILES[0])
    W.need(old==plan['original_M1_FVM_control_authority'],'Original full FVM25 empirical/custody prerequisite differs')
    results=base/'reference32-inputs/reference/results'
    report=json.loads((results/'report.json').read_text());job=report['jobs'][3]
    W.need((job['case'],job['step'],job['extent'],job['uniform_control'])==('TYP-w.16-self','.02','32',False)
        and W.P.sha(results/'case-003.json')==job['output_sha256'],'Exact M1 fine independent target differs')
    first=json.loads((results/'case-003.json').read_text())
    targets={'TYP-Metal1-self':dict(matrix_F_per_m=first['matrix_F_per_m'],ground_F_per_m=first['ground_C_F_per_m'])}
    for case in W.G.CASES[1:]:
        selected=[r['kernel_row'] for r in closed['leaves'] if r['job']==dict(case=case['reference_case_id'],step='.02',extent='32')]
        W.need(len(selected)==1,'Complete exact upper-layer fine target membership differs')
        row=selected[0];targets[case['name']]=dict(matrix_F_per_m=row['matrix_F_per_m'],ground_F_per_m=row['ground_C_F_per_m'])
    W.need(set(targets)=={c['name'] for c in W.G.CASES},'Complete nine-case reference targets required')
    return targets,closed


def provisional(base,plan,analysis,rows,authority):
    common=dict(full_accuracy_status='unmeasured',finite_BEM_passed=False,model_qualified=False,qualified_timing=False,
        empirical_reference_is_not_continuum_enclosure=True,no_fitting_in_this_study=True)
    if authority is None:
        return dict(common,status='unmeasured',reference_prerequisites_passed=False,
            provisional_numeric_comparison_passed=False,reason='No actual complete passing reference-only32 authority supplied')
    binding=dict(path=str(authority.resolve()),sha256=W.P.sha(regular(authority)))
    try:targets,closed=reference_targets(base,plan,authority)
    except (ValueError,OSError,KeyError,TypeError) as error:
        return dict(common,status='blocked_by_reference_failure',reference_prerequisites_passed=False,
            provisional_numeric_comparison_passed=False,reference32_authority=binding,error=type(error).__name__+': '+str(error))
    if analysis is None or not analysis['measurement_controls_passed']:
        return dict(common,status='blocked_by_measurement_failure',reference_prerequisites_passed=True,
            provisional_numeric_comparison_passed=False,reference32_authority=binding)
    comparisons=[]
    for row in analysis['jobs']:
        target=targets[row['case']];vector=[D(str(x)) for line in target['matrix_F_per_m'] for x in line]+[D(str(x)) for x in target['ground_F_per_m']]
        W.need(all(len(W.C.vector(s))==len(vector) for s in row['slopes']),
            'Complete supplementary target/measurement dimensions differ')
        errors=[[abs(x/y-1) for x,y in zip(W.C.vector(slope),vector)] for slope in row['slopes']]
        W.need(all(len(e)==len(vector) for e in errors),'Complete supplementary comparison cell count differs')
        raw=next(r for r in rows if r['job']==row['job']);rounding=max(D(v['writer_rounding_bound_F']) for v in raw['values']['nets'].values())*8/D('50e-6')
        comparisons.append(dict(job=row['job'],case=row['case'],target=target,slopes=row['slopes'],
            per_slope_complete_matrix_ground_relative_errors=[[str(x) for x in e] for e in errors],
            largest_relative_difference=str(max(x for e in errors for x in e)),
            conservative_each_slope_cell_writer_rounding_bound_F_per_m=str(rounding),
            printing_bound_is_not_physical_reference_error_enclosure=True,
            passed=max(x for e in errors for x in e)<=D('.10')))
    passed=all(r['passed'] for r in comparisons)
    return dict(common,status='pass' if passed else 'fail',reference_prerequisites_passed=True,
        provisional_numeric_comparison_passed=passed,reference32_authority=binding,
        original_M1_FVM_control_authority=plan['original_M1_FVM_control_authority'],comparisons=comparisons,
        widths_are_nominal_samples_not_range_qualification=True,known_M1_self_development_failure_must_remain_visible=True)


def readback(base,digest,directory,resource_path,proposal_path,reference32_authority=None):
    plan,report,rows,analysis=raw_readback(base,digest,directory)
    proposal=json.loads(regular(proposal_path).read_text())
    W.need(proposal==W.command_proposal(base,digest,directory.parent,require_fresh=False) and directory.name==W.OUTPUT,
        'Supplementary C exact command proposal/output differs')
    resource=resource_join(resource_path,proposal_path,proposal,base,plan,report)
    comparisons=provisional(base,plan,analysis,rows,reference32_authority)
    return dict(schema='pinwheel.streaming-8x4-rc-cap-all-layers-independent-readback.v1',qualified=False,model_qualified=False,
        qualified_timing=False,finite_BEM_passed=False,full_accuracy_status='unmeasured',plan_sha256=digest,
        execution_report_sha256=W.P.sha(directory/'report.json'),measurement_packet_completed=True,
        measurement_controls_passed=report['passed'],jobs=rows,analysis=analysis,provisional_comparison=comparisons,
        resource_cleanup_join=resource,spacing_control_is_physical_boundary_test=False,native_executed_by_readback=False)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for n in ('inputs','directory','resource-report','command-proposal','output'):p.add_argument('--'+n,type=Path,required=True)
    p.add_argument('--plan-sha256',required=True);p.add_argument('--reference32-authority',type=Path)
    a=p.parse_args();result=readback(a.inputs,a.plan_sha256,a.directory,a.resource_report,a.command_proposal,a.reference32_authority)
    W.write(a.output,result);print(json.dumps({k:result[k] for k in ('measurement_controls_passed','provisional_comparison','full_accuracy_status','model_qualified')},indent=2))


if __name__=='__main__':main()
