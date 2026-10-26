"""Independent HOST physical/raw R-study readback and separate Root custody.

An incomplete/error packet is preserved without a mathematical pass. Original
absolute failures and model/capacitance qualification stay separate.
"""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_r_length as W

P, need = W.P, W.need


def regular(path):
    need(path.is_file() and not path.is_symlink(), 'Missing/aliased R-study raw file'); return path


def bound(path): return dict(path=str(path.resolve()), sha256=P.sha(regular(path)))


def resource_join(path, proposal_path, proposal, plan, report):
    resource = json.loads(regular(path).read_text()); boundary = resource['campaign_boundary']
    code = resource['exit_code']; status = resource['status']
    need(resource['schema'] == 'pinwheel.streaming-tt-resource-job.v1' and type(code) is int
        and ((status == 'stopped' and code == 124) or (status == ('completed' if report['passed'] else 'failed')
             and code == (0 if report['passed'] else 2)))
        and resource['argv'] == proposal['argv'] and resource['timeout_seconds'] == 300
        and resource['cleanup_confirmed'] is True and resource['inputs_unchanged'] is True
        and resource['owned_processes_remaining'] == [] and resource['containers_remaining'] == [] and resource['cleanup_errors'] == []
        and boundary['schema'] == 'pinwheel.streaming-8x4-resource-boundary.v1'
        and boundary['campaign_root'] == str(W.ROOT) and boundary['campaign_kind'] == 'rc_experiment'
        and boundary['shared_lease']['heavy_lock'] == str(W.ROOT / 'build/streaming-tt-resources/heavy.lock')
        and boundary['wrapper_sha256'] == P.sha(W.ROOT / 'scripts/streaming_8x4_acceptance_resources.py')
        and boundary['inherited_supervisor_sha256'] == resource['supervisor_sha256'] == P.sha(W.ROOT / 'scripts/streaming_tt_resources.py'),
        'R-study exact Root command/terminal/cleanup/shared-lock scope differs')
    seals = resource['input_sha256']; required = {str(proposal_path.resolve()): P.sha(proposal_path),
        proposal['plan_path']: proposal['plan_sha256'], proposal['parent_semantic_proposal']['path']: proposal['parent_semantic_proposal']['sha256']}
    required.update({str(W.ROOT / 'scripts' / n): h for n, h in plan['producer_sha256'].items()})
    need(all(seals.get(n) == h == P.sha(n) for n, h in required.items()), 'R-study Root source/proposal/plan seal omitted or changed')
    return dict(resource_report=bound(path), command_proposal=bound(proposal_path), resource_custody_closed=True,
        status=status, exit_code=code, cleanup_confirmed=True, inputs_unchanged=True, diagnostic_pass_claim=False)


def raw_readback(base, digest, directory, plan):
    path = regular(directory / 'report.json'); report = json.loads(path.read_text())
    need(report['schema'] == 'pinwheel.streaming-8x4-rc-R-length-width-execution.v1' and report['plan_sha256'] == digest
        and all(report[k] is False for k in ('qualified', 'model_qualified', 'capacitance_qualified', 'original_17net_experiment_passed'))
        and report['original_absolute_audits_retained'] is True and report['measurement_packet_completed'] is True
        and report['inputs_unchanged'] is True and type(report['passed']) is bool
        and [(j['corner'], j['policy']) for j in report['jobs']] == W.M.JOBS,
        'Complete ordered fresh R-study packet required')
    cg = report['cgroups']; cpu = cg['cpu.max'].split()
    need(cg['memory.max'].isdigit() and 0 < int(cg['memory.max']) <= 2147483648 and cg['memory.swap.max'] == '0'
        and len(cpu) == 2 and all(v.isdigit() for v in cpu) and 0 < int(cpu[0]) <= int(cpu[1])
        and cg['pids.max'].isdigit() and 0 < int(cg['pids.max']) <= 128, 'Actual R-study cgroup resources differ')
    expected = {c + '-' + p for c, p in W.M.JOBS}
    need({p.name for p in directory.iterdir()} == {'report.json'} | expected, 'R-study exact output membership differs')
    rows = []
    for job in report['jobs']:
        corner, policy = job['corner'], job['policy']; owner = directory / (corner + '-' + policy)
        need({p.name for p in owner.iterdir()} == {'tech.lef', 'widths.lef', 'fixture.def', 'run.tcl', 'rules.txt',
            'native.log', 'before.def', 'after.def', 'result.spef', 'physical.json'}
            and job['argv'] == ['openroad', '-no_init', '-exit', 'run.tcl'] and type(job['exit_code']) is int and job['exit_code'] == 0
            and job['process_tree_reaped'] is True and job['copied_inputs_unchanged'] is True,
            'Actual R-study leaf membership/execution/cleanup differs')
        selected = W.copies(plan, corner, policy)
        copies = {'fixture.def': 'fixture.def', 'widths.lef': 'widths.lef', 'tech.lef': selected['tech'],
            'run.tcl': selected['tcl'], 'rules.txt': selected['rules']}
        need(job['copied_input_sha256'] == {n: plan['generated_files_sha256'][v] for n, v in copies.items()}
            and all(P.sha(regular(owner / n)) == h for n, h in job['copied_input_sha256'].items())
            and job['output_sha256'] == {n: P.sha(regular(owner / n)) for n in ('native.log', 'before.def', 'after.def', 'result.spef', 'physical.json')},
            'Actual R-study selected copies/raw hashes differ')
        parsed = W.parse_leaf(base, plan, owner, corner, policy)
        need(json.loads(regular(owner / 'physical.json').read_text()) == parsed['geometry']
            and all(job[k] == parsed[k] for k in ('values', 'absolute_audit', 'rounding_intervals')),
            'Independent R-study geometry/SPEF/absolute audit/rounding intervals differ')
        rows.append(job)
    analysis = W.M.measurements(plan, rows)
    need(report['analysis'] == analysis and report['passed'] is analysis['length_width_diagnostic_controls_passed'],
        'R-study original absolute or separate slope/heldout/via aggregate differs')
    W.verify(base, digest)
    return dict(schema='pinwheel.streaming-8x4-rc-R-length-width-raw-readback.v1', measurement_packet_completed=True,
        length_width_diagnostic_controls_passed=analysis['length_width_diagnostic_controls_passed'],
        analysis=analysis, execution_report=bound(path), all_six_actual_physical_and_raw_packets_reopened=True,
        original_17net_experiment_passed=False, model_qualified=False, capacitance_qualified=False)


def closeout(base, digest, directory, resource_path, proposal_path):
    plan = W.verify(base, digest); proposal = json.loads(regular(proposal_path).read_text())
    need(proposal == W.proposal(base, digest, Path(proposal['parent_semantic_proposal']['path']), require_fresh=False)
        and directory.resolve() == Path(proposal['output_directory']).resolve(), 'R-study exact proposal/output differs')
    report = json.loads(regular(directory / 'report.json').read_text())
    need(report['schema'] == 'pinwheel.streaming-8x4-rc-R-length-width-execution.v1' and report['plan_sha256'] == digest
        and type(report['passed']) is bool and report['model_qualified'] is False, 'R-study worker scope differs')
    resource = resource_join(resource_path, proposal_path, proposal, plan, report)
    try: raw = raw_readback(base, digest, directory, plan)
    except (ValueError, OSError, KeyError, TypeError) as error:
        raw = dict(schema='pinwheel.streaming-8x4-rc-R-length-width-raw-failure.v1', measurement_packet_completed=False,
            length_width_diagnostic_controls_passed=False, error=type(error).__name__ + ': ' + str(error),
            execution_report=bound(directory / 'report.json'), original_17net_experiment_passed=False,
            model_qualified=False, capacitance_qualified=False)
    return dict(schema='pinwheel.streaming-8x4-rc-R-length-width-independent-closeout.v1',
        resource_custody_closed=True, resource_join=resource, raw_readback=raw,
        measurement_packet_completed=raw['measurement_packet_completed'],
        length_width_diagnostic_controls_passed=raw['length_width_diagnostic_controls_passed'] and resource['status'] == 'completed',
        original_17net_experiment_passed=False, model_qualified=False, capacitance_qualified=False, native_executed_by_closeout=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for n in ('inputs', 'directory', 'resource-report', 'command-proposal', 'output'): parser.add_argument('--' + n, type=Path, required=True)
    parser.add_argument('--plan-sha256', required=True); a = parser.parse_args()
    result = closeout(a.inputs, a.plan_sha256, a.directory, a.resource_report, a.command_proposal); W.write(a.output, result)
    print(json.dumps({k: result[k] for k in ('resource_custody_closed', 'measurement_packet_completed',
        'length_width_diagnostic_controls_passed', 'original_17net_experiment_passed', 'model_qualified')}, indent=2))


if __name__ == '__main__': main()
