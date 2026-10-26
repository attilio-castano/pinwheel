"""Independent HOST raw six-call readback under the new physical gate.

Original strict R equations/component summaries are unchanged. Resource cleanup
is an additional exact Root obligation even when the numerical result fails.
"""
import argparse
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer_semantic as W
import streaming_8x4_rc_consumer_readback as OLD

C = W.C
regular, component_summary = OLD.regular, OLD.component_summary


def physical(base, owner, job):
    result = W.geometry_gate(base, owner); path = regular(owner / 'semantic-geometry.json')
    C.need(C.P.sha(path) == job['semantic_geometry_sha256'] and json.loads(path.read_text()) == result,
        'Semantic physical receipt differs from actual complete DEF readback')
    C.need({p.name for p in owner.iterdir()} == {'tech.lef', 'widths.lef', 'fixture.def', 'run.tcl', 'rules.txt',
        'native.log', 'before.def', 'after.def', 'result.spef', 'semantic-geometry.json'},
        'Semantic exact leaf artifact membership differs')
    return result


def native_readback(inputs, plan_hash, directory):
    plan = W.verify_consumer(inputs, plan_hash)
    report_path = regular(directory / 'report.json'); report = json.loads(report_path.read_text())
    C.need(report['schema'] == 'pinwheel.streaming-8x4-rc-consumer-route-native-execution.v1'
           and report['plan_sha256'] == plan_hash and report['qualified'] is False
           and report['model_qualified'] is False and report['inputs_unchanged'] is True
           and type(report['passed']) is bool and len(report['jobs']) == 6,
           'Consumer workflow did not close complete expected membership')
    expected = [(c, p) for c in ('MIN', 'TYP', 'MAX') for p in C.POLICIES]
    C.need([(j['corner'], j['policy']) for j in report['jobs']] == expected, 'Consumer actual job membership differs')
    jobs = []
    for job in report['jobs']:
        corner, policy = job['corner'], job['policy']; owner = directory / (corner + '-' + policy)
        log = regular(owner / 'native.log'); spef = regular(owner / 'result.spef')
        C.need(type(job['exit_code']) is int and job['exit_code'] == 0
               and job['argv'] == ['openroad', '-no_init', '-exit', 'run.tcl']
               and job['geometry_unchanged'] is True and job['copied_inputs_unchanged'] is True
               and job['process_tree_reaped'] is True, 'Consumer Native execution facts differ')
        C.need(C.P.sha(log) == job['native_log_sha256'] and C.P.sha(spef) == job['SPEF_sha256'],
               'Actual consumer log/SPEF differs from receipt')
        raw = log.read_text()
        C.need(not re.search(r'(?im)\b(?:warning|warn|error|fatal)\b', raw)
               and raw.count('PINWHEEL_CONSUMER_TERMINAL') == 1, 'Consumer native warning/error/terminal gap')
        physical(inputs, owner, job)
        for name in ('tech.lef', 'widths.lef', 'fixture.def', 'run.tcl'):
            C.need(C.P.sha(regular(owner / name)) == plan['files_sha256'][name], 'Copied consumer input changed')
        C.need(C.P.sha(regular(owner / 'rules.txt')) == plan['files_sha256'][corner + '-' + policy + '.txt'],
               'Copied corner/policy rules changed')
        values = C.parse_spef(spef.read_text(), {r['name'] for r in plan['fixture_rows']})
        analysis = C.analyze_values(plan, corner, policy, values)
        C.need(values == job['values'] and analysis == job['analysis'], 'Independent raw SPEF analysis differs')
        jobs.append({'corner': corner, 'policy': policy, 'values': values, 'analysis': analysis,
                     'native_log_sha256': C.P.sha(log), 'SPEF_sha256': C.P.sha(spef),
                     'geometry_unchanged': True, 'copied_inputs_unchanged': True})
    components = component_summary(plan, jobs)
    C.need(report['passed'] == components['full_consumer_experiment_passed'], 'Overall consumer workflow/result differs')
    W.verify_consumer(inputs, plan_hash)
    return {'schema': 'pinwheel.streaming-8x4-rc-consumer-route-native-independent-readback.v1',
            'qualified': False, 'model_qualified': False, 'plan_sha256': plan_hash,
            'execution_report_sha256': C.P.sha(report_path), 'workflow_passed': report['passed'],
            'all_six_native_calls_closed': True, 'components': components, 'jobs': jobs,
            'producer_sha256': C.P.sha(__file__),
            'resource_cleanup_join': 'separate Root resource-supervisor receipt required, including when the numeric experiment exits nonzero'}


def readback(inputs, plan_hash, directory):
    plan = W.verify(inputs, plan_hash); path = regular(directory / 'report.json'); report = json.loads(path.read_text())
    C.need(report['schema'] == 'pinwheel.streaming-8x4-rc-consumer-route-execution.v1'
        and report['plan_sha256'] == plan_hash and report['qualified'] is False and report['model_qualified'] is False
        and type(report['passed']) is bool and report['all_six_native_calls_closed'] is True
        and report['original_numeric_policy_unchanged'] is True and report['initial_native_DEF_exact'] is True
        and report['inputs_unchanged'] is True and C.P.sha(regular(directory / 'native/report.json')) == report['inner_report_sha256']
        and {p.name for p in directory.iterdir()} == {'report.json', 'native'}, 'Complete fresh typed semantic packet required')
    expected = {c + '-' + p for c in ('MIN', 'TYP', 'MAX') for p in C.POLICIES}
    C.need({p.name for p in (directory / 'native').iterdir()} == {'report.json'} | expected,
        'Semantic exact six-call output membership differs')
    raw = native_readback(inputs / 'consumer-inputs', plan['consumer_plan_sha256'], directory / 'native')
    C.need(raw['workflow_passed'] is report['passed'] and W.verify(inputs, plan_hash) == plan,
        'Semantic actual raw result/input closeout differs')
    return dict(schema='pinwheel.streaming-8x4-rc-consumer-route-independent-readback.v1', qualified=False,
        model_qualified=False, plan_sha256=plan_hash, execution_report_sha256=C.P.sha(path),
        workflow_passed=raw['workflow_passed'], all_six_native_calls_closed=True,
        exact_initial_native_DEF_checked_in_all_six_calls=True, complete_semantic_physical_gate_checked_in_all_six_calls=True,
        original_numeric_policy_unchanged=True, raw_consumer_readback=raw,
        resource_cleanup_join='Separate exact Root argv/input/exit/cleanup receipt remains mandatory, including numerical failure.')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('inputs', 'directory', 'output'): p.add_argument('--' + name, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); args = p.parse_args()
    result = readback(args.inputs, args.plan_sha256, args.directory); W.write(args.output, result)
    print(json.dumps(dict(workflow_passed=result['workflow_passed'], components=result['raw_consumer_readback']['components']), indent=2))


if __name__ == '__main__': main()
