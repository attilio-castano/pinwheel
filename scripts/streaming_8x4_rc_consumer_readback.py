"""HOST raw-file readback of the frozen consumer/via experiment.

Keep the overall workflow and each tested component distinct. A wire-width
failure remains a failure even if the five tested via-name arithmetic controls
pass. No process/foundry/full-model qualification is issued here.
"""
import argparse
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_consumer as C


def regular(path):
    C.need(path.is_file() and not path.is_symlink(), 'Missing/aliased consumer raw file')
    return path


def component_summary(plan, jobs):
    expected = [(c, p) for c in ('MIN', 'TYP', 'MAX') for p in C.POLICIES]
    C.need([(j['corner'], j['policy']) for j in jobs] == expected, 'Consumer corner/policy membership differs')
    via_names = list(C.VIA_FIXTURES)
    default_wires = [r['name'] for r in plan['fixture_rows'] if r['via'] is None and '_wide_' not in r['name']]
    all_vias = True; all_default = True; all_wires = True
    for job in jobs:
        analysis = job['analysis']
        C.need([r['name'] for r in analysis['vias']] == via_names, 'Tested via-name component membership differs')
        wires = {r['name']: r for r in analysis['wires']}
        C.need(set(default_wires) <= set(wires), 'Default wire controls missing')
        all_vias &= all(r['passed'] is True for r in analysis['vias'])
        all_default &= all(wires[n]['passed'] is True for n in default_wires)
        all_wires &= all(r['passed'] is True for r in analysis['wires'])
    return {'via_corner_consumer_arithmetic_passed': bool(all_vias and all_default),
            'all_default_width_wire_controls_passed': bool(all_default),
            'all_width_wire_controls_passed': bool(all_wires),
            'full_consumer_experiment_passed': bool(all_vias and all_wires),
            'tested_tech_via_names': via_names, 'corners': ['MIN', 'TYP', 'MAX'],
            'generated_dbVia_coverage': False, 'all_explicit_tech_via_names_measured': False,
            'independent_parallel_cut_physics_qualified': False,
            'model_qualified': False,
            'scope': 'retained fallback and owned VIARES per-cut ITF arithmetic for exactly five measured tech-via names; default-width wire controls mandatory'}


def readback(inputs, plan_hash, directory):
    plan = C.verify_plan(inputs, plan_hash)
    report_path = regular(directory / 'report.json'); report = json.loads(report_path.read_text())
    C.need(report['schema'] == 'pinwheel.streaming-8x4-rc-consumer-execution.v1'
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
        C.need(regular(owner / 'before.def').read_bytes() == regular(owner / 'after.def').read_bytes(),
               'Consumer extraction changed geometry readback')
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
    C.verify_plan(inputs, plan_hash)
    return {'schema': 'pinwheel.streaming-8x4-rc-consumer-independent-readback.v1',
            'qualified': False, 'model_qualified': False, 'plan_sha256': plan_hash,
            'execution_report_sha256': C.P.sha(report_path), 'workflow_passed': report['passed'],
            'all_six_native_calls_closed': True, 'components': components, 'jobs': jobs,
            'producer_sha256': C.P.sha(__file__),
            'resource_cleanup_join': 'separate Root resource-supervisor receipt required, including when the numeric experiment exits nonzero'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--inputs', type=Path, required=True); p.add_argument('--plan-sha256', required=True)
    p.add_argument('--directory', type=Path, required=True); p.add_argument('--output', type=Path, required=True)
    a = p.parse_args(); C.need(not a.output.exists() and a.output.parent.is_dir(), 'Consumer readback output must be fresh')
    result = readback(a.inputs, a.plan_sha256, a.directory)
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'workflow_passed': result['workflow_passed'], 'components': result['components']}, indent=2))


if __name__ == '__main__':
    main()
