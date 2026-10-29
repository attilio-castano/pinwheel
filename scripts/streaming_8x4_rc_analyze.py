"""Independent HOST readback of frozen native RC pilot logs and references.

No subprocesses or numerical fitting.  Every expected width/length/ground case
must be present.  Missing measurements remain failures, and qualified is always
false: this pilot cannot establish the full process/extractor envelope.
"""
import argparse
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_protocol as P


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(a, b):
    a, b = P.number(str(a)), P.number(str(b))
    P.need(a > 0 and b > 0, 'Expected positive capacitance/reference')
    return abs(a - b) / b


def read_native(plan, plan_hash, directory):
    directory = Path(directory)
    report_path, log_path = directory / 'report.json', directory / 'native.log'
    P.need(report_path.is_file() and log_path.is_file() and not report_path.is_symlink()
           and not log_path.is_symlink(), 'Missing/aliased actual Native result')
    report = json.loads(report_path.read_text())
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-manual-execution.v1', 'Wrong Native report schema')
    P.need(report['plan_sha256'] == plan_hash and report['passed'] is True and report['qualified'] is False,
           'Wrong plan, failed or promoted Native workflow')
    P.need(type(report['exit_code']) is int and report['exit_code'] == 0 and report['timed_out'] is False
           and report['solver_executed'] is True and report['process_tree_reaped'] is True
           and report['source_runtime_unchanged'] is True and report['copied_inputs_unchanged'] is True,
           'Incomplete actual execution/input/runtime closeout')
    P.need(sha(log_path) == report['log_sha256'], 'Actual log bytes differ from execution receipt')
    selected = [x for x in plan['cases'] if x['name'] == report['case']]
    P.need(len(selected) == 1, 'Native case differs from expected membership')
    case = selected[0]; policy = plan['protocol']['manual_solver']
    P.need(report['mesh'] in policy['mesh_ladder'], 'Undeclared actual mesh')
    expected_argv = ['/solver/runtime/bin/FasterCap', '-b', 'geometry.lst', '-g',
                     '-m' + report['mesh'], '-t' + policy['gmres_tolerance'], '-d' + policy['interaction_ratio']]
    P.need(report['argv'] == expected_argv, 'Actual solver argv differs')
    numeric = P.parse_manual_log(log_path.read_text(), case['matrix_names'], report['mesh'],
                                 policy['gmres_tolerance'], policy['interaction_ratio'])
    scale = P.number(case['coordinate_unit_m'])
    numeric['matrix_F'] = [[str(P.number(x) * scale) for x in row] for row in numeric['matrix']]
    P.need(numeric == report['numeric'], 'Independent log/numeric readback differs')
    return {'case': case, 'numeric': numeric, 'report_sha256': sha(report_path),
            'log_sha256': sha(log_path), 'directory': str(directory)}


def reference_stability(plan, reference):
    protocol = plan['protocol']; policy = protocol['reference']; acceptance = protocol['acceptance']
    P.need(reference['schema'] == 'pinwheel.streaming-8x4-rc-reference-execution.v1'
           and reference['passed'] is True and reference['inputs_unchanged'] is True
           and reference['qualified'] is False, 'Independent reference execution did not close')
    expected = ['w' + width + '-h' + step + '-E' + extent for width in ('0.16', '0.32')
                for step in policy['mesh_steps_um'] for extent in policy['domain_extents_um']]
    P.need([row['case_id'] for row in reference['cases']] == expected, 'Independent reference membership differs')
    rows = {}
    for row in reference['cases']:
        match = re.fullmatch(r'w(0\.(?:16|32))-h(0\.0[24])-E(16|32)', row['case_id'])
        P.need(match is not None, 'Unexpected reference case ID')
        width, step, extent = match.groups()
        g = protocol['geometry']
        P.need(all(P.number(str(row[key])) == P.number(value) for key, value in
                   [('width_um', width), ('mesh_step_um', step), ('extent_um', extent),
                    ('gap_um', g['gap_um']), ('thickness_um', g['thickness_um'])]),
               'Reference actual geometry differs from its declared case ID')
        P.need([[P.number(str(v)) for v in layer] for layer in row['epsilon_layers']] ==
               [[P.number(v) for v in layer] for layer in policy['epsilon_layers']],
               'Reference dielectric differs from the declared material')
        P.need(row['qualified'] is False and row['continuum_error_enclosure'] is False,
               'Reference silently promoted to a continuum enclosure')
        P.need(P.number(str(row['true_residual_relative'])) <= P.number(policy['residual_relative_tolerance']),
               'Reference actual residual exceeds tolerance')
        P.need(P.number(str(row['energy_flux_relative_error'])) <= Decimal('1e-7'),
               'Reference flux/energy closure failed')
        P.need(row['nodes'] <= policy['maximum_nodes'] and row['cg_iterations'] <= policy['maximum_cg_iterations'],
               'Reference numerical allowance differs')
        rows[row['case_id']] = row
    result = {}
    for width in ('0.16', '0.32'):
        def c(step, extent):
            return rows['w' + width + '-h' + step + '-E' + extent]['capacitance_per_length_F_per_m']
        mesh = relative(c('0.04', '32'), c('0.02', '32'))
        domain = relative(c('0.02', '16'), c('0.02', '32'))
        P.need(mesh <= P.number(acceptance['maximum_reference_mesh_change']), 'Independent reference mesh stability failed')
        P.need(domain <= P.number(acceptance['maximum_reference_domain_change']), 'Independent reference domain stability failed')
        result[width] = {'reference_F_per_m': str(c('0.02', '32')),
                         'mesh_relative_change': str(mesh), 'domain_relative_change': str(domain)}
    return result


def analyze(plan, plan_hash, directories, reference):
    P.validate_protocol(plan['protocol'])
    P.need(reference['plan_sha256'] == plan_hash, 'Independent reference has wrong frozen plan')
    P.need(all(reference['producer_sha256'].get(name) == plan['producers_sha256'][name]
               for name in ('streaming_8x4_rc_protocol.py', 'streaming_8x4_rc_reference.py')),
           'Independent reference producer identities differ')
    expected = [x['name'] for x in plan['cases']]
    groups = {name: {} for name in expected}
    for directory in directories:
        row = read_native(plan, plan_hash, directory)
        name, mesh = row['case']['name'], row['numeric']['mesh']
        P.need(mesh not in groups[name], 'Duplicate actual case/mesh; no cherry-picked replicate allowed')
        groups[name][mesh] = row
    accepted = {}
    ladder = plan['protocol']['manual_solver']['mesh_ladder']
    for case in plan['cases']:
        name = case['name']; group = groups[name]
        P.need(group, 'Missing native case: ' + name)
        selected = [group[mesh] for mesh in ladder if mesh in group]
        stable = P.admit_mesh_sequence(plan['protocol'], [row['numeric'] for row in selected])
        accepted[name] = {'last': selected[-1], 'stability': stable}
    refs = reference_stability(plan, reference)
    bound = plan['protocol']['acceptance']
    comparison = {}
    for width in ('0.16', '0.32'):
        def cap(length, margin):
            name = 'wire_w' + width.replace('.', 'p') + '_L' + length + '_M' + margin
            return P.number(accepted[name]['last']['numeric']['matrix_F'][1][1])
        first_slope = (cap('20', '20') - cap('10', '20')) / Decimal('0.00001')
        second_slope = (cap('30', '20') - cap('20', '20')) / Decimal('0.00001')
        extended_slope = (cap('30', '30') - cap('20', '30')) / Decimal('0.00001')
        length_change = relative(first_slope, second_slope)
        extension_change = relative(extended_slope, second_slope)
        error = relative(second_slope, refs[width]['reference_F_per_m'])
        P.need(length_change <= P.number(bound['maximum_length_slope_change']), 'Finite-wire length-slope stability failed')
        P.need(extension_change <= P.number(bound['maximum_native_ground_extension_change']), 'Native ground-extension sensitivity failed')
        P.need(error <= P.number(bound['maximum_independent_reference_relative_error']), 'Independent finite-wire reference comparison failed')
        comparison[width] = {'native_F_per_m': str(second_slope), 'reference': refs[width],
                             'length_slope_relative_change': str(length_change),
                             'ground_extension_relative_change': str(extension_change),
                             'independent_reference_relative_error': str(error)}
    return {'schema': 'pinwheel.streaming-8x4-rc-pilot-analysis.v1',
            'uniform_finite_wire_pilot_passed': True, 'qualified': False,
            'rc_model_qualified': False, 'draft_model_promoted': False,
            'plan_sha256': plan_hash,
            'native_cases': {name: {'stability': row['stability'],
                                   'last_report_sha256': row['last']['report_sha256']}
                             for name, row in accepted.items()},
            'comparison': comparison,
            'limits': plan['protocol']['limits'],
            'resource_cleanup_join': 'separate campaign-owner obligation; this is log/numerical readback only'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--plan-sha256', required=True)
    parser.add_argument('--native', type=Path, action='append', required=True)
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    P.need(sha(args.plan) == args.plan_sha256, 'Frozen plan hash differs')
    report = {'schema': 'pinwheel.streaming-8x4-rc-pilot-analysis.v1', 'uniform_finite_wire_pilot_passed': False,
              'qualified': False, 'rc_model_qualified': False, 'draft_model_promoted': False}
    try:
        report = analyze(json.loads(args.plan.read_text()), args.plan_sha256, args.native,
                         json.loads(args.reference.read_text()))
    except (ValueError, KeyError, TypeError) as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    P.need(not args.output.exists() and args.output.parent.is_dir(), 'Analysis output must be fresh')
    args.output.write_bytes(P.canonical(report) + b'\n')
    print(json.dumps(report, indent=2))
    return 0 if report['uniform_finite_wire_pilot_passed'] else 2


if __name__ == '__main__':
    raise SystemExit(main())
