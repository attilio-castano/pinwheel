"""Independent HOST readback of the limited layered M1 experiment.

Reparse retained native logs, check complete immutable case membership and
recompute reference/mesh/length/domain comparisons. Never promote a full model.
No numerical field solve or subprocess is started by this module.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import struct
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_execute as E
import streaming_8x4_rc_layered_run as R


def flat(matrix):
    return [x for row in matrix for x in row] + [sum(row) for row in matrix]


def change(a, b):
    P.need(len(a) == len(b) and a and all(y != 0 for y in b), 'Invalid complete cellwise comparison')
    return max(abs(x - y) / abs(y) for x, y in zip(a, b))


def difference(a, b, length_m):
    P.need(len(a) == len(b) and all(len(x) == len(a) for x in a + b), 'Slope matrix dimensions differ')
    return [[(x - y) / length_m for x, y in zip(arow, brow)] for arow, brow in zip(a, b)]


def check_unit_witness(geometry, case_name):
    """Reparse both retained SI bytes and emitted S20 bytes independently."""
    manifest = json.loads((geometry / 'manifest.json').read_text())
    original = Path(manifest['physical_SI_source_owner'])
    P.need(original.resolve().is_relative_to(geometry.parent.resolve())
           and E.sha(original / 'manifest.json') == manifest['physical_source_manifest_sha256'],
           'Retained SI geometry authority differs/escapes campaign')
    directory = geometry / case_name; old_directory = original / case_name
    unit = json.loads((directory / 'unit-map.json').read_text())
    P.need(unit['S'] == 1048576 and P.number(unit['coordinate_unit_m']) == P.number('0.00000095367431640625')
           and unit['exact_binary32_coordinate_scaling'] is True
           and unit['capacitance_physical_F_equals_raw_times_coordinate_unit_m'] is True,
           'Wrong exact S20 unit policy')
    def binary(token):
        return Fraction.from_float(struct.unpack('>f', struct.pack('>f', float(token)))[0])
    witnesses = []
    P.need(set(unit['SI_files_sha256']) == set(unit['emitted_files_sha256']), 'S20 unit file membership differs')
    for name in unit['SI_files_sha256']:
        old, new = old_directory / name, directory / name
        P.need(Path(name).name == name and not old.is_symlink() and not new.is_symlink()
               and E.sha(old) == unit['SI_files_sha256'][name]
               and E.sha(new) == unit['emitted_files_sha256'][name], 'SI/emitted unit witness file bytes differ')
        before, after = old.read_text().splitlines(), new.read_text().splitlines()
        P.need(len(before) == len(after), 'SI/S20 line membership differs')
        for line_number, (a, b) in enumerate(zip(before, after), 1):
            source, emitted = a.split(), b.split()
            if source and source[0] in ('Q', 'D'):
                indices = list(range(2, 14)) if source[0] == 'Q' else list(range(7, 10))
                P.need(len(source) == len(emitted) == (14 if source[0] == 'Q' else 10)
                       and all(source[i] == emitted[i] for i in range(len(source)) if i not in indices),
                       'S20 material/name/noncoordinate fields changed')
                physical = [binary(source[i]) for i in indices]
                raw = [binary(emitted[i]) for i in indices]
                P.need(physical == [x / 1048576 for x in raw], 'Emitted S20 coordinates change physical SI geometry')
                witnesses.append(dict(file=name, line=line_number, SI_m=list(map(str, physical)),
                                      emitted_coordinate=list(map(str, raw)), source_parser_binary32_roundtrip_exact=True))
            else:
                P.need(b == a.replace('coordinates SI meters', 'raw coordinates=2**20 * SI metres'),
                       'S20 noncoordinate line changed')
    P.need(witnesses == unit['all_coordinate_and_reference_witnesses'], 'Missing/extra/reordered coordinate unit witness')
    return {'coordinate_unit_m': unit['coordinate_unit_m'], 'coordinate_witness_rows': len(witnesses),
            'retained_SI_and_emitted_S20_readback_exact': True, 'unit_map_sha256': E.sha(directory / 'unit-map.json')}


def read_reference(reference_plan, reference_hash, directory):
    plan = R.verify(reference_plan, reference_hash)
    report = json.loads((directory / 'report.json').read_text())
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-layered-reference-execution.v1'
           and report['plan_sha256'] == reference_hash and report['passed'] is True
           and report['qualified'] is False and report['model_qualified'] is False
           and report['inputs_unchanged'] is True and len(report['jobs']) == 25,
           'Layered reference execution did not close')
    decoded = []; uniform = None
    for index, job in enumerate(report['jobs']):
        prefix = 'uniform-' if job['uniform_control'] else ''
        path = directory / (prefix + f'case-{index:03}.json'); log = path.with_name(path.name + '.log')
        P.need(type(job['exit_code']) is int and job['exit_code'] == 0 and job['process_tree_reaped'] is True
               and E.sha(path) == job['output_sha256'] and E.sha(log) == job['log_sha256']
               and log.read_bytes() == b'', 'Independent reference raw case/exit/reap differs')
        row = json.loads(path.read_text())
        P.need(row['plan_sha256'] == reference_hash and row['case_id'] == job['case'], 'Reference case binding differs')
        row['declared_mesh'] = job['step']; row['declared_extent'] = job['extent']
        if job['uniform_control']:
            P.need(index == 24 and uniform is None, 'Uniform control membership differs')
            uniform = row
        else:
            decoded.append(row)
    P.need(decoded == report['cases'] and uniform == report['uniform_control'], 'Reference aggregate differs from raw case files')
    recomputed = R.analyze(plan, decoded, uniform, reference_hash)
    P.need(recomputed == report['analysis'] and recomputed['passed'] is True, 'Independent reference aggregate analysis differs')
    return plan, report


def read_native(plan, plan_hash, row, expected_mesh, directory, geometry, runtime):
    report_path, log = directory / 'report.json', directory / 'native.log'
    report = json.loads(report_path.read_text())
    P.need(report.get('mesh') == expected_mesh, 'Native leaf mesh differs from its declared batch job')
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-layered-native-execution.v1'
           and report['plan_sha256'] == plan_hash and report['case'] == row['name']
           and report['passed'] is True and report['qualified'] is False and report['model_qualified'] is False,
           'Layered Native receipt binding/promotion differs')
    P.need(type(report['exit_code']) is int and report['exit_code'] == 0
           and report['timed_out'] is False and all(report[k] is True for k in
               ('solver_executed', 'process_tree_reaped', 'source_runtime_unchanged',
                'copied_inputs_unchanged', 'producer_plan_unchanged')), 'Layered Native execution did not close')
    P.need(E.sha(log) == report['log_sha256'] and E.tree(directory / 'work') == row['files']
           and E.tree(geometry / row['name']) == row['files'] and E.tree(runtime) == plan['runtime'],
           'Layered Native log/copied/source/runtime bytes differ')
    mesh = report['mesh']; policy = plan['protocol']
    P.need(mesh in policy['native_mesh_ladder'] and report['argv'] == [
        '/solver/runtime/bin/FasterCap', '-b', 'geometry.lst', '-g', '-m' + mesh,
        '-t' + policy['native_gmres_tolerance'], '-d' + policy['native_interaction_ratio']], 'Actual layered argv differs')
    numeric = P.parse_manual_log(log.read_text(), row['matrix_names'], mesh,
                                 policy['native_gmres_tolerance'], policy['native_interaction_ratio'])
    scale = P.number(row['coordinate_unit_m'])
    numeric['matrix_F'] = [[str(P.number(x) * scale) for x in vector] for vector in numeric['matrix']]
    P.need(numeric == report['numeric'] and row['coordinate_unit_m'] == '0.00000095367431640625'
           and row['coordinate_unit_m'] == plan['protocol']['native_coordinate_unit_m'],
           'Independent Native numeric/unit readback differs')
    check_unit_witness(geometry, row['name'])
    return numeric


def compare_case(policy, names, finite, reference):
    def get(length, extension):
        return [[P.number(x) for x in row] for row in finite[length, extension]]
    slopes = [difference(get('20', '20'), get('10', '20'), P.number('.00001')),
              difference(get('30', '20'), get('20', '20'), P.number('.00001'))]
    extended = difference(get('30', '30'), get('20', '30'), P.number('.00001'))
    for matrix in slopes + [extended]:
        P.matrix_physics(names, matrix)
    reference = [[P.number(str(x)) for x in row] for row in reference]
    slope_error = change(flat(slopes[0]), flat(slopes[1]))
    boundary_error = change(flat(slopes[1]), flat(extended))
    errors = [change(flat(matrix), flat(reference)) for matrix in slopes + [extended]]
    return {'length_slope_relative_difference': str(slope_error),
            'ground_extension_relative_difference': str(boundary_error),
            'BEM_reference_relative_differences': list(map(str, errors)),
            'slope_matrices_F_per_m': [[[str(x) for x in row] for row in matrix] for matrix in slopes + [extended]],
            'passed': slope_error <= P.number(policy['maximum_length_slope_difference'])
                      and boundary_error <= P.number(policy['maximum_ground_extension_difference'])
                      and max(errors) <= P.number(policy['maximum_BEM_reference_difference'])}


def analyze(native_plan, plan_hash, batch, geometry, runtime, reference_plan, reference_directory):
    P.need(E.sha(native_plan) == plan_hash, 'Native layered plan hash differs')
    plan = json.loads(native_plan.read_text()); ref_hash = plan['reference_plan_sha256']
    reference, reference_report = read_reference(reference_plan, ref_hash, reference_directory)
    for name, value in plan['producers_sha256'].items():
        P.need(E.sha(Path(__file__).with_name(name)) == value, 'Layered producer bytes differ')
    P.need(E.sha(geometry / 'manifest.json') == plan['geometry_manifest_sha256'], 'Layered geometry manifest differs')
    batch_report = json.loads((batch / 'report.json').read_text()); policy = plan['protocol']
    P.need(batch_report['schema'] == 'pinwheel.streaming-8x4-rc-layered-native-batch.v1'
           and batch_report['plan_sha256'] == plan_hash and batch_report['passed'] is True
           and batch_report['qualified'] is False and batch_report['model_qualified'] is False
           and batch_report['full_declared_membership'] is True
           and batch_report['selected_cases'] == [c['name'] for c in plan['cases']]
           and batch_report['selected_meshes'] == policy['native_mesh_ladder'], 'Incomplete layered Native batch')
    expected = [(c['name'], m) for c in plan['cases'] for m in policy['native_mesh_ladder']]
    P.need([(j['case'], j['mesh']) for j in batch_report['jobs']] == expected, 'Layered Native expected membership differs')
    groups = {c['name']: [] for c in plan['cases']}; definitions = {c['name']: c for c in plan['cases']}
    for index, job in enumerate(batch_report['jobs']):
        directory = batch / ('job-' + str(index).zfill(3))
        P.need(job['passed'] is True and E.sha(directory / 'report.json') == job['report_sha256'], 'Native batch/raw receipt differs')
        groups[job['case']].append(read_native(plan, plan_hash, definitions[job['case']], job['mesh'], directory, geometry, runtime))
    accepted = {}; mesh_results = []
    for case in plan['cases']:
        rows = groups[case['name']]
        changes = [P.cellwise_change(a, b) for a, b in zip(rows, rows[1:])]
        stable = all(x <= P.number(policy['maximum_successive_BEM_matrix_change']) for x in changes[-2:])
        P.need(len(rows) == 5 and stable, 'Layered Native two-successive mesh gate failed: ' + case['name'])
        matrix = rows[-1]['matrix_F']; accepted[case['name']] = [row[1:] for row in matrix[1:]]
        mesh_results.append({'name': case['name'], 'successive_complete_matrix_changes': list(map(str, changes)), 'passed': stable})
    comparisons = []
    fine_refs = {(r['case_id']): r for r in reference_report['cases'] if r['declared_mesh'] == '.02' and r['declared_extent'] == '32'}
    for case in reference['cases']:
        finite = {(c['length_um'], c['extension_um']): accepted[c['name']] for c in plan['cases'] if c['case'] == case['name']}
        result = compare_case(policy, [r['name'] for r in case['rectangles']], finite, fine_refs[case['name']]['matrix_F_per_m'])
        comparisons.append(dict(name=case['name'], role=case['role'], **result))
    return {'schema': 'pinwheel.streaming-8x4-rc-layered-independent-readback.v1', 'qualified': False,
            'model_qualified': False, 'continuum_error_enclosure': False,
            'limited_layered_M1_pilot_passed': all(r['passed'] for r in comparisons),
            'native_plan_sha256': plan_hash, 'reference_plan_sha256': ref_hash,
            'batch_report_sha256': E.sha(batch / 'report.json'),
            'reference_report_sha256': E.sha(reference_directory / 'report.json'),
            'mesh_results': mesh_results, 'comparisons': comparisons,
            'scope': 'M1 self/lateral two-wire C at the explicitly declared ITF cases only; full eight-field extraction coverage remains incomplete'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('native-plan', 'batch', 'geometry', 'runtime', 'reference-plan', 'reference-directory', 'output'):
        p.add_argument('--' + name, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    P.need(not a.output.exists() and a.output.parent.is_dir(), 'Layered readback output must be fresh')
    result = analyze(a.native_plan, a.plan_sha256, a.batch, a.geometry, a.runtime, a.reference_plan, a.reference_directory)
    a.output.write_text(json.dumps(result, indent=2) + '\n'); print(json.dumps(result, indent=2))
    if not result['limited_layered_M1_pilot_passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
