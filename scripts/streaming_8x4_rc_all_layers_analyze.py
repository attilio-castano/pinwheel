"""Independent raw-file HOST readback of a closed nominal all-layer batch.

This starts no solver. Complete case, mesh, excitation and prerequisite
membership is mandatory. A passing batch never qualifies the CMOS5L model.
"""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_all_layers_plan as A
import streaming_8x4_rc_all_layers_execute as W
import streaming_8x4_rc_layered_analyze as H
import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_execute as E


def read_report(directory, plan_hash, batch, kind, prerequisites):
    report = json.loads((directory / 'report.json').read_text())
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-all-layers-' + kind + '-execution.v1'
           and report['plan_sha256'] == plan_hash and report['batch'] == batch
           and report['declared_case_names'] == A.BATCHES[batch]
           and report['prerequisites'] == prerequisites and report['passed'] is True
           and report['qualified'] is False and report['model_qualified'] is False
           and report['inputs_prerequisites_unchanged'] is True,
           'All-layer closed batch identity/prerequisite/scope differs')
    return report


def read_reference(plan, plan_hash, batch, directory, prerequisites):
    report = read_report(directory, plan_hash, batch, 'reference', prerequisites)
    cases = [c for c in plan['cases'] if c['batch'] == batch]; policy = plan['protocol']
    expected = [(c['name'], h, e) for c in cases for h in policy['reference_mesh_steps_um']
                for e in policy['reference_domain_extents_um']]
    P.need([(j['case'], j['step'], j['extent']) for j in report['jobs']] == expected,
           'Reference raw-job membership/order differs')
    leaves = []
    for index, job in enumerate(report['jobs']):
        path = directory / ('case-' + str(index).zfill(3) + '.json'); log = path.with_name(path.name + '.log')
        P.need(type(job['exit_code']) is int and job['exit_code'] == 0
               and job['process_tree_reaped'] is True and E.sha(path) == job['output_sha256']
               and E.sha(log) == job['log_sha256'] and log.read_bytes() == b'',
               'Reference raw file/exit/warning/reap differs')
        leaf = json.loads(path.read_text())
        P.need((leaf['case'], leaf['step'], leaf['extent']) == (job['case'], job['step'], job['extent']),
               'Reference leaf differs from declared job')
        leaves.append(leaf)
    recomputed = W.reference_analysis(plan, plan_hash, batch, leaves)
    P.need(recomputed == report['analysis'] and recomputed['passed'] is True,
           'Independent reference convergence analysis differs/fails')
    return report, leaves


def read_native(plan, plan_hash, case, expected_mesh, directory, geometry, runtime):
    report = json.loads((directory / 'report.json').read_text()); log = directory / 'native.log'
    P.need(report.get('mesh') == expected_mesh, 'Native leaf mesh differs from batch job')
    P.need(report['schema'] == 'pinwheel.streaming-8x4-rc-all-layers-native-leaf.v1'
           and report['plan_sha256'] == plan_hash and report['case'] == case['name']
           and report['passed'] is True and report['qualified'] is False and report['model_qualified'] is False,
           'Native leaf identity/scope differs')
    P.need(type(report['exit_code']) is int and report['exit_code'] == 0 and report['timed_out'] is False
           and all(report[k] is True for k in ('solver_executed', 'process_tree_reaped',
                       'source_runtime_unchanged', 'copied_inputs_unchanged')),
           'Native solver exit/reaping/input/runtime gate failed')
    P.need(E.sha(log) == report['log_sha256'] and E.tree(directory / 'work') == case['files']
           and E.tree(geometry / case['name']) == case['files'] and E.tree(runtime) == plan['runtime'],
           'Native raw/copied/source/runtime bytes differ')
    p = plan['protocol']; mesh = report['mesh']
    P.need(mesh in p['native_mesh_ladder'] and report['argv'] == [
        '/solver/runtime/bin/FasterCap', '-b', 'geometry.lst', '-g', '-m' + mesh,
        '-t' + p['native_gmres_tolerance'], '-d' + p['native_interaction_ratio']], 'Native actual argv differs')
    numeric = P.parse_manual_log(log.read_text(), case['matrix_names'], mesh,
                                 p['native_gmres_tolerance'], p['native_interaction_ratio'])
    P.need(case['coordinate_unit_m'] == p['native_coordinate_unit_m'] == '0.00000095367431640625',
           'Native exact fixed S20 unit differs')
    numeric['matrix_F'] = [[str(P.number(x) * P.number(case['coordinate_unit_m'])) for x in r] for r in numeric['matrix']]
    P.need(numeric == report['numeric'], 'Independent Native numeric/unit readback differs')
    unit = H.check_unit_witness(geometry, case['name'])
    return numeric, unit


def analyze(plan_path, plan_hash, batch, native_directory, reference_directory, runtime,
            m1_report, m1_hash, prior_report=None, prior_hash=None):
    plan = W.verify(plan_path, plan_hash); root = plan_path.parent; p = plan['protocol']
    pre = W.prerequisites(plan, plan_hash, batch, m1_report, m1_hash, prior_report, prior_hash)
    reference_report, leaves = read_reference(plan, plan_hash, batch, reference_directory, pre)
    native_report = read_report(native_directory, plan_hash, batch, 'native', pre)
    definitions = [c for c in plan['geometry_cases'] if c['batch'] == batch]
    expected = [(c['name'], mesh) for c in definitions for mesh in p['native_mesh_ladder']]
    P.need([(j['case'], j['mesh']) for j in native_report['jobs']] == expected,
           'Incomplete/reordered Native batch mesh/case membership')
    by_name = {c['name']: c for c in definitions}; groups = {name: [] for name in by_name}; units = []
    for index, job in enumerate(native_report['jobs']):
        directory = native_directory / ('job-' + str(index).zfill(3))
        P.need(job['passed'] is True and E.sha(directory / 'report.json') == job['report_sha256'],
               'Native batch/raw leaf receipt differs')
        numeric, unit = read_native(plan, plan_hash, by_name[job['case']], job['mesh'],
                                    directory, root / 'geometry', runtime)
        groups[job['case']].append(numeric); units.append(dict(name=job['case'], mesh=job['mesh'], **unit))
    accepted = {}; meshes = []
    for case in definitions:
        rows = groups[case['name']]
        changes = [P.cellwise_change(a, b) for a, b in zip(rows, rows[1:])]
        P.need(len(rows) == 5 and len(changes) == 4
               and all(x <= P.number(p['maximum_successive_BEM_matrix_change']) for x in changes[-2:]),
               'All-layer two-successive complete-matrix mesh gate failed: ' + case['name'])
        accepted[case['name']] = [r[1:] for r in rows[-1]['matrix_F'][1:]]
        meshes.append({'name': case['name'], 'successive_complete_matrix_changes': list(map(str, changes)), 'passed': True})
    comparisons = []
    for case in [c for c in plan['cases'] if c['batch'] == batch]:
        finite = {(c['length_um'], c['extension_um']): accepted[c['name']] for c in definitions if c['case'] == case['name']}
        P.need(set(finite) == set(A.LENGTH_EXTENSIONS), 'Length/ground-extension membership differs')
        fine = next(x['row'] for x in leaves if x['case'] == case['name'] and x['step'] == '.02' and x['extent'] == '32')
        result = H.compare_case(p, [r['name'] for r in case['rectangles']], finite, fine['matrix_F_per_m'])
        comparisons.append(dict(name=case['name'], role=case['role'], **result))
    W.verify(plan_path, plan_hash); W.prerequisites(plan, plan_hash, batch, m1_report, m1_hash, prior_report, prior_hash)
    passed = all(r['passed'] for r in comparisons)
    return {'schema': 'pinwheel.streaming-8x4-rc-all-layers-independent-readback.v1',
            'qualified': False, 'model_qualified': False, 'continuum_error_enclosure': False,
            'limited_batch_passed': passed, 'plan_sha256': plan_hash, 'batch': batch,
            'declared_case_names': A.BATCHES[batch], 'prerequisites': pre,
            'all_eight_new_nominal_cases_closed': passed and batch == 'remaining3',
            'reference_report_sha256': E.sha(reference_directory / 'report.json'),
            'native_report_sha256': E.sha(native_directory / 'report.json'),
            'reference_analysis': reference_report['analysis'], 'mesh_results': meshes,
            'unit_readbacks': units, 'comparisons': comparisons,
            'scope': plan['scope']}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('plan', 'native-directory', 'reference-directory', 'runtime', 'm1-pass-report', 'output'):
        p.add_argument('--' + name, type=Path, required=True)
    for name in ('plan-sha256', 'm1-pass-sha256', 'batch'):
        p.add_argument('--' + name, required=True)
    p.add_argument('--prior-batch-report', type=Path); p.add_argument('--prior-batch-sha256')
    a = p.parse_args(); P.need(not a.output.exists() and a.output.parent.is_dir(), 'Independent readback owner must be fresh')
    result = analyze(a.plan, a.plan_sha256, a.batch, a.native_directory, a.reference_directory,
                     a.runtime, a.m1_pass_report, a.m1_pass_sha256, a.prior_batch_report, a.prior_batch_sha256)
    E.write(a.output, result); print(json.dumps(result, indent=2))
    if not result['limited_batch_passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
