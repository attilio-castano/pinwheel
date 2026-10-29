"""Separately typed bounded all-layer workers; Root owns all Native admission.

Only complete first5 or remaining3 batches are supported. A closed full M1
independent pass is mandatory; remaining3 additionally needs the closed first5
independent pass from this exact universe. No solve occurs at import/verification.
"""
import argparse
import json
import math
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_all_layers_plan as A
import streaming_8x4_rc_all_layers_reference as F
import streaming_8x4_rc_layered_run as M
import streaming_8x4_rc_execute as E
import streaming_8x4_rc_protocol as P


def verify(path, expected_hash):
    P.need(E.sha(path) == expected_hash, 'All-layer universe plan hash differs')
    plan = json.loads(path.read_text()); root = path.parent
    P.need(plan['schema'] == A.SCHEMA and plan['qualified'] is False and plan['model_qualified'] is False,
           'All-layer typed scope/promotion differs')
    for name, value in plan['producer_sha256'].items():
        P.need(E.sha(Path(__file__).with_name(name)) == value, 'All-layer/frozen M1 producer bytes differ')
    P.need(E.sha(root / 'baseline-M1/reference-plan.json') == A.M1_REFERENCE_HASH
           and E.sha(root / 'baseline-M1/native-plan.json') == A.M1_NATIVE_HASH
           and plan['M1_reference_plan_sha256'] == A.M1_REFERENCE_HASH
           and plan['M1_native_plan_sha256'] == A.M1_NATIVE_HASH, 'Frozen M1 prerequisite plans differ')
    baseline = json.loads((root / 'baseline-M1/native-plan.json').read_text())['protocol']
    changed = {'maximum_reference_nodes', 'reference_resources', 'native_resources',
               'material_geometry_convention', 'process_corner_scope'}
    P.need(set(plan['protocol']) == set(baseline)
           and all(plan['protocol'][key] == value for key, value in baseline.items() if key not in changed)
           and plan['protocol']['maximum_reference_nodes'] == 65000, 'All-layer equations/tolerance policy changed')
    for kind, memory, scratch, calls in (('reference', 2147483648, 134217728, 32),
                                         ('native', 6442450944, 536870912, 200)):
        resource = plan['protocol'][kind + '_resources']
        P.need(resource['cpus'] == 1 and resource['memory_bytes'] == memory
               and resource['seconds_per_call'] == 120 and resource['work_seconds'] == 1800
               and resource['outer_seconds'] == 1860 and resource['scratch_bytes'] == scratch
               and resource['maximum_calls'] == calls and resource['root_go_required'] is True,
               'All-layer resource policy differs')
    P.need(E.sha(root / 'itf-typ.txt') == plan['ITF_TYP_sha256'], 'All-layer exact ITF bytes differ')
    cases = A.case_universe(A.P.parse_stack((root / 'itf-typ.txt').read_text()))
    P.need(plan['cases'] == cases and {b: r['case_names'] for b, r in plan['batches'].items()} == A.BATCHES,
           'Frozen eight-case universe/batch membership differs')
    grids = A.grid_inventory(cases)
    P.need(plan['grid_inventory'] == grids and all(
        row['all_case_grids_within_node_admission'] == all(g['within_reviewed_65000_node_cap'] for g in grids if g['batch'] == batch)
        and row['reference_calls'] == 4 * len(A.BATCHES[batch])
        and row['native_calls'] == 25 * len(A.BATCHES[batch]) for batch, row in plan['batches'].items()),
        'All-layer dry grid/batch admission differs')
    P.need(plan['reference_structural_storage_admission'] == A.reference_storage_budget(),
           'Reference source/storage admission differs')
    P.need(E.sha(root / 'geometry/manifest.json') == plan['geometry_manifest_sha256']
           and E.sha(root / 'physical-SI/manifest.json') == plan['physical_SI_manifest_sha256'],
           'All-layer geometry/SI authority differs')
    verify_geometry(plan, root)
    P.need(A.operator_derivation() == plan['FVM_derivation'], 'Byte-identified FVM operator adaptation differs')
    return plan


def verify_geometry(plan, root):
    expected = [(c['name'] + '-L' + length + '-E' + extension, c['name'], c['batch'], length, extension)
                for c in plan['cases'] for length, extension in A.LENGTH_EXTENSIONS]
    rows = plan['geometry_cases']
    P.need([(c['name'], c['case'], c['batch'], c['length_um'], c['extension_um']) for c in rows] == expected,
           'Exact forty-case geometry universe differs')
    geometry = json.loads((root / 'geometry/manifest.json').read_text())
    physical = json.loads((root / 'physical-SI/manifest.json').read_text())
    P.need(geometry['cases'] == rows and [r['case'] for r in physical['cases']] == [r[0] for r in expected],
           'Geometry/SI manifest exact membership differs')
    definitions = {c['name']: c for c in plan['cases']}
    for row, si in zip(rows, physical['cases']):
        names = ['GND_SUB'] + [r['name'] for r in definitions[row['case']]['rectangles']]
        P.need(row['matrix_names'] == ['g' + str(i + 1) + '_' + name for i, name in enumerate(names)]
               and row['coordinate_unit_m'] == '0.00000095367431640625'
               and E.tree(root / 'geometry' / row['name']) == row['files']
               and E.tree(root / 'physical-SI' / row['name']) == si['files'],
               'Declared geometry labels/unit/retained SI or emitted source tree differs')


def prerequisites(plan, plan_hash, batch, m1_path, m1_hash, prior_path=None, prior_hash=None):
    P.need(batch in A.BATCHES and E.sha(m1_path) == m1_hash, 'Missing/wrong full M1 prerequisite receipt')
    P.need(plan['batches'][batch]['all_case_grids_within_node_admission'] is True,
           'Complete declared batch exceeds reviewed reference node admission')
    m1 = json.loads(m1_path.read_text())
    P.need(m1['schema'] == 'pinwheel.streaming-8x4-rc-layered-independent-readback.v1'
           and m1['limited_layered_M1_pilot_passed'] is True and m1['qualified'] is False
           and m1['model_qualified'] is False and m1['continuum_error_enclosure'] is False
           and m1['native_plan_sha256'] == A.M1_NATIVE_HASH and m1['reference_plan_sha256'] == A.M1_REFERENCE_HASH,
           'A point/prefix/foreign M1 result cannot admit the all-layer follow-on')
    evidence = {'M1_report_sha256': m1_hash, 'M1_limited_complete_pass': True}
    if batch == 'remaining3':
        P.need(prior_path is not None and prior_hash is not None and E.sha(prior_path) == prior_hash,
               'Second all-layer batch requires closed first5 independent pass')
        prior = json.loads(prior_path.read_text())
        P.need(prior['schema'] == 'pinwheel.streaming-8x4-rc-all-layers-independent-readback.v1'
               and prior['batch'] == 'first5' and prior['plan_sha256'] == plan_hash
               and prior['limited_batch_passed'] is True and prior['model_qualified'] is False
               and prior['qualified'] is False and prior['declared_case_names'] == A.BATCHES['first5'],
               'Second batch prerequisite is incomplete/foreign/promoted')
        evidence['first5_report_sha256'] = prior_hash
    else:
        P.need(prior_path is None and prior_hash is None, 'Unexpected prior-batch prerequisite on first5')
    return evidence


def validate_reference_row(plan, plan_hash, case, row, step, extent):
    policy = plan['protocol']; names = [r['name'] for r in case['rectangles']]
    grid = next(g for g in plan['grid_inventory'] if (g['case'], g['step_um'], g['extent_um']) == (case['name'], step, extent))
    P.need(row['schema'] == 'pinwheel.streaming-8x4-rc-layered-reference.v1'
           and row['names'] == names
           and row['rectangles'] == [{'name': r['name'], 'bounds_um': [float(x) for x in r['bounds_um']]}
                                     for r in case['rectangles']]
           and row['epsilon_layers'] == [[float(x) for x in slab] for slab in case['epsilon_layers']]
           and row['mesh_step_um'] == float(step) and row['extent_um'] == float(extent)
           and row['qualified'] is False and row['continuum_error_enclosure'] is False,
           'All-layer reference actual geometry/material/scope differs')
    M.validate_excitation_membership(names, row['excitations'])
    P.need(type(row['nodes']) is int and row['nodes'] == grid['nodes'] <= 65000
           and type(row['unknown_nodes']) is int and 0 < row['unknown_nodes'] < row['nodes']
           and all(0 < e['cg_iterations'] <= policy['maximum_cg_iterations']
                   and math.isfinite(e['true_residual_relative'])
                   and 0 <= e['true_residual_relative'] <= float(policy['true_residual_relative_tolerance'])
                   and math.isfinite(e['energy_flux_relative_error'])
                   and 0 <= e['energy_flux_relative_error'] <= float(policy['energy_flux_relative_tolerance'])
                   for e in row['excitations']), 'All-layer reference numerical contract differs')
    matrix = row['matrix_F_per_m']
    P.matrix_physics(names, [[str(x) for x in r] for r in matrix],
                     asymmetry_limit=P.number(policy['reciprocity_relative_tolerance']))
    P.need(len(row['ground_C_F_per_m']) == len(names)
           and all(abs(sum(r) - g) <= 1e-12 * abs(g) for r, g in zip(matrix, row['ground_C_F_per_m']))
           and (row['coupling_C_F_per_m'] is None if len(names) == 1 else
                abs(row['coupling_C_F_per_m'] + matrix[0][1]) <= 1e-12 * abs(matrix[0][1])),
           'All-layer reference ground/coupling semantics differ')


def reference_analysis(plan, plan_hash, batch, leaves):
    cases = [c for c in plan['cases'] if c['name'] in A.BATCHES[batch]]; p = plan['protocol']
    expected = [(c['name'], h, e) for c in cases for h in p['reference_mesh_steps_um'] for e in p['reference_domain_extents_um']]
    P.need([(x['case'], x['step'], x['extent']) for x in leaves] == expected, 'Incomplete reference batch membership/order')
    groups = {}
    for leaf in leaves:
        P.need(leaf['schema'] == 'pinwheel.streaming-8x4-rc-all-layers-reference-leaf.v1'
               and leaf['plan_sha256'] == plan_hash and leaf['batch'] == batch
               and leaf['qualified'] is False and leaf['model_qualified'] is False,
               'Reference leaf plan/batch/type differs')
        case = next(c for c in cases if c['name'] == leaf['case'])
        validate_reference_row(plan, plan_hash, case, leaf['row'], leaf['step'], leaf['extent'])
        groups[leaf['case'], leaf['step'], leaf['extent']] = leaf['row']
    results = []
    for case in cases:
        fine = groups[case['name'], '.02', '32']
        mesh = M.relative_change(M.flatten(groups[case['name'], '.04', '32']), M.flatten(fine))
        domain = M.relative_change(M.flatten(groups[case['name'], '.02', '16']), M.flatten(fine))
        results.append({'name': case['name'], 'fine_matrix_F_per_m': fine['matrix_F_per_m'],
                        'fine_ground_C_F_per_m': fine['ground_C_F_per_m'],
                        'fine_coupling_C_F_per_m': fine['coupling_C_F_per_m'],
                        'mesh_relative_change': mesh, 'domain_relative_change': domain,
                        'passed': mesh <= float(p['maximum_reference_mesh_change'])
                                  and domain <= float(p['maximum_reference_domain_change'])})
    return {'cases': results, 'passed': all(r['passed'] for r in results), 'model_qualified': False}


def reference_leaf(args):
    path = Path(args.plan); plan = verify(path, args.plan_sha256)
    prerequisites(plan, args.plan_sha256, args.batch, Path(args.m1_pass_report), args.m1_pass_sha256,
                  Path(args.prior_batch_report) if args.prior_batch_report else None, args.prior_batch_sha256)
    M.cgroups(); case = next((c for c in plan['cases'] if c['name'] == args.case), None)
    P.need(case and case['name'] in A.BATCHES[args.batch]
           and args.step in plan['protocol']['reference_mesh_steps_um']
           and args.extent in plan['protocol']['reference_domain_extents_um'], 'Undeclared reference leaf selection')
    row = F.solve([{'name': r['name'], 'bounds_um': [float(x) for x in r['bounds_um']]} for r in case['rectangles']],
                  [[float(x) for x in slab] for slab in case['epsilon_layers']], float(args.extent), float(args.step),
                  tolerance=float(plan['protocol']['true_residual_relative_tolerance']),
                  maximum_iterations=plan['protocol']['maximum_cg_iterations'], maximum_nodes=65000)
    validate_reference_row(plan, args.plan_sha256, case, row, args.step, args.extent)
    result = {'schema': 'pinwheel.streaming-8x4-rc-all-layers-reference-leaf.v1', 'qualified': False, 'model_qualified': False,
              'plan_sha256': args.plan_sha256, 'batch': args.batch, 'case': args.case,
              'step': args.step, 'extent': args.extent, 'row': row}
    verify(path, args.plan_sha256); target = Path(args.output)
    P.need(not target.exists() and target.parent.is_dir(), 'Reference leaf output must be fresh')
    E.write(target, result)
    return result


def native_leaf(plan, plan_hash, case, mesh, inputs, runtime, output):
    P.need(E.tree(runtime) == plan['runtime'] and E.sha(runtime / 'bin/FasterCap') == P.SOLVER_SHA256
           and str(runtime) == '/solver/runtime', 'All-layer runtime identity/mount differs')
    source = inputs / 'geometry' / case['name']
    P.need(E.tree(source) == case['files'] and not output.exists() and output.parent.is_dir(), 'Native input/output owner differs')
    output.mkdir(); work = output / 'work'; work.mkdir()
    for name, row in case['files'].items():
        P.need(row['kind'] == 'file' and Path(name).name == name, 'Only flat regular Native inputs admitted')
        shutil.copyfile(source / name, work / name); (work / name).chmod(0o444)
    p = plan['protocol']; argv = [str(runtime / 'bin/FasterCap'), '-b', 'geometry.lst', '-g', '-m' + mesh,
                                '-t' + p['native_gmres_tolerance'], '-d' + p['native_interaction_ratio']]
    env = {'PATH': '/nix/store/4yfx6p85jy8v8003v5ia8c738mbcwnnq-coreutils-full-9.11/bin:/usr/bin:/bin',
           'HOME': '/tmp', 'LANG': 'C', 'LC_ALL': 'C', 'TZ': 'UTC',
           'OMP_NUM_THREADS': '1', 'OMP_DYNAMIC': 'FALSE', 'LD_BIND_NOW': '1'}
    started = time.monotonic(); child = None
    result = {'schema': 'pinwheel.streaming-8x4-rc-all-layers-native-leaf.v1', 'qualified': False,
              'model_qualified': False, 'passed': False, 'plan_sha256': plan_hash,
              'case': case['name'], 'mesh': mesh, 'argv': argv, 'environment': env,
              'cgroups': E.verify_cgroups(), 'solver_executed': False, 'exit_code': None,
              'timed_out': False, 'process_tree_reaped': False}
    try:
        with (output / 'native.log').open('xb') as stream:
            child = subprocess.Popen(argv, cwd=work, env=env, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            result['solver_executed'] = True
            try:
                result['exit_code'] = child.wait(timeout=120)
            except subprocess.TimeoutExpired:
                result['timed_out'] = True; os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
                raise ValueError('All-layer Native leaf timed out')
        try:
            os.killpg(child.pid, 0)
        except ProcessLookupError:
            result['process_tree_reaped'] = True
        else:
            os.killpg(child.pid, signal.SIGKILL); raise ValueError('All-layer Native process group remained live')
        P.need(type(result['exit_code']) is int and result['exit_code'] == 0, 'All-layer Native solver exit failed')
        numeric = P.parse_manual_log((output / 'native.log').read_text(), case['matrix_names'], mesh,
                                     p['native_gmres_tolerance'], p['native_interaction_ratio'])
        P.need(case['coordinate_unit_m'] == p['native_coordinate_unit_m'] == '0.00000095367431640625', 'S20 unit differs')
        numeric['matrix_F'] = [[str(P.number(x) * P.number(case['coordinate_unit_m'])) for x in r] for r in numeric['matrix']]
        result['numeric'] = numeric; result['passed'] = True
    except BaseException as error:
        result['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if child is not None and child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
        result['copied_inputs_unchanged'] = E.tree(work) == case['files']
        result['source_runtime_unchanged'] = E.tree(source) == case['files'] and E.tree(runtime) == plan['runtime']
        result['passed'] &= result['copied_inputs_unchanged'] and result['source_runtime_unchanged']
        result['log_sha256'] = E.sha(output / 'native.log') if (output / 'native.log').exists() else None
        result['wall_seconds'] = time.monotonic() - started; E.write(output / 'report.json', result)
    return result


def run(args):
    started = time.monotonic(); path = Path(args.plan); plan = verify(path, args.plan_sha256)
    pre = prerequisites(plan, args.plan_sha256, args.batch, Path(args.m1_pass_report), args.m1_pass_sha256,
                        Path(args.prior_batch_report) if args.prior_batch_report else None, args.prior_batch_sha256)
    P.need(args.batch in A.BATCHES and args.kind in ('reference', 'native'), 'Unsupported all-layer complete batch')
    output = Path(args.output); P.need(not output.exists() and output.parent.is_dir(), 'All-layer batch output must be fresh')
    (M.cgroups if args.kind == 'reference' else E.verify_cgroups)()
    output.mkdir(); jobs = []; leaves = []
    result = {'schema': 'pinwheel.streaming-8x4-rc-all-layers-' + args.kind + '-execution.v1',
              'qualified': False, 'model_qualified': False, 'passed': False,
              'plan_sha256': args.plan_sha256, 'batch': args.batch,
              'declared_case_names': A.BATCHES[args.batch], 'prerequisites': pre, 'jobs': jobs}
    try:
        if args.kind == 'reference':
            definitions = [c for c in plan['cases'] if c['name'] in A.BATCHES[args.batch]]
            calls = [(c, h, e) for c in definitions for h in plan['protocol']['reference_mesh_steps_um']
                     for e in plan['protocol']['reference_domain_extents_um']]
            for case, step, extent in calls:
                P.need(time.monotonic() - started <= 1670, 'Reference batch lacks full next-leaf budget')
                target = output / ('case-' + str(len(jobs)).zfill(3) + '.json'); log = target.with_name(target.name + '.log')
                argv = [sys.executable, '-I', '-B', str(Path(__file__).resolve()), 'reference-leaf',
                        '--plan', str(path), '--plan-sha256', args.plan_sha256, '--batch', args.batch,
                        '--m1-pass-report', args.m1_pass_report, '--m1-pass-sha256', args.m1_pass_sha256,
                        '--case', case['name'], '--step', step, '--extent', extent, '--output', str(target)]
                if args.prior_batch_report:
                    argv += ['--prior-batch-report', args.prior_batch_report, '--prior-batch-sha256', args.prior_batch_sha256]
                with log.open('xb') as stream:
                    child = subprocess.Popen(argv, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                    try:
                        code = child.wait(timeout=120)
                    except subprocess.TimeoutExpired:
                        os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2); raise ValueError('Reference leaf timeout')
                try:
                    os.killpg(child.pid, 0)
                except ProcessLookupError:
                    pass
                else:
                    os.killpg(child.pid, signal.SIGKILL); raise ValueError('Reference child group remained live')
                P.need(type(code) is int and code == 0 and log.read_bytes() == b'', 'Reference exit/warning/output failed')
                leaf = json.loads(target.read_text()); leaves.append(leaf)
                jobs.append({'case': case['name'], 'step': step, 'extent': extent, 'argv': argv,
                             'exit_code': code, 'process_tree_reaped': True, 'output_sha256': E.sha(target), 'log_sha256': E.sha(log)})
            result['analysis'] = reference_analysis(plan, args.plan_sha256, args.batch, leaves)
            result['passed'] = result['analysis']['passed']
        else:
            calls = [(c, m) for c in plan['geometry_cases'] if c['batch'] == args.batch for m in plan['protocol']['native_mesh_ladder']]
            for case, mesh in calls:
                P.need(time.monotonic() - started <= 1670, 'Native batch lacks full next-leaf budget')
                target = output / ('job-' + str(len(jobs)).zfill(3))
                leaf = native_leaf(plan, args.plan_sha256, case, mesh, path.parent, Path(args.runtime), target)
                jobs.append({'case': case['name'], 'mesh': mesh, 'passed': leaf['passed'], 'report_sha256': E.sha(target / 'report.json')})
                P.need(leaf['passed'], 'Native leaf failed; no later prefix promotion')
            result['passed'] = len(jobs) == plan['batches'][args.batch]['native_calls']
        verify(path, args.plan_sha256)
        prerequisites(plan, args.plan_sha256, args.batch, Path(args.m1_pass_report), args.m1_pass_sha256,
                      Path(args.prior_batch_report) if args.prior_batch_report else None, args.prior_batch_sha256)
        result['inputs_prerequisites_unchanged'] = True
    except BaseException as error:
        result['passed'] = False; result['error'] = type(error).__name__ + ': ' + str(error)
    result['wall_seconds'] = time.monotonic() - started; E.write(output / 'report.json', result)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    for action in ('run', 'reference-leaf'):
        q = sub.add_parser(action)
        for name in ('plan', 'plan-sha256', 'batch', 'm1-pass-report', 'm1-pass-sha256', 'output'):
            q.add_argument('--' + name, required=True)
        q.add_argument('--prior-batch-report'); q.add_argument('--prior-batch-sha256')
        if action == 'run':
            q.add_argument('--kind', choices=('native', 'reference'), required=True); q.add_argument('--runtime', default='/solver/runtime')
        else:
            q.add_argument('--case', required=True); q.add_argument('--step', required=True); q.add_argument('--extent', required=True)
    a = p.parse_args()
    if a.action == 'reference-leaf':
        reference_leaf(a)
    else:
        result = run(a); print(json.dumps({'passed': result['passed'], 'model_qualified': False}, indent=2))
        if not result['passed']:
            raise SystemExit(1)


if __name__ == '__main__':
    main()
