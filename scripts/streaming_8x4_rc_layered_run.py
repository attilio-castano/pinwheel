"""Bounded Native runner for the separately frozen layered M1 FVM reference.

Root owns resource admission, offline image identity and container cleanup.
No subprocess is started by import, protocol preparation or HOST review.
"""
import argparse
from decimal import Decimal
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_layered_reference as R
import streaming_8x4_rc_process as P


def verify(plan_path, plan_hash):
    P.need(P.sha(plan_path) == plan_hash, 'Layered plan hash differs')
    plan = json.loads(plan_path.read_text())
    P.need(plan['schema'] == 'pinwheel.streaming-8x4-rc-layered-plan.v1' and plan['qualified'] is False,
           'Layered plan schema/promotion differs')
    for name, value in plan['producers_sha256'].items():
        P.need(P.sha(Path(__file__).with_name(name)) == value, 'Layered producer changed')
    return plan


def cgroups():
    cg = Path('/sys/fs/cgroup')
    rows = {name: (cg / name).read_text().strip() for name in ('cpu.max', 'memory.max', 'memory.swap.max', 'pids.max')}
    quota, period = rows['cpu.max'].split()
    P.need(quota.isdigit() and 0 < int(quota) <= int(period), 'Layered reference CPU ceiling differs')
    P.need(rows['memory.max'].isdigit() and 0 < int(rows['memory.max']) <= 2147483648
           and rows['memory.swap.max'] == '0', 'Layered reference memory/swap ceiling differs')
    P.need(rows['pids.max'].isdigit() and 0 < int(rows['pids.max']) <= 256, 'Layered PID ceiling differs')
    return rows


def one(plan_path, plan_hash, case_id, step, extent, output):
    plan = verify(plan_path, plan_hash); cgroups()
    matches = [c for c in plan['cases'] if c['name'] == case_id]
    P.need(len(matches) == 1 and step in plan['protocol']['reference_mesh_steps_um']
           and extent in plan['protocol']['reference_domain_extents_um'], 'Undeclared layered reference case')
    case = matches[0]
    rects = [{'name': r['name'], 'bounds_um': [float(x) for x in r['bounds_um']]} for r in case['rectangles']]
    layers = [[float(x) for x in row] for row in case['epsilon_layers']]
    if output.name.startswith('uniform-'):
        P.need(case_id == plan['controls']['uniform_limit']['case'] and step == '.02' and extent == '32',
               'Undeclared uniform-limit control')
        layers = [[0.0, 1000.0, 4.1]]
    result = R.solve(rects, layers, float(extent), float(step),
                     tolerance=float(plan['protocol']['true_residual_relative_tolerance']),
                     maximum_iterations=plan['protocol']['maximum_cg_iterations'],
                     maximum_nodes=plan['protocol']['maximum_reference_nodes'])
    result['case_id'] = case_id; result['plan_sha256'] = plan_hash
    verify(plan_path, plan_hash)
    P.need(not output.exists() and output.parent.is_dir(), 'Layered one-case output must be fresh')
    output.write_text(json.dumps(result, indent=2) + '\n')
    return result


def flatten(row):
    return [x for vector in row['matrix_F_per_m'] for x in vector] + row['ground_C_F_per_m']


def relative_change(a, b):
    P.need(len(a) == len(b) and all(math.isfinite(x) and x != 0 for x in a + b), 'Invalid reference comparison vector')
    return max(abs(x - y) / abs(y) for x, y in zip(a, b))


def validate_excitation_membership(names, excitations):
    P.need(type(excitations) is list and len(excitations) == len(names)
           and all(type(e) is dict for e in excitations)
           and [e.get('name') for e in excitations] == names,
           'Layered reference exact ordered excitation membership differs')


def validate_uniform_control(plan, row, plan_hash):
    control = plan['controls']['uniform_limit']; policy = plan['protocol']
    cases = [c for c in plan['cases'] if c['name'] == control['case']]
    P.need(len(cases) == 1, 'Uniform-limit physical case membership differs')
    case = cases[0]; names = [r['name'] for r in case['rectangles']]
    P.need(row['plan_sha256'] == plan_hash and row['case_id'] == case['name']
           and row['names'] == names
           and row['rectangles'] == [{'name': r['name'], 'bounds_um': [float(x) for x in r['bounds_um']]}
                                     for r in case['rectangles']]
           and row['epsilon_layers'] == [[float(x) for x in layer] for layer in control['epsilon_layers']]
           and row['mesh_step_um'] == float(control['mesh_step_um'])
           and row['extent_um'] == float(control['extent_um'])
           and row['declared_mesh'] == control['mesh_step_um']
           and row['declared_extent'] == control['extent_um'], 'Uniform-limit actual geometry/material/mesh/plan differs')
    validate_excitation_membership(names, row['excitations'])
    P.need(row['qualified'] is False and row['continuum_error_enclosure'] is False
           and 0 < row['nodes'] <= policy['maximum_reference_nodes']
           and all(math.isfinite(e['true_residual_relative'])
                   and 0 <= e['true_residual_relative'] <= float(policy['true_residual_relative_tolerance'])
                   and math.isfinite(e['energy_flux_relative_error'])
                   and 0 <= e['energy_flux_relative_error'] <= float(policy['energy_flux_relative_tolerance'])
                   and 0 < e['cg_iterations'] <= policy['maximum_cg_iterations'] for e in row['excitations']),
           'Uniform-limit numerical contract differs')
    P.need(len(names) == 1 and len(row['matrix_F_per_m']) == 1 and len(row['matrix_F_per_m'][0]) == 1
           and math.isfinite(row['matrix_F_per_m'][0][0]) and row['matrix_F_per_m'][0][0] > 0,
           'Uniform-limit matrix membership/finiteness differs')


def analyze(plan, rows, uniform, plan_hash):
    policy = plan['protocol']; expected = [(c['name'], h, e) for c in plan['cases']
                                          for h in policy['reference_mesh_steps_um']
                                          for e in policy['reference_domain_extents_um']]
    P.need([(r['case_id'], r['declared_mesh'], r['declared_extent']) for r in rows] == expected,
           'Incomplete layered reference membership/order')
    P.need(all(row['plan_sha256'] == plan_hash for row in rows), 'Layered actual case plan hash differs')
    validate_uniform_control(plan, uniform, plan_hash)
    definitions = {c['name']: c for c in plan['cases']}
    for row in rows:
        case = definitions[row['case_id']]
        P.need(row['names'] == [r['name'] for r in case['rectangles']]
               and row['rectangles'] == [{'name': r['name'], 'bounds_um': [float(v) for v in r['bounds_um']]}
                                         for r in case['rectangles']]
               and row['epsilon_layers'] == [[float(v) for v in layer] for layer in case['epsilon_layers']]
               and row['extent_um'] == float(row['declared_extent'])
               and row['mesh_step_um'] == float(row['declared_mesh']), 'Actual layered reference geometry/material differs')
        validate_excitation_membership(row['names'], row['excitations'])
        P.need(row['qualified'] is False and row['continuum_error_enclosure'] is False
               and all(e['true_residual_relative'] <= float(policy['true_residual_relative_tolerance'])
                       and e['energy_flux_relative_error'] <= float(policy['energy_flux_relative_tolerance'])
                       and e['cg_iterations'] <= policy['maximum_cg_iterations'] for e in row['excitations'])
               and row['nodes'] <= policy['maximum_reference_nodes'], 'Layered reference numerical contract differs')
    groups = {(r['case_id'], r['declared_mesh'], r['declared_extent']): r for r in rows}
    results = []
    for case in plan['cases']:
        def get(h, e):
            return groups[case['name'], h, e]
        fine = get('.02', '32')
        mesh = relative_change(flatten(get('.04', '32')), flatten(fine))
        domain = relative_change(flatten(get('.02', '16')), flatten(fine))
        results.append({'name': case['name'], 'role': case['role'], 'mesh_relative_change': mesh,
                        'domain_relative_change': domain, 'fine_matrix_F_per_m': fine['matrix_F_per_m'],
                        'fine_ground_C_F_per_m': fine['ground_C_F_per_m'],
                        'fine_coupling_C_F_per_m': fine['coupling_C_F_per_m'],
                        'passed': mesh <= float(policy['maximum_reference_mesh_change'])
                                  and domain <= float(policy['maximum_reference_domain_change'])})
    uniform_error = abs(uniform['matrix_F_per_m'][0][0] / float(plan['controls']['uniform_limit']['reference_F_per_m']) - 1)
    # Direct series law vs the separately implemented piecewise harmonic edge integral.
    layers = [[float(x) for x in row] for row in plan['controls']['series_planar_exact']['layers']]
    oracle = sum((Decimal(str(top)) - Decimal(str(bottom))) / Decimal(str(er)) for bottom, top, er in layers)
    actual = R._layer_integral(layers, 0, 1.04, inverse=True)
    series_error = abs(Decimal(str(actual)) / oracle - 1)
    P.need(series_error <= Decimal(plan['controls']['series_planar_exact']['relative_tolerance']),
           'Independent layered planar series control failed')
    fine = {r['name']: r for r in results}
    ordered = True
    for field in ('fine_ground_C_F_per_m',):
        lo, mid, hi = (fine[c + '-w.16-s.18'][field] for c in ('MIN', 'TYP', 'MAX'))
        ordered &= all(a <= b <= c for a, b, c in zip(lo, mid, hi))
    coupling = [fine[c + '-w.16-s.18']['fine_coupling_C_F_per_m'] for c in ('MIN', 'TYP', 'MAX')]
    ordered &= coupling[0] <= coupling[1] <= coupling[2]
    return {'cases': results, 'uniform_limit_relative_difference': uniform_error,
            'planar_series_relative_difference': str(series_error), 'ITF_ER_corner_monotonicity': ordered,
            'passed': all(r['passed'] for r in results)
                      and uniform_error <= float(plan['controls']['uniform_limit']['relative_tolerance']) and ordered,
            'model_qualified': False, 'continuum_error_enclosure': False}


def run(plan_path, plan_hash, output):
    plan = verify(plan_path, plan_hash)
    P.need(not output.exists() and output.parent.is_dir(), 'Layered reference output must be fresh')
    output.mkdir(); started = time.monotonic(); rows = []; jobs = []
    report = {'schema': 'pinwheel.streaming-8x4-rc-layered-reference-execution.v1', 'plan_sha256': plan_hash,
              'passed': False, 'qualified': False, 'model_qualified': False, 'jobs': jobs, 'cases': rows}
    try:
        report['cgroups'] = cgroups()
        calls = [(c['name'], h, e, False) for c in plan['cases']
                 for h in plan['protocol']['reference_mesh_steps_um'] for e in plan['protocol']['reference_domain_extents_um']]
        calls.append((plan['controls']['uniform_limit']['case'], '.02', '32', True))
        uniform = None
        for index, (case_id, step, extent, is_uniform) in enumerate(calls):
            P.need(time.monotonic() - started <= 1670, 'Insufficient predeclared reference work budget')
            name = ('uniform-' if is_uniform else '') + f'case-{index:03}.json'
            target = output / name; log = output / (name + '.log')
            command = [sys.executable, '-I', '-B', str(Path(__file__).resolve()), 'one',
                       '--plan', str(plan_path), '--plan-sha256', plan_hash, '--case', case_id,
                       '--step', step, '--extent', extent, '--output', str(target)]
            with log.open('wb') as stream:
                child = subprocess.Popen(command, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    code = child.wait(timeout=120)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL); child.wait()
                    raise ValueError('Layered reference per-call timeout')
            try:
                os.killpg(child.pid, 0)
            except ProcessLookupError:
                pass
            else:
                os.killpg(child.pid, signal.SIGKILL)
                raise ValueError('Layered reference process group remained live')
            P.need(type(code) is int and code == 0 and log.read_bytes() == b'', 'Reference child exit/warning/output failed')
            row = json.loads(target.read_text())
            P.need(row['plan_sha256'] == plan_hash and row['qualified'] is False and row['case_id'] == case_id,
                   'Layered child result binding differs')
            row['declared_mesh'] = step; row['declared_extent'] = extent
            jobs.append({'case': case_id, 'step': step, 'extent': extent, 'uniform_control': is_uniform,
                         'exit_code': code, 'argv': command, 'output_sha256': P.sha(target),
                         'log_sha256': P.sha(log), 'process_tree_reaped': True})
            if is_uniform:
                uniform = row
            else:
                rows.append(row)
        report['uniform_control'] = uniform; report['analysis'] = analyze(plan, rows, uniform, plan_hash)
        verify(plan_path, plan_hash); report['inputs_unchanged'] = True
        report['passed'] = report['analysis']['passed']
    except Exception as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    report['wall_seconds'] = time.monotonic() - started
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    for action in ('run', 'one'):
        q = sub.add_parser(action); q.add_argument('--plan', type=Path, required=True)
        q.add_argument('--plan-sha256', required=True); q.add_argument('--output', type=Path, required=True)
        if action == 'one':
            q.add_argument('--case', required=True); q.add_argument('--step', required=True); q.add_argument('--extent', required=True)
    args = p.parse_args()
    if args.action == 'one':
        one(args.plan, args.plan_sha256, args.case, args.step, args.extent, args.output)
    else:
        result = run(args.plan, args.plan_sha256, args.output)
        print(json.dumps({'passed': result['passed'], 'qualified': False, 'output': str(args.output)}, indent=2))
        if not result['passed']:
            raise SystemExit(1)


if __name__ == '__main__':
    main()
