"""Bounded full-universe Native worker; Root owns the external GO/lease."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import streaming_8x4_rc_full_policy as W
import streaming_8x4_rc_conditioning_parser as O

P, E = W.P, W.E


def parse(log, plan, case, mesh):
    p = plan['policy']
    P.need(type(log) is str and len(log) <= 8 * 1024 * 1024
        and not re.search(r'(?i)\b(?:warning|warn|error|fatal)\b|segmentation fault|killed|timeout', log),
        'Warning/failure marker anywhere in full-policy solver log')
    expected = 'Jacobi' if p['preconditioner'] == 'jacobi' else 'Two-levels, two-levels preconditioner dimension (-ps): 128'
    P.need(re.findall(r'^Precond Type\(s\) \(-p\):\s*([^\r\n]*?)\s*$', log, re.M) == [expected],
           'Actual full-policy preconditioner differs/mixed/duplicated')
    numeric = P.parse_manual_log(log, case['matrix_names'], mesh, p['gmres_tolerance'], p['interaction_ratio'])
    numeric['matrix_F'] = [[str(P.number(x) * P.number(case['coordinate_unit_m'])) for x in row] for row in numeric['matrix']]
    traces = re.findall(r'^GMRES Iteration:\s*([^\r\n]*)$', log, re.M); lengths = []
    P.need(len(traces) <= len(case['matrix_names']), 'Extra full-policy GMRES excitation')
    for text in traces:
        P.need(re.fullmatch(r'\d+(?:\s+\d+)*\s*', text) is not None, 'Unsupported full-policy GMRES trace')
        values = list(map(int, text.split()))
        P.need(0 < len(values) <= 1000 and values == list(range(len(values))), 'Skipped/reordered/excess full-policy GMRES trace')
        lengths.append(len(values))
    numeric.update(actual_preconditioner=p['preconditioner'], interaction_ratio=p['interaction_ratio'],
                   GMRES_iteration_trace_lengths=lengths, independent_true_residual_enclosure=False, model_qualified=False)
    return numeric


def closed(row):
    W.C.D.closed_leaf(row)


def leaf(inputs, plan_hash, plan, case, mesh, runtime, output):
    P.need(not output.exists() and output.parent.is_dir() and str(runtime) == '/solver/runtime'
        and E.tree(runtime) == plan['runtime'], 'Full-policy leaf owner/runtime differs')
    output.mkdir(); work = output / 'work'; work.mkdir()
    for n, row in case['files'].items():
        P.need(Path(n).name == n and row['kind'] == 'file', 'Only flat regular full-policy inputs admitted')
        shutil.copyfile(inputs / 'geometry' / case['name'] / n, work / n); (work / n).chmod(0o444)
    result = {'schema': 'pinwheel.streaming-8x4-rc-full-policy-native-leaf.v1', 'profile': plan['profile'],
        'qualified': False, 'model_qualified': False, 'qualified_timing': False,
        'plan_sha256': plan_hash, 'case': case['name'], 'mesh': mesh,
        'argv': W.solver_argv(plan['policy'], mesh), 'environment': W.C.ENVIRONMENT,
        'timeout_seconds': 120, 'cgroups': E.verify_cgroups(), 'passed': False,
        'solver_executed': False, 'exit_code': None, 'timed_out': False, 'process_tree_reaped': False,
        'numeric': None, 'scratch_available_bytes_before': shutil.disk_usage('/tmp').free}
    child = None; started = time.monotonic(); raw = ''
    try:
        with (output / 'native.log').open('xb') as stream:
            child = subprocess.Popen(result['argv'], cwd=work, env=dict(W.C.ENVIRONMENT), stdout=stream,
                stderr=subprocess.STDOUT, start_new_session=True); result['solver_executed'] = True
            try: result['exit_code'] = child.wait(timeout=120)
            except subprocess.TimeoutExpired:
                result['timed_out'] = True; os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2); result['exit_code'] = child.returncode
        try: os.killpg(child.pid, 0)
        except ProcessLookupError: result['process_tree_reaped'] = True
        else:
            os.killpg(child.pid, signal.SIGKILL); raise ValueError('Full-policy leaf process group remains live')
        P.need(result['exit_code'] == 0 and result['timed_out'] is False, 'Full-policy solver exit/timeout failed')
        raw = (output / 'native.log').read_text(); result['numeric'] = parse(raw, plan, case, mesh); result['passed'] = True
    except BaseException as error: result['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if child is not None and child.poll() is None: os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
        result['copied_inputs_unchanged'] = E.tree(work) == case['files']
        result['source_runtime_unchanged'] = E.tree(inputs / 'geometry' / case['name']) == case['files'] and E.tree(runtime) == plan['runtime']
        result['producer_plan_unchanged'] = W.verify(inputs, plan_hash) == plan
        raw = (output / 'native.log').read_text() if (output / 'native.log').exists() else raw
        result['log_sha256'] = E.sha(output / 'native.log') if (output / 'native.log').exists() else None
        result['observations'] = O.observations(raw, case['matrix_names']); result['wall_seconds'] = time.monotonic() - started
        result['scratch_available_bytes_after'] = shutil.disk_usage('/tmp').free
        result['passed'] &= all(result[k] is True for k in ('process_tree_reaped', 'copied_inputs_unchanged', 'source_runtime_unchanged', 'producer_plan_unchanged'))
        W.write(output / 'report.json', result)
    return result


def run(inputs, plan_hash, runtime, output):
    plan = W.verify(inputs, plan_hash); p = plan['policy']; expected = W.jobs(plan)
    P.need(str(runtime) == '/solver/runtime' and E.tree(runtime) == plan['runtime'] and not output.exists()
        and output.parent.is_dir() and output.name == 'rc-full-' + plan['profile'] + '-01', 'Full-policy run owner/runtime differs')
    E.verify_cgroups(); output.mkdir(); rows = []; started = time.monotonic()
    result = {'schema': 'pinwheel.streaming-8x4-rc-full-policy-native-execution.v1', 'profile': plan['profile'],
        'plan_sha256': plan_hash, 'policy': p, 'qualified': False, 'model_qualified': False, 'qualified_timing': False,
        'limited_pilot_passed': False, 'measurement_packet_completed': False, 'all_numeric_leaves_passed': False,
        'jobs': rows, 'passed': False}
    definitions = {c['name']: c for c in plan['cases']}; closed_count = 0
    try:
        for index, job in enumerate(expected):
            P.need(time.monotonic() - started <= p['work_seconds'] - 130, 'Insufficient full-policy next-leaf/cleanup allowance')
            W.verify(inputs, plan_hash)
            owner = output / ('job-' + str(index).zfill(3))
            value = leaf(inputs, plan_hash, plan, definitions[job['case']], job['mesh'], runtime, owner)
            rows.append(dict(job, passed=value['passed'], report_sha256=E.sha(owner / 'report.json')))
            closed(value); closed_count += 1
            P.need(value['passed'] is True, 'Full-policy numeric failure; later suffix not executed')
        result['measurement_packet_completed'] = len(rows) == p['maximum_calls'] and [{k: r[k] for k in ('case', 'mesh')} for r in rows] == expected
        result['all_numeric_leaves_passed'] = result['measurement_packet_completed'] and all(r['passed'] for r in rows)
        result['passed'] = result['all_numeric_leaves_passed']
    except BaseException as error: result['error'] = type(error).__name__ + ': ' + str(error)
    result['measurement_packet_completed'] = len(rows) == len(expected) == closed_count and [{k: r[k] for k in ('case', 'mesh')} for r in rows] == expected
    result['all_numeric_leaves_passed'] = result['measurement_packet_completed'] and all(r['passed'] is True for r in rows)
    result['passed'] = result['all_numeric_leaves_passed']
    result['inputs_runtime_unchanged'] = W.verify(inputs, plan_hash) == plan and E.tree(runtime) == plan['runtime']
    result['passed'] &= result['inputs_runtime_unchanged']; result['wall_seconds'] = time.monotonic() - started
    W.write(output / 'report.json', result); return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for n in ('inputs', 'runtime', 'output'): p.add_argument('--' + n, type=Path, required=True)
    p.add_argument('--plan-sha256', required=True); a = p.parse_args()
    result = run(a.inputs, a.plan_sha256, a.runtime, a.output)
    print(json.dumps({'measurement_packet_completed': result['measurement_packet_completed'], 'all_numeric_leaves_passed': result['all_numeric_leaves_passed'], 'limited_pilot_passed': False, 'model_qualified': False}, indent=2))
    return 0 if result['passed'] else 2


if __name__ == '__main__': raise SystemExit(main())
