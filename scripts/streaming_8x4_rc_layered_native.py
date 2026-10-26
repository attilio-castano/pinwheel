"""Frozen layered BEM input preparation and resource-bounded explicit jobs.

Root must separately admit the exact proposal and offline container. Geometry
preparation is HOST-only. Native results cannot qualify the full RC model.
"""
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
import streaming_8x4_rc_execute as E
import streaming_8x4_rc_protocol as P
import streaming_8x4_rc_layered_run as L


def prepare(reference_plan, reference_hash, geometry, runtime, output):
    reference = L.verify(reference_plan, reference_hash)
    P.need(not output.exists() and output.parent.is_dir(), 'Layered native preparation must be fresh')
    manifest = json.loads((geometry / 'manifest.json').read_text())
    P.need(manifest['reference_plan_sha256'] == reference_hash
           and manifest['producer_sha256'] == E.sha(Path(__file__).with_name('streaming_8x4_rc_layered_geometry.py')),
           'Layered geometry derivation differs')
    expected = [(c['name'], length, ext) for c in reference['cases']
                for length, ext in [('10', '20'), ('20', '20'), ('30', '20'), ('20', '30'), ('30', '30')]]
    P.need([(r['case'], r['length_um'], r['extension_um']) for r in manifest['cases']] == expected,
           'Layered geometry membership differs')
    cases = []
    for row in manifest['cases']:
        source = geometry / row['name']; tree = E.tree(source)
        P.need(set(tree) == set(row['files_sha256']) | {'geometry-certificate.json'}, 'Layered geometry files differ')
        for name, value in row['files_sha256'].items():
            P.need(tree[name]['kind'] == 'file' and tree[name]['sha256'] == value, 'Layered geometry bytes differ')
        P.need(E.sha(source / 'geometry-certificate.json') == row['certificate_sha256'], 'Geometry certificate differs')
        unit_map = json.loads((source / 'unit-map.json').read_text())
        P.need(unit_map['coordinate_unit_m'] == '0.00000095367431640625' and unit_map['S'] == 1048576
               and unit_map['exact_binary32_coordinate_scaling'] is True, 'Wrong fixed layered numerical unit')
        P.need(set(unit_map['emitted_files_sha256']) == set(row['files_sha256']) - {'unit-map.json'}
               and all(E.sha(source / n) == v for n, v in unit_map['emitted_files_sha256'].items()),
               'S20 emitted file witness differs')
        cases.append(dict(row, files=tree, coordinate_unit_m=unit_map['coordinate_unit_m'],
                          matrix_names=['g' + str(i + 1) + '_' + n for i, n in enumerate(row['conductor_names'])]))
    P.need(E.sha(runtime / 'bin/FasterCap') == P.SOLVER_SHA256, 'Wrong native layered solver')
    names = set(reference['producers_sha256']) | {
        'streaming_8x4_rc_layered_native.py', 'streaming_8x4_rc_layered_geometry.py', 'streaming_8x4_rc_execute.py'}
    protocol = dict(reference['protocol'], native_coordinate_unit_m='0.00000095367431640625',
                    native_scaling_policy='all corners/held-out cases share exact binary32 S20 normalization; same m values do not assert equivalent mesh to U')
    plan = {'schema': 'pinwheel.streaming-8x4-rc-layered-native-plan.v1', 'qualified': False,
            'model_qualified': False, 'execution_admitted': False, 'reference_plan_sha256': reference_hash,
            'geometry_manifest_sha256': E.sha(geometry / 'manifest.json'),
            'native_scaling_source_evidence': {
                'fastercap_commit': 'b42179a8fdd25ab42fe45527282b4a738d7e7f87',
                'Autorefine_cpp_sha256': '50dd78c1589a244a49bc3a4aca33e8bde696e14ab5853f00648c5a572065b1a8',
                'Potential_cpp_sha256': 'a9295b2cbc294318b833e4b38af5b7663ece01b123c3a0c8ac4b093d62292858',
                'manual_m_scale_invariant': False,
                'inference': '3D conductor criterion scales 1/s and dielectric criterion 1/s^2; fixed unit is mandatory; no mesh equivalence is inferred',
                'supersedes_reference_plan_native_coordinate_hint_only': True,
                'reference_FVM_cases_and_tolerances_unchanged': True},
            'protocol': protocol, 'cases': cases, 'runtime': E.tree(runtime),
            'solver_sha256': P.SOLVER_SHA256,
            'producers_sha256': {n: E.sha(Path(__file__).with_name(n)) for n in sorted(names)}}
    output.mkdir(); E.write(output / 'plan.json', plan)
    return {'plan': str(output / 'plan.json'), 'plan_sha256': E.sha(output / 'plan.json'),
            'cases': len(cases), 'solver_executed': False}


def verify(plan_path, plan_hash, cases, runtime):
    P.need(E.sha(plan_path) == plan_hash, 'Frozen layered Native plan differs')
    plan = json.loads(plan_path.read_text())
    P.need(plan['schema'] == 'pinwheel.streaming-8x4-rc-layered-native-plan.v1' and plan['qualified'] is False,
           'Wrong layered Native plan schema/promotion')
    for name, value in plan['producers_sha256'].items():
        P.need(E.sha(Path(__file__).with_name(name)) == value, 'Layered Native producer differs')
    P.need(E.tree(runtime) == plan['runtime'] and E.sha(runtime / 'bin/FasterCap') == P.SOLVER_SHA256,
           'Layered runtime differs')
    P.need(E.sha(cases / 'manifest.json') == plan['geometry_manifest_sha256'], 'Layered geometry manifest differs')
    return plan


def one(args):
    started = time.monotonic()
    plan_path, cases, runtime, output = map(Path, (args.plan, args.cases, args.runtime, args.output))
    plan = verify(plan_path, args.plan_sha256, cases, runtime)
    matches = [c for c in plan['cases'] if c['name'] == args.case]
    P.need(len(matches) == 1 and args.mesh in plan['protocol']['native_mesh_ladder'], 'Undeclared layered job')
    case = matches[0]; source = cases / case['name']
    P.need(E.tree(source) == case['files'], 'Layered case input differs')
    P.need(str(runtime) == '/solver/runtime', 'Require pinned runtime mount')
    P.need(not output.exists() and output.parent.is_dir(), 'Layered output owner must be fresh')
    output.mkdir(); work = output / 'work'; work.mkdir()
    for name, row in case['files'].items():
        P.need(Path(name).name == name and row['kind'] == 'file', 'Only flat regular layered case inputs admitted')
        shutil.copyfile(source / name, work / name); (work / name).chmod(0o444)
    argv = [str(runtime / 'bin/FasterCap'), '-b', 'geometry.lst', '-g', '-m' + args.mesh,
            '-t' + plan['protocol']['native_gmres_tolerance'], '-d' + plan['protocol']['native_interaction_ratio']]
    environment = {'PATH': '/nix/store/4yfx6p85jy8v8003v5ia8c738mbcwnnq-coreutils-full-9.11/bin:/usr/bin:/bin',
                   'HOME': '/tmp', 'LANG': 'C', 'LC_ALL': 'C', 'TZ': 'UTC',
                   'OMP_NUM_THREADS': '1', 'OMP_DYNAMIC': 'FALSE', 'LD_BIND_NOW': '1'}
    report = {'schema': 'pinwheel.streaming-8x4-rc-layered-native-execution.v1', 'qualified': False,
              'model_qualified': False, 'plan_sha256': args.plan_sha256, 'case': args.case,
              'mesh': args.mesh, 'argv': argv, 'environment': environment, 'cgroups': E.verify_cgroups(),
              'mountinfo': Path('/proc/self/mountinfo').read_text(), 'passed': False,
              'solver_executed': False, 'exit_code': None, 'timed_out': False, 'process_tree_reaped': False,
              'source_runtime_unchanged': False, 'copied_inputs_unchanged': False,
              'scratch_available_bytes_before': shutil.disk_usage('/tmp').free}
    E.write(output / 'report.json', report); child = None
    try:
        with (output / 'native.log').open('xb') as stream:
            child = subprocess.Popen(argv, cwd=work, env=environment, stdout=stream,
                                     stderr=subprocess.STDOUT, start_new_session=True)
            report['solver_executed'] = True
            try:
                code = child.wait(timeout=plan['protocol']['native_resources']['seconds_per_call'])
            except subprocess.TimeoutExpired:
                report['timed_out'] = True; os.killpg(child.pid, signal.SIGKILL); child.wait()
                raise ValueError('Layered Native per-call timeout')
            report['exit_code'] = code
        try:
            os.killpg(child.pid, 0)
        except ProcessLookupError:
            report['process_tree_reaped'] = True
        else:
            os.killpg(child.pid, signal.SIGKILL)
            raise ValueError('Layered Native process group remained live')
        P.need(type(code) is int and code == 0 and report['timed_out'] is False, 'Layered solver exit failed')
        numeric = P.parse_manual_log((output / 'native.log').read_text(), case['matrix_names'], args.mesh,
                                     plan['protocol']['native_gmres_tolerance'], plan['protocol']['native_interaction_ratio'])
        scale = P.number(case['coordinate_unit_m'])
        P.need(case['coordinate_unit_m'] == plan['protocol']['native_coordinate_unit_m'], 'Native unit policy differs')
        numeric['matrix_F'] = [[str(P.number(x) * scale) for x in row] for row in numeric['matrix']]
        report['numeric'] = numeric; report['passed'] = True
    except BaseException as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if child is not None and child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL); child.wait(timeout=2)
        report['copied_inputs_unchanged'] = E.tree(work) == case['files']
        report['source_runtime_unchanged'] = E.tree(runtime) == plan['runtime'] and E.tree(source) == case['files']
        try:
            verify(plan_path, args.plan_sha256, cases, runtime)
            report['producer_plan_unchanged'] = True
        except Exception as error:
            report['producer_plan_unchanged'] = False; report['binding_error'] = str(error)
        report['passed'] &= report['copied_inputs_unchanged'] and report['source_runtime_unchanged'] and report['producer_plan_unchanged']
        report['wall_seconds'] = time.monotonic() - started
        report['scratch_available_bytes_after'] = shutil.disk_usage('/tmp').free
        report['log_sha256'] = E.sha(output / 'native.log') if (output / 'native.log').exists() else None
        E.write(output / 'report.json', report)
    return report


def batch(args):
    started = time.monotonic(); plan = verify(Path(args.plan), args.plan_sha256, Path(args.cases), Path(args.runtime))
    names = [c['name'] for c in plan['cases']]
    selected = args.case or names; meshes = args.mesh or plan['protocol']['native_mesh_ladder']
    P.need(len(selected) == len(set(selected)) and all(n in names for n in selected), 'Bad layered case selection')
    P.need(len(meshes) == len(set(meshes)) and meshes == plan['protocol']['native_mesh_ladder'][:len(meshes)],
           'Layered mesh selection must be a complete declared prefix')
    P.need(len(selected) * len(meshes) <= 150 and 0 < args.work_seconds <= 3600, 'Layered work allowance differs')
    output = Path(args.output); P.need(not output.exists() and output.parent.is_dir(), 'Layered batch owner must be fresh')
    output.mkdir(); rows = []; result = {'schema': 'pinwheel.streaming-8x4-rc-layered-native-batch.v1',
        'qualified': False, 'model_qualified': False, 'passed': False, 'plan_sha256': args.plan_sha256,
        'selected_cases': selected, 'selected_meshes': meshes, 'jobs': rows}
    try:
        for name in selected:
            for mesh in meshes:
                P.need(time.monotonic() - started <= args.work_seconds - 130, 'Layered batch work budget insufficient')
                child_args = argparse.Namespace(**vars(args)); child_args.case = name; child_args.mesh = mesh
                child_args.output = str(output / ('job-' + str(len(rows)).zfill(3)))
                row = one(child_args); rows.append({'directory': child_args.output, 'case': name, 'mesh': mesh,
                                                    'passed': row['passed'], 'report_sha256': E.sha(Path(child_args.output) / 'report.json')})
                P.need(row['passed'], 'Layered Native case failed; no later prefix promoted')
        result['passed'] = len(rows) == len(selected) * len(meshes)
        result['full_declared_membership'] = selected == names and meshes == plan['protocol']['native_mesh_ladder']
    except BaseException as error:
        result['error'] = type(error).__name__ + ': ' + str(error)
    result['wall_seconds'] = time.monotonic() - started; E.write(output / 'report.json', result)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__); sub = p.add_subparsers(dest='action', required=True)
    q = sub.add_parser('prepare'); q.add_argument('--reference-plan', type=Path, required=True)
    q.add_argument('--reference-hash', required=True); q.add_argument('--geometry', type=Path, required=True)
    q.add_argument('--runtime', type=Path, required=True); q.add_argument('--output', type=Path, required=True)
    for action in ('one', 'batch'):
        q = sub.add_parser(action)
        for name in ('plan', 'plan-sha256', 'cases', 'runtime', 'output'):
            q.add_argument('--' + name, required=True)
        q.add_argument('--case', required=action == 'one', action='append' if action == 'batch' else 'store')
        q.add_argument('--mesh', required=action == 'one', action='append' if action == 'batch' else 'store')
        if action == 'batch':
            q.add_argument('--work-seconds', type=int, default=3600)
    args = p.parse_args()
    if args.action == 'prepare':
        result = prepare(args.reference_plan, args.reference_hash, args.geometry, args.runtime, args.output)
    else:
        result = one(args) if args.action == 'one' else batch(args)
    print(json.dumps(result, indent=2))
    if args.action != 'prepare' and not result['passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
