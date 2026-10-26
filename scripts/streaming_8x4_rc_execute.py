"""Prepare RC pilot inputs or execute one explicitly selected bounded Linux job.

Preparation never invokes FasterCap.  A campaign owner must admit the exact
plan/source/runtime hashes and supply the offline resource-bounded container.
This worker verifies its cgroup ceilings and records actual process outcomes;
it never upgrades a failed historical experiment or qualifies a process model.
"""
import argparse
from datetime import datetime, timezone
import hashlib
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
import streaming_8x4_rc_protocol as P


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def tree(root):
    root = Path(root).resolve(strict=True)
    result = {}
    for path in sorted(root.rglob('*')):
        relative = str(path.relative_to(root))
        if path.is_symlink():
            target = os.readlink(path)
            if Path(target).is_absolute():
                # The archived wx-config install link names its original Linux
                # mount.  Rebind only that declared mount for host readback;
                # preserve the literal link and require the identical mount in
                # the container.  No arbitrary absolute link is accepted.
                prefix = '/solver/runtime/'
                P.need(target.startswith(prefix), 'Unadmitted absolute runtime symlink')
                rebound = root / target[len(prefix):]
                P.need(rebound.resolve(strict=True).is_relative_to(root), 'Rebound runtime link escapes root')
            else:
                P.need(path.resolve(strict=True).is_relative_to(root), 'Runtime symlink escapes selected root')
            result[relative] = {'kind': 'symlink', 'target': target}
        elif path.is_file():
            result[relative] = {'kind': 'file', 'bytes': path.stat().st_size, 'sha256': sha(path)}
        else:
            P.need(path.is_dir(), 'Unsupported runtime node')
    P.need(result, 'Empty selected tree')
    return result


def write(path, value):
    path = Path(path)
    temp = path.with_name(path.name + '.tmp')
    temp.write_bytes(P.canonical(value) + b'\n')
    temp.replace(path)


def prepare(owner, runtime, historical_u=None):
    owner, runtime = Path(owner), Path(runtime).resolve(strict=True)
    P.need(owner.is_absolute() and not owner.exists() and owner.parent.is_dir(), 'Preparation owner must be fresh')
    P.need(sha(runtime / 'bin/FasterCap') == P.SOLVER_SHA256, 'Unexpected FasterCap binary')
    protocol = P.frozen_protocol()
    owner.mkdir()
    cases = []
    for width in ('0.16', '0.32'):
        for length in ('10', '20', '30'):
            name = 'wire_w' + width.replace('.', 'p') + '_L' + length + '_M20'
            path = owner / name; path.mkdir()
            for filename, content in P.finite_wire_files(protocol, width, length).items():
                (path / filename).write_bytes(content)
            cases.append({'name': name, 'kind': 'training' if width == '0.16' else 'held_out',
                          'width_um': width, 'length_um': length, 'margin_um': '20',
                          'coordinate_unit_m': '0.000001', 'matrix_names': ['g1_GND_SUB', 'g2_SIGNAL'],
                          'files': tree(path)})
    for width in ('0.16', '0.32'):
        for length in ('20', '30'):
            name = 'wire_w' + width.replace('.', 'p') + '_L' + length + '_M30'
            path = owner / name; path.mkdir()
            for filename, content in P.finite_wire_files(protocol, width, length, margin_um='30').items():
                (path / filename).write_bytes(content)
            cases.append({'name': name, 'kind': 'ground_extension',
                          'width_um': width, 'length_um': length, 'margin_um': '30',
                          'coordinate_unit_m': '0.000001', 'matrix_names': ['g1_GND_SUB', 'g2_SIGNAL'],
                          'files': tree(path)})
    if historical_u:
        original = Path(historical_u).resolve(strict=True)
        P.need(original.is_dir(), 'Original U case unavailable')
        selected = ['c_GND_SUB_0.qui', 'c_SIGNAL_0.qui', 'geometry.lst', 'certificate.json', 'mesh.json', 'unit-map.json']
        path = owner / 'historical_U_new_manual'; path.mkdir()
        for name in selected:
            source = original / name
            P.need(source.is_file() and not source.is_symlink(), 'Missing/aliased historical U geometry')
            shutil.copyfile(source, path / name)
        cases.insert(0, {'name': path.name, 'kind': 'historical_geometry_new_manual_experiment',
                         'coordinate_unit_m': '0.00000095367431640625',
                         'matrix_names': ['g1_GND_SUB', 'g2_SIGNAL'],
                         'source_path': str(original), 'files': tree(path),
                         'historical_failure_promoted': False})
    producers = {}
    for name in ('streaming_8x4_rc_protocol.py', 'streaming_8x4_rc_execute.py', 'streaming_8x4_rc_reference.py'):
        producers[name] = sha(Path(__file__).resolve().parent / name)
    plan = {'schema': 'pinwheel.streaming-8x4-rc-execution-plan.v1', 'created_utc': utc(),
            'protocol': protocol, 'protocol_sha256': P.validate_protocol(protocol),
            'producers_sha256': producers, 'runtime': tree(runtime),
            'solver_sha256': P.SOLVER_SHA256, 'cases': cases,
            'qualified': False, 'execution_admitted': False}
    write(owner / 'plan.json', plan)
    return {'plan': str(owner / 'plan.json'), 'plan_sha256': sha(owner / 'plan.json'),
            'case_count': len(cases), 'solver_executed': False}


def verify_cgroups():
    base = Path('/sys/fs/cgroup')
    memory = (base / 'memory.max').read_text().strip()
    swap = (base / 'memory.swap.max').read_text().strip()
    cpu = (base / 'cpu.max').read_text().split()
    pids = (base / 'pids.max').read_text().strip()
    P.need(memory.isdigit() and 0 < int(memory) <= 6 * 1024 ** 3, 'Missing/excessive memory cgroup')
    P.need(swap == '0', 'Extra swap is not admitted')
    P.need(len(cpu) == 2 and all(x.isdigit() for x in cpu) and int(cpu[0]) <= int(cpu[1]),
           'CPU cgroup exceeds one CPU')
    P.need(pids.isdigit() and 0 < int(pids) <= 256, 'Missing/excessive PID cgroup')
    return {'memory_max': memory, 'memory_swap_max': swap, 'cpu_max': ' '.join(cpu), 'pids_max': pids}


def run_one(args):
    started = time.monotonic()
    plan_path, case_root, runtime, output = map(Path, (args.plan, args.cases, args.runtime, args.output))
    P.need(re.fullmatch('[0-9a-f]{64}', args.plan_sha256) and sha(plan_path) == args.plan_sha256,
           'Admitted plan hash mismatch')
    plan = json.loads(plan_path.read_text())
    P.need(plan['schema'] == 'pinwheel.streaming-8x4-rc-execution-plan.v1', 'Wrong execution plan schema')
    P.validate_protocol(plan['protocol'])
    P.need(plan['protocol_sha256'] == P.validate_protocol(plan['protocol']), 'Protocol identity differs')
    for name, value in plan['producers_sha256'].items():
        P.need(sha(Path(__file__).resolve().parent / name) == value, 'Producer source differs: ' + name)
    P.need(tree(runtime) == plan['runtime'], 'Runtime membership/content differs before execution')
    P.need(sha(runtime / 'bin/FasterCap') == P.SOLVER_SHA256, 'Wrong solver binary')
    rows = [x for x in plan['cases'] if x['name'] == args.case]
    P.need(len(rows) == 1, 'Case is absent/duplicated in admitted plan')
    case = rows[0]
    source = case_root / case['name']
    P.need(tree(source) == case['files'], 'Geometry membership/content differs before execution')
    mesh = args.mesh
    P.need(mesh in plan['protocol']['manual_solver']['mesh_ladder'], 'Undeclared mesh selection')
    P.need(output.is_absolute() and not output.exists() and output.parent.is_dir(), 'Require fresh output owner')
    output.mkdir()
    work = output / 'work'; work.mkdir()
    for name, row in case['files'].items():
        P.need(row['kind'] == 'file' and Path(name).name == name, 'Only flat regular case files admitted')
        shutil.copyfile(source / name, work / name)
        (work / name).chmod(0o444)
    selected = plan['protocol']['manual_solver']
    argv = [str(runtime / 'bin/FasterCap'), '-b', 'geometry.lst', '-g', '-m' + mesh,
            '-t' + selected['gmres_tolerance'], '-d' + selected['interaction_ratio']]
    # Preserve the previously exercised direct ELF entry and child environment.
    # In particular FasterCap's helper uname lookup needs this pinned coreutils
    # prefix; /usr/bin:/bin alone failed in the historical Nix image.  The ELF
    # RPATH selects the frozen wx runtime, so no LD_LIBRARY_PATH is introduced.
    P.need(str(runtime) == '/solver/runtime', 'Require the original declared runtime mount')
    environment = {
        'PATH': '/nix/store/4yfx6p85jy8v8003v5ia8c738mbcwnnq-coreutils-full-9.11/bin:/usr/bin:/bin',
        'HOME': '/tmp', 'LANG': 'C', 'LC_ALL': 'C', 'TZ': 'UTC',
        'OMP_NUM_THREADS': '1', 'OMP_DYNAMIC': 'FALSE', 'LD_BIND_NOW': '1',
    }
    report = {'schema': 'pinwheel.streaming-8x4-rc-manual-execution.v1',
              'started_utc': utc(), 'plan_sha256': args.plan_sha256,
              'case': args.case, 'mesh': mesh, 'argv': argv, 'environment': environment,
              'cgroups': verify_cgroups(), 'mountinfo': Path('/proc/self/mountinfo').read_text(),
              'solver_executed': False, 'exit_code': None, 'timed_out': False,
              'process_tree_reaped': False, 'passed': False, 'qualified': False,
              'scratch_available_bytes_before': shutil.disk_usage('/tmp').free,
              'source_runtime_unchanged': False, 'observed_max_solver_rss_KiB': 0}
    write(output / 'report.json', report)
    process = None
    try:
        with (output / 'native.log').open('xb') as log:
            process = subprocess.Popen(argv, cwd=work, env=environment, stdout=log,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            report['solver_executed'] = True; report['solver_pid'] = process.pid
            write(output / 'report.json', report)
            deadline = time.monotonic() + plan['protocol']['resource_request']['solver_seconds_per_call']
            while process.poll() is None:
                status = Path('/proc') / str(process.pid) / 'status'
                try:
                    match = re.search(r'^VmRSS:\s*(\d+)\s+kB', status.read_text(), flags=re.M)
                    if match:
                        report['observed_max_solver_rss_KiB'] = max(report['observed_max_solver_rss_KiB'], int(match[1]))
                except FileNotFoundError:
                    pass
                if time.monotonic() > deadline:
                    report['timed_out'] = True
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL); process.wait(timeout=2)
                    break
                time.sleep(.05)
            report['exit_code'] = process.wait()
            report['process_tree_reaped'] = True
        P.need(report['exit_code'] == 0 and not report['timed_out'], 'Solver failed/timed out')
        numeric = P.parse_manual_log((output / 'native.log').read_text(), case['matrix_names'], mesh,
                                     selected['gmres_tolerance'], selected['interaction_ratio'])
        scale = P.number(case['coordinate_unit_m'])
        numeric['matrix_F'] = [[str(P.number(x) * scale) for x in row] for row in numeric['matrix']]
        report['numeric'] = numeric
        report['passed'] = True
    except BaseException as error:
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        if process is not None and process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL); process.wait(timeout=2)
            report['process_tree_reaped'] = True
        copied_same = tree(work) == case['files']
        report['copied_inputs_unchanged'] = copied_same
        same = tree(runtime) == plan['runtime'] and tree(source) == case['files'] and copied_same
        report['source_runtime_unchanged'] = same
        report['passed'] = report['passed'] and same
        report['ended_utc'] = utc(); report['wall_seconds'] = time.monotonic() - started
        report['scratch_available_bytes_after'] = shutil.disk_usage('/tmp').free
        report['log_sha256'] = sha(output / 'native.log') if (output / 'native.log').exists() else None
        write(output / 'report.json', report)
    return 0 if report['passed'] else 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    prep = sub.add_parser('prepare')
    prep.add_argument('--owner', required=True); prep.add_argument('--runtime', required=True)
    prep.add_argument('--historical-u')
    run = sub.add_parser('one')
    for name in ('plan', 'plan-sha256', 'cases', 'runtime', 'output', 'case', 'mesh'):
        run.add_argument('--' + name, required=True)
    args = parser.parse_args()
    if args.command == 'prepare':
        print(json.dumps(prepare(args.owner, args.runtime, args.historical_u), indent=2))
        return 0
    return run_one(args)


if __name__ == '__main__':
    raise SystemExit(main())
