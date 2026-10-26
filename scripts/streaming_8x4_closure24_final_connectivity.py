"""New24 coordinator for unchanged read-only native Boolean ODB export.

Root must launch `run` through the shared campaign resource supervisor. The
historical HOST coordinator is neither patched nor given a translated receipt.
This producer authenticates the new 8x4 authority, uses the unchanged native
exporter's actual object traversal, and emits a new scoped closeout. Later
physical-check failure is preserved when DetailedRouting itself completed.
No proof, final-wire, layout, timing or tapeout acceptance follows from export.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
import uuid

import streaming_8x4_prepare as P
import streaming_8x4_closure24_final_target as T
from streaming_8x4_geometry import regular, require, sha
from streaming_8x4_run import cleanup

CAMPAIGN = 'build/campaigns/8x4-20261024-01'


def owned(path, workspace):
    path = Path(path).absolute()
    campaign = (Path(workspace).resolve(strict=True) / CAMPAIGN).resolve()
    require(path.resolve().is_relative_to(campaign) and path.resolve() != campaign,
            'New24 final coordinator output must have its own new campaign owner')
    return path


def prepare(report, report_sha256, prepared, reference, output):
    from streaming_tt_intake import dependency_closure
    request = T.request(report, report_sha256, prepared, reference)
    output = owned(output, P.ROOT)
    require(not output.exists(), 'Preserve earlier final-connectivity preparation')
    closure = dependency_closure(P.ROOT, ['scripts/streaming_8x4_closure24_final_connectivity.py',
                                        'scripts/streaming_tt_export_odb.py', 'tools/physical-toolchain.json'])
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=P.ROOT, text=True, timeout=30).strip()
    sources = {}
    for name in closure['files']:
        source = regular(P.ROOT / name)
        committed = subprocess.check_output(['git', 'show', commit + ':' + name], cwd=P.ROOT, timeout=30)
        require(hashlib.sha256(committed).hexdigest() == sha(source), 'Commit final-connectivity producer first: ' + name)
        sources[name] = sha(source)
    inputs = output / 'inputs'; inputs.mkdir(parents=True)
    for name in sources:
        target = inputs / 'producer' / name; target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(P.ROOT / name, target)
    for name, binding in [('actual.odb', request['target']['actual_odb']),
                          ('reference.json', request['original_flat_reference']),
                          ('export.py', request['native_exporter'])]:
        require(sha(binding['path']) == binding['sha256'], 'Final export staging source changed')
        shutil.copyfile(binding['path'], inputs / name)
        require(sha(inputs / name) == binding['sha256'], 'Final export staged input differs')
    (inputs / 'launch.py').write_text('import runpy,sys\nsys.argv=' + repr(request['native_exporter_argv']) +
                                     '\nrunpy.run_path("/inputs/export.py",run_name="__main__")\n')
    P.write(inputs / 'request.json', request)
    for path in inputs.rglob('*'):
        if path.is_file(): path.chmod(0o444)
    packet = dict(schema='pinwheel.closure24-final-connectivity-preparation.v1', producer_commit=commit,
        workspace_root=str(P.ROOT), producer_sha256=sources, producer_dependency_closure=closure,
        input_sha256=P.inventory(inputs), request=request, native_executed=False,
        qualified=False, physical_acceptance=False, final_correspondence_proved=False)
    P.write(output / 'preparation.json', packet)
    return packet


def verify(output, workspace):
    from streaming_tt_intake import dependency_closure
    workspace = Path(workspace).resolve(strict=True); output = owned(output, workspace)
    P.ROOT = workspace
    packet = P.read(output / 'preparation.json')
    require(packet.get('schema') == 'pinwheel.closure24-final-connectivity-preparation.v1' and
            P.inventory(output / 'inputs') == packet.get('input_sha256'), 'Frozen final-export inputs changed')
    request = packet['request']
    require(P.read(output / 'inputs/request.json') == request, 'Staged final export request changed')
    require(Path(packet['workspace_root']).resolve() == workspace, 'Final export workspace authority changed')
    for name, expected in packet['producer_sha256'].items():
        require(sha(workspace / name) == expected == sha(output / 'inputs/producer' / name),
                'Final export producer changed: ' + name)
        committed = subprocess.check_output(['git', 'show', packet['producer_commit'] + ':' + name],
                                            cwd=workspace, timeout=30)
        require(hashlib.sha256(committed).hexdigest() == expected, 'Final export source is not its recorded commit')
    require(dependency_closure(workspace, ['scripts/streaming_8x4_closure24_final_connectivity.py',
            'scripts/streaming_tt_export_odb.py', 'tools/physical-toolchain.json']) == packet['producer_dependency_closure'],
            'Final export producer closure changed')
    prepared = Path(request['preparation']['path']).parent
    require(sha(request['preparation']['path']) == request['preparation']['sha256'], '8x4 physical preparation changed')
    actual_preparation = P.verify(prepared)
    target = request['target']
    require(T.select_report(target['physical_report']['path'], target['physical_report']['sha256'],
                            prepared, actual_preparation) == target, 'Actual final-target authority changed')
    require(request.get('physical_candidate') == T.candidate_identity(target, prepared),
            'Final export changes the explicitly selected physical candidate')
    for key in ('original_flat_reference', 'native_exporter'):
        require(sha(request[key]['path']) == request[key]['sha256'], 'Final export reference/source changed')
    require(sha(output / 'inputs/export.py') == T.NATIVE_EXPORTER_SHA256 and
            sha(output / 'inputs/actual.odb') == target['actual_odb']['sha256'] and
            sha(output / 'inputs/reference.json') == T.FLAT_REFERENCE_SHA256,
            'Canonical native export staged bytes differ')
    return packet


def command(output, image, name, owner):
    require(re.fullmatch(r'pinwheel-[A-Za-z0-9_-]+', name) and
            re.fullmatch(r'[0-9a-f-]{36}', owner) and re.fullmatch(r'sha256:[0-9a-f]{64}', image),
            'Unsafe final export runtime/ownership')
    return ['docker', 'run', '--rm', '--pull', 'never', '--name', name,
            '--label', 'org.pinwheel.streaming8_owner=' + owner, '--network', 'none', '--cpus', '1',
            '--memory', '2048m', '--memory-swap', '2048m', '--read-only', '--cap-drop', 'ALL',
            '--security-opt', 'no-new-privileges', '--env', 'PYTHONDONTWRITEBYTECODE=1',
            '--mount', f'type=bind,source={output / "inputs"},target=/inputs,readonly',
            '--mount', f'type=bind,source={output / "native"},target=/outputs', '--workdir', '/outputs', image,
            'openroad', '-no_init', '-exit', '-python', '/inputs/launch.py']


def validate_native(output, packet):
    directory = output / 'native/export'; path = regular(directory / 'receipt.json')
    native = P.read(path); request = packet['request']
    require(native.get('schema') == 'pinwheel.streaming-tt-odb-export.v1' and
            native.get('read_only_database') is True and native.get('top') == T.TOP and
            native.get('database_sha256') == request['target']['actual_odb']['sha256'] and
            native.get('reference_sha256') == T.FLAT_REFERENCE_SHA256 and
            native.get('source_sha256') == T.NATIVE_EXPORTER_SHA256 and
            set(native.get('artifacts_sha256', {})) == {'connectivity.json', 'inventory.json'},
            'Canonical native export does not bind the exact actual target/reference/source')
    for name, expected in native['artifacts_sha256'].items():
        require(sha(directory / name) == expected, 'Native final-connectivity output changed')
    return dict(path=str(path), sha256=sha(path), database_sha256=native['database_sha256'],
                artifact_sha256=native['artifacts_sha256'])


def run(output, workspace, name, timeout=120, *, frozen=False):
    from streaming_tt_physical import inspect_runtime
    output = Path(output).absolute(); workspace = Path(workspace).resolve(strict=True)
    packet = verify(output, workspace)
    worker = regular(output / 'inputs/producer/scripts/streaming_8x4_closure24_final_connectivity.py')
    if not frozen:
        os.execv(sys.executable, [sys.executable, '-B', str(worker), 'run', '--output', str(output),
            '--workspace', str(workspace), '--name', name, '--timeout-seconds', str(timeout), '--frozen'])
    require(Path(__file__).resolve() == worker.resolve(), 'Execute the frozen final-connectivity producer')
    require(1 <= timeout <= 120 and set(path.name for path in output.iterdir()) == {'inputs', 'preparation.json'},
            'Fresh final-connectivity output and at most 120 Native seconds required')
    (output / 'native').mkdir()
    runtime = inspect_runtime(P.read(workspace / 'tools/physical-toolchain.json'))
    owner = str(uuid.uuid4()); argv = command(output, runtime['image_id'], name, owner)
    before = sha(output / 'preparation.json'); started = time.monotonic()
    request = packet['request']; target = request['target']
    receipt = dict(schema='pinwheel.closure24-final-connectivity-run.v1', passed=False,
        status='running', argv=argv, runtime=runtime, ownership_label=owner,
        preparation=dict(path=str(output / 'preparation.json'), sha256=before),
        producer_commit=packet['producer_commit'], source_candidate_commit=request['source_candidate_commit'],
        physical_candidate=request['physical_candidate'],
        source_sha256=packet['producer_sha256'], target=target, timeout_seconds=timeout,
        started_utc=datetime.now(timezone.utc).isoformat(), qualified=False, physical_acceptance=False,
        final_correspondence_proved=False, physical_original_status=target['physical_status'],
        boundary='Fresh read-only Boolean connectivity export only; later physical failures remain failures.')
    previous = signal.getsignal(signal.SIGTERM)
    def interrupted(signum, frame): raise KeyboardInterrupt('signal ' + str(signum))
    signal.signal(signal.SIGTERM, interrupted)
    P.write(output / 'report.json', receipt)
    with (output / 'native.log').open('w') as log:
        try:
            result = subprocess.run(argv, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
            receipt.update(exit_code=result.returncode, status='exported' if result.returncode == 0 else 'failed')
        except subprocess.TimeoutExpired: receipt.update(exit_code=124, status='timed_out')
        except KeyboardInterrupt as error: receipt.update(exit_code=130, status='interrupted', error=str(error))
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            receipt.update(exit_code=127, status='blocked', error=type(error).__name__ + ': ' + str(error))
        finally:
            receipt['container_termination'] = cleanup(owner, log)
            signal.signal(signal.SIGTERM, previous)
            try:
                require(sha(output / 'preparation.json') == before and verify(output, workspace) == packet,
                        'Final export authority/input closure changed')
                require(inspect_runtime(P.read(workspace / 'tools/physical-toolchain.json')) == runtime,
                        'Final export runtime changed')
                receipt['inputs_runtime_unchanged'] = True
                if receipt.get('exit_code') == 0 and receipt['status'] == 'exported':
                    receipt['native_binding'] = validate_native(output, packet)
                    require(receipt['container_termination']['status'] == 'absent', 'Final export cleanup is unconfirmed')
                    receipt['passed'] = True
            except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
                receipt.update(passed=False, status='invalidated', closeout_error=type(error).__name__ + ': ' + str(error))
            if receipt['container_termination']['status'] != 'absent':
                receipt.update(passed=False, status='cleanup_unconfirmed')
            receipt.update(elapsed_seconds=time.monotonic() - started, finished_utc=datetime.now(timezone.utc).isoformat())
            log.flush()
            receipt['artifact_sha256'] = {str(path.relative_to(output)): sha(path)
                for path in sorted((output / 'native').rglob('*')) if path.is_file()}
            receipt['native_log_sha256'] = sha(output / 'native.log')
            P.write(output / 'report.json', receipt)
    print(output / 'report.json', flush=True)
    return 0 if receipt['passed'] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest='mode', required=True)
    pre = modes.add_parser('prepare')
    for name in ('physical-report', 'prepared', 'reference', 'output'): pre.add_argument('--' + name, type=Path, required=True)
    pre.add_argument('--physical-report-sha256', required=True)
    execute = modes.add_parser('run')
    execute.add_argument('--output', type=Path, required=True)
    execute.add_argument('--workspace', type=Path, required=True)
    execute.add_argument('--name', required=True)
    execute.add_argument('--timeout-seconds', type=int, default=120)
    execute.add_argument('--frozen', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.mode == 'prepare':
        prepare(args.physical_report, args.physical_report_sha256, args.prepared, args.reference, args.output)
        print(args.output / 'preparation.json'); return 0
    return run(args.output, args.workspace, args.name, args.timeout_seconds, frozen=args.frozen)


if __name__ == '__main__': raise SystemExit(main())
