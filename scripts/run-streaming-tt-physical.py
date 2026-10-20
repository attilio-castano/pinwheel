#!/usr/bin/env python3
"""One owned, offline, bounded physical producer; never a qualification verdict."""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid

from streaming_tt_physical import BASE, ROOT, BOUNDARY, inspect_runtime, read, regular, require, safe_name, sha, verify_prepared, write


STOPS = ('OpenROAD.Floorplan', 'OpenROAD.GlobalPlacement', 'OpenROAD.CTS', 'OpenROAD.STAMidPNR-2',
    'OpenROAD.GlobalRouting', 'OpenROAD.STAMidPNR-3')


def cleanup(owner, log):
    result = dict(status='unconfirmed', ownership_label=owner)
    query = ['docker', 'container', 'ls', '--all', '--no-trunc', '--filter',
        'label=org.pinwheel.streaming_tt_owner=' + owner, '--format', '{{.ID}}']
    try:
        response = subprocess.run(query, capture_output=True, text=True, timeout=10)
        require(response.returncode == 0, 'Owned-container query failed: ' + response.stderr.strip())
        identities = response.stdout.splitlines()
        require(all(len(identity) == 64 and all(c in '0123456789abcdef' for c in identity) for identity in identities),
            'Malformed owned-container identity')
        result['owned_container_ids'] = identities
        for identity in identities:
            response = subprocess.run(['docker', 'stop', '--time', '10', identity], stdout=log, stderr=subprocess.STDOUT, timeout=30)
            require(response.returncode == 0, 'Owned-container stop failed')
        response = subprocess.run(query, capture_output=True, text=True, timeout=10)
        require(response.returncode == 0, 'Final owned-container query failed')
        result.update(status='absent' if not response.stdout.strip() else 'unconfirmed', remaining=response.stdout.splitlines())
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        result['error'] = type(error).__name__ + ': ' + str(error)
    return result


def container_command(design, output, runtime, tag, owner, stop):
    return ['docker', 'run', '--rm', '--pull', 'never', '--name', 'pinwheel-' + tag,
        '--label', 'org.pinwheel.streaming_tt_owner=' + owner, '--network', 'none', '--cpus', '4', '--memory', '6g',
        '--memory-swap', '6g',
        '--env', 'PYTHONPATH=/work/inputs', '--env', 'PYTHONDONTWRITEBYTECODE=1',
        '--mount', 'type=bind,source=' + str(design / 'inputs') + ',target=/work/inputs,readonly',
        '--mount', 'type=bind,source=' + str(design / 'pdk') + ',target=/work/pdk,readonly',
        '--mount', 'type=bind,source=' + str(output) + ',target=/work/run',
        '--workdir', '/work/inputs', runtime['image_id'], 'python3', '-B', '-m', 'librelane',
        '--manual-pdk', '--pdk-root', '/work/pdk', '--pdk', 'ihp-sg13cmos5l', '--jobs', '4',
        '--run-tag', tag, '--force-run-dir', '/work/run', '--with-initial-state', '/work/inputs/seed.json',
        '--to', stop, '/work/inputs/core.json']


def collect_states(output, design):
    """Keep carried NL distinct from authoritative ODB, including partial failures."""
    roots = {'/work/run': output, '/work/inputs': design / 'inputs', '/work/pdk': design / 'pdk'}
    def resolve(value):
        if isinstance(value, dict): return {key: resolve(child) for key, child in value.items()}
        if isinstance(value, list): return [resolve(child) for child in value]
        if not isinstance(value, str): return value
        for prefix, host in roots.items():
            if value.startswith(prefix + '/'):
                path = host / value[len(prefix) + 1:]
                require(path.resolve().is_relative_to(host.resolve()), 'Tool-generated physical view escapes its mounted root')
                if path.is_file(): return dict(container=value, path=str(path), sha256=sha(path))
        return value
    states = []
    for path in sorted(output.rglob('state_out.json')):
        value = read(path)
        states.append(dict(state=str(path), state_sha256=sha(path), step_directory=path.parent.name,
            metrics=value.get('metrics', {}), views=resolve({key: data for key, data in value.items() if key != 'metrics'}),
            authoritative_physical_view='odb', carried_netlist_requires_ODB_reexport=True))
    return states


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--design', required=True)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--to', choices=STOPS, default='OpenROAD.STAMidPNR-3')
    parser.add_argument('--timeout-seconds', type=int, default=3600)
    parser.add_argument('--frozen-input',type=Path,help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.frozen_input is not None:
        # Initial live imports are hash-verified before CAD. Re-exec then runs
        # the byte-identical worker and its imports from the staged snapshot.
        metadata = read(regular(args.frozen_input))
        require(metadata.get('schema') == 'pinwheel.streaming-tt-physical-input.v2', 'Invalid frozen worker input')
        global ROOT, BASE
        import streaming_tt_physical as physical
        ROOT = physical.ROOT = Path(metadata['workspace_root']).resolve()
        BASE = physical.BASE = ROOT/'build/physical'
        require(args.frozen_input.resolve() == (BASE/args.design/'inputs.json').resolve() and
            Path(__file__).resolve() == (BASE/args.design/'inputs/producer/scripts/run-streaming-tt-physical.py').resolve(),
            'Frozen worker is not the selected staged producer')
    safe_name(args.design); safe_name(args.tag)
    require(1 <= args.timeout_seconds <= 14400, 'Attempt wall-time must be1..14400 seconds')
    design = BASE / args.design
    inputs = verify_prepared(design)
    if inputs.get('schema') == 'pinwheel.streaming-tt-physical-input.v2' and args.frozen_input is None:
        worker = regular(design/'inputs/producer/scripts/run-streaming-tt-physical.py')
        require(sha(worker) == inputs['producer_sha256']['scripts/run-streaming-tt-physical.py'], 'Frozen worker changed before use')
        os.execv(sys.executable,[sys.executable,'-B',str(worker),'--design',args.design,'--tag',args.tag,
            '--to',args.to,'--timeout-seconds',str(args.timeout_seconds),'--frozen-input',str(design/'inputs.json')])
    # All executed producer bytes must be committed before a native attempt.
    for name, expected in inputs['producer_sha256'].items():
        data = subprocess.check_output(['git', 'show', inputs.get('producer_commit','HEAD') + ':' + name], cwd=ROOT, timeout=30)
        import hashlib
        require(hashlib.sha256(data).hexdigest() == expected, 'Uncommitted physical producer: ' + name)
    run = BASE / args.tag
    require(not run.exists(), 'Preserve prior physical attempts; choose a fresh tag')
    run.mkdir(parents=True)
    output = run / 'flow'; output.mkdir()
    owner = str(uuid.uuid4())
    lock_path = BASE / 'streaming-tt-active.json'
    descriptor = os.open(lock_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, 'w') as stream:
        json.dump(dict(owner=owner, pid=os.getpid(), tag=args.tag), stream)
    receipt_path = run / 'report.json'
    receipt = dict(schema='pinwheel.streaming-tt-physical-run.v2' if args.frozen_input else 'pinwheel.streaming-tt-physical-run.v1', qualified=False, physical_acceptance_claim=False,
        post_pnr_equivalence_proved=False, status='preflight', tag=args.tag, design=str(design),
        source_commit=inputs.get('producer_commit') or subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, timeout=30).decode().strip(),
        started_utc=datetime.now(timezone.utc).isoformat(), prepared_input_sha256=sha(design / 'inputs.json'),
        producer_sha256=inputs['producer_sha256'], ownership_label=owner, timeout_seconds=args.timeout_seconds,
        stop_step=args.to, cpus=4, memory='6g', memory_swap='6g', network='none', boundary=BOUNDARY,
        input_mount_readonly=True, pdk_mount_readonly=True,
        path_map={'/work/run': str(output), '/work/inputs': str(design / 'inputs'), '/work/pdk': str(design / 'pdk')})
    if args.frozen_input:
        receipt.update(recipe=inputs['recipe'],executed_staged_producer=str(Path(__file__).resolve()),
            candidate_source_commit=inputs['candidate']['source_commit'],parent_admitted_scope='through_global_route_only',
            frozen_lean_replay_status_at_intake=inputs['candidate']['replay_status'],nominal_wire_rc=inputs['nominal_wire_rc'])
    started = time.monotonic(); process = None
    previous = signal.getsignal(signal.SIGTERM)
    def interrupted(signum, frame): raise KeyboardInterrupt('signal ' + str(signum))
    signal.signal(signal.SIGTERM, interrupted)
    write(receipt_path, receipt)
    with (run / 'native.log').open('w') as log:
        try:
            receipt['runtime'] = inspect_runtime(read(ROOT / 'tools/physical-toolchain.json'))
            command = container_command(design, output, receipt['runtime'], args.tag, owner, args.to)
            receipt.update(status='running', command=command)
            write(receipt_path, receipt)
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            code = process.wait(timeout=args.timeout_seconds)
            receipt.update(exit_code=code, status='flow_completed' if code == 0 else 'failed')
        except subprocess.TimeoutExpired:
            receipt.update(exit_code=124, status='timed_out', stop_reason='wall_time_limit')
        except KeyboardInterrupt as error:
            receipt.update(exit_code=130, status='interrupted', stop_reason=str(error))
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            receipt.update(exit_code=127, status='blocked', error=type(error).__name__ + ': ' + str(error))
        finally:
            write(receipt_path, receipt)
            receipt['container_termination'] = cleanup(owner, log)
            if process is not None and process.poll() is None:
                try: process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGTERM)
                    try: process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL); process.wait(timeout=5)
            signal.signal(signal.SIGTERM, previous)
            if receipt['container_termination']['status'] != 'absent': receipt['status'] = 'cleanup_unconfirmed'
            try:
                verify_prepared(design); receipt['inputs_unchanged_after_run'] = True
            except (OSError, ValueError) as error:
                receipt.update(inputs_unchanged_after_run=False, status='invalidated', closeout_error=str(error))
            receipt['elapsed_seconds'] = round(time.monotonic() - started, 3)
            receipt['states'] = collect_states(output, design)
            receipt['artifact_sha256'] = {str(path.relative_to(run)): sha(path) for path in sorted(run.rglob('*'))
                if path.is_file() and path != receipt_path}
            write(receipt_path, receipt)
            if receipt['container_termination']['status'] == 'absent' and read(lock_path)['owner'] == owner:
                lock_path.unlink()
    print(receipt_path)
    return receipt.get('exit_code', 127) or (3 if receipt['status'] != 'flow_completed' else 0)


if __name__ == '__main__': raise SystemExit(main())
