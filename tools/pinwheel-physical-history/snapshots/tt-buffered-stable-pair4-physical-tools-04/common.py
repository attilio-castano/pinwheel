"""Bounded, owned diagnostic execution; does not launch on import."""
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[3]
IMAGE = 'sha256:5825633bea1f9cbc705ece2de2bc31de6e4ec83d233739205a0f265ef9d92f92'
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('checkpoint_runner', ROOT / 'scripts/run-buffered-tt-physical.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def write(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + '\n')

def resolve_view(state, design, name):
    value = state.get(name)
    prefix = '/work/recovery/'
    assert isinstance(value, str) and value.startswith(prefix), (name, value)
    relative = Path(value[len(prefix):])
    assert not relative.is_absolute() and '..' not in relative.parts, (name, value)
    resolved = (design / relative).resolve()
    assert resolved.is_relative_to(design.resolve()) and resolved.is_file(), resolved
    return resolved

def cleanup_container(owner):
    """Confirm absence of this sole owned container within 3+6+3 seconds."""
    query = ['docker', 'container', 'ls', '--all', '--no-trunc', '--filter',
             'label=org.pinwheel.baseline_owner=' + owner, '--format', '{{.ID}}']
    report = {'status': 'unconfirmed', 'ownership_label': owner}
    try:
        first = subprocess.run(query, capture_output=True, text=True, timeout=3)
        if first.returncode:
            report['query_error'] = first.stderr
            return report
        identities = first.stdout.splitlines()
        import re
        assert len(identities) <= 1 and all(re.fullmatch('[0-9a-f]{64}', identity) for identity in identities)
        report['owned_container_ids'] = identities
        for identity in identities:
            subprocess.run(['docker', 'stop', '--time', '2', identity],
                           stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT, timeout=6)
        last = subprocess.run(query, capture_output=True, text=True, timeout=3)
        if last.returncode:
            report['final_query_error'] = last.stderr
        elif not last.stdout.strip():
            report['status'] = 'absent'
        else:
            report['remaining_ids'] = last.stdout.splitlines()
    except (OSError, subprocess.TimeoutExpired, AssertionError) as error:
        report['cleanup_error'] = str(error)
    return report

def execute(out, paths, argv, *, seconds, cpus, memory, schema, scope, extra=None,
            expected_hashes=None, absolute_work_stop=None, all_in_deadline_monotonic=None):
    hashes = {str(Path(path).resolve()): sha(path) for path in paths}
    for path, expected in (expected_hashes or {}).items():
        assert hashes[str(Path(path).resolve())] == expected, ('Input changed while staging', path)
    owner = str(uuid.uuid4())
    command = ['docker', 'run', '--rm', '--pull', 'never', '--network', 'none',
               '--cpus', str(cpus), '--memory', memory, '--env', 'PYTHONDONTWRITEBYTECODE=1',
               '--env', 'PYTHONPATH=/work/diagnostic', '--label', 'org.pinwheel.baseline_owner=' + owner,
               '--mount', 'type=bind,source=' + str(out) + ',target=/work/diagnostic',
               '--mount', 'type=bind,source=' + str(ROOT / 'build/physical/pdk') + ',target=/work/pdk,readonly',
               '--workdir', '/work/diagnostic', IMAGE, *argv]
    report = dict(schema=schema, status='running', input_sha256=hashes, command=command,
                  image_id=IMAGE, bounds=dict(docker_subprocess_seconds=seconds, cpus=cpus, memory=memory,
                                             network='none', cleanup_outside_subprocess_cap=True),
                  ownership_label=owner, scope=scope, **(extra or {}))
    write(out / 'report.json', report)
    started = time.monotonic()
    previous = signal.getsignal(signal.SIGTERM)
    previous_int = signal.getsignal(signal.SIGINT)
    def interrupt(*_):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        raise KeyboardInterrupt('SIGTERM')
    signal.signal(signal.SIGTERM, interrupt)
    try:
        with (out / 'execution.log').open('w') as log:
            assert absolute_work_stop is not None and all_in_deadline_monotonic is not None
            # This phase requires its full frozen native window at actual launch.
            # Owned cleanup is bounded3+6+3=12s; reserve another18s for recustody.
            assert seconds==720
            assert absolute_work_stop-time.time()>90,'Insufficient native route window'
            assert all_in_deadline_monotonic-time.monotonic()>=min(seconds,max(1,int(absolute_work_stop-time.time()-1)))+30,'Native+ownedcleanup/recustody reserve absent at actual launch'
            actual_timeout=min(seconds,max(1,int(absolute_work_stop-time.time()-1)))
            report['bounds']['owned_cleanup_max_seconds']=12
            report['bounds']['source_recustody_reserve_seconds']=18
            report['bounds']['actual_docker_subprocess_seconds']=actual_timeout
            write(out/'report.json',report)
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=actual_timeout)
        report.update(exit_code=result.returncode, status='passed' if result.returncode == 0 else 'failed')
        if result.returncode == 0:
            report['measurement'] = read(out / 'measurement.json')
            if report['measurement'].get('status') != 'measured':
                report['status'] = 'failed'
    except subprocess.TimeoutExpired as error:
        report.update(status='timed_out', error=str(error), exit_code=124)
    except KeyboardInterrupt as error:
        report.update(status='interrupted', error=str(error), exit_code=130)
    except BaseException as error:
        report.update(status='failed', error=repr(error), exit_code=1)
    finally:
        # A new interruption must not skip owned-container absence confirmation.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        try:
            report['container_termination'] = cleanup_container(owner)
            report['inputs_unchanged'] = all(sha(path) == digest for path, digest in hashes.items())
            report['elapsed_seconds'] = round(time.monotonic() - started, 3)
            report['elapsed_scope'] = 'Docker execution plus owned cleanup and source recustody; host staging precedes this timer.'
            report['artifact_sha256'] = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*'))
                                         if p.is_file() and p.name != 'report.json'}
            if not report['inputs_unchanged'] or report['container_termination']['status'] == 'unconfirmed':
                report['status'] = 'invalidated'
            write(out / 'report.json', report)
        finally:
            signal.signal(signal.SIGTERM, previous)
            signal.signal(signal.SIGINT, previous_int)
    return report
