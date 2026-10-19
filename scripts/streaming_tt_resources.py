"""Single-heavy-job admission and observable, owned cleanup for local campaigns.

This supervisor records resource/termination evidence, never proof or CAD acceptance.
Run with permission to read ps/memory_pressure and Docker for CAD jobs.
"""
import argparse
from datetime import datetime, timedelta, timezone
import fcntl
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

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'build/streaming-tt-resources'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def utc():
    return datetime.now(timezone.utc).isoformat()


def write(path, value):
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def command(argv):
    result = subprocess.run(argv, capture_output=True, text=True, timeout=10)
    require(result.returncode == 0, 'Observation failed: ' + ' '.join(argv) + ': ' + result.stderr.strip())
    return result.stdout


def processes(text):
    result = {}
    for line in text.splitlines():
        parts = line.split(None, 9)
        require(len(parts) == 10, 'Malformed process observation')
        pid, ppid, pgid, rss = map(int, parts[:4])
        result[pid] = dict(pid=pid, ppid=ppid, pgid=pgid, rss_kib=rss,
                           birth=' '.join(parts[4:9]), command=parts[9])
    return result


def process_table():
    return processes(command(['ps', '-Ao', 'pid=,ppid=,pgid=,rss=,lstart=,comm=']))


def descendants(table, root):
    owned = {root}
    while True:
        expanded = owned | {pid for pid, row in table.items() if row['ppid'] in owned}
        if expanded == owned:
            return {pid: table[pid] for pid in owned if pid in table}
        owned = expanded


def availability():
    if sys.platform == 'darwin':
        output = command(['/usr/bin/memory_pressure', '-Q'])
        match = re.search(r'System-wide memory free percentage:\s*(\d+)%', output)
        require(match is not None, 'Missing macOS memory availability')
        return int(match[1])
    data = dict((key, int(value.split()[0])) for key, value in
                (line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines()))
    return 100 * data['MemAvailable'] // data['MemTotal']


def observation():
    return dict(utc=utc(), memory_available_percent=availability(),
                disk_free_bytes=shutil.disk_usage(ROOT).free)


def gate(sample, *, admission, rss_kib=0, rss_mib=4096):
    require(0 <= sample['memory_available_percent'] <= 100, 'Invalid memory percentage')
    minimum = 25 if admission else 15
    require(sample['memory_available_percent'] >= minimum, 'Host memory below resource floor')
    require(sample['disk_free_bytes'] >= 12 * 1024 ** 3, 'Disk below 12 GiB resource floor')
    require(rss_kib <= rss_mib * 1024, 'Owned host process tree exceeded RSS limit')


def admission_window(kind, deadline, now):
    remaining = (deadline - now).total_seconds()
    require(remaining > 30, 'Campaign deadline reached')
    if kind == 'cad':
        require(now < deadline - timedelta(hours=3), 'New candidate CAD admission is closed')
    return remaining


def validation_parent(kind, path):
    require((kind == 'cad-validation') == (path is not None),
            'CAD validation requires one explicit frozen parent; other jobs cannot select it')
    if path is None:
        return None
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Frozen validation parent must be a regular file')
    path = path.resolve()
    return dict(path=str(path), sha256=file_hashes([path])[str(path)])


def file_hashes(paths):
    result = {}
    for path in paths:
        path = Path(path).resolve(strict=True)
        require(path.is_file(), 'Input is not a file: ' + str(path))
        with path.open('rb') as stream:
            result[str(path)] = hashlib.file_digest(stream, 'sha256').hexdigest()
    return result


def live_owned(table, tracked):
    # PID reuse must never authorize signaling an unrelated process.
    return {pid: table[pid] for pid, row in tracked.items()
            if pid in table and table[pid]['birth'] == row['birth']}


def signal_owned(tracked, sig):
    table = process_table()
    for pid in live_owned(table, tracked):
        try:
            os.kill(pid, sig)
        except ProcessLookupError:
            pass


def settle_owned(tracked, *, timeout_seconds=5):
    """Observe asynchronous termination; never follow a reused process identity."""
    deadline = time.monotonic() + timeout_seconds
    while True:
        remaining = live_owned(process_table(), tracked)
        if not remaining or time.monotonic() >= deadline:
            return remaining
        time.sleep(.05)


def docker_ids(name):
    ids = command(['docker', 'ps', '--all', '--no-trunc', '--filter',
                   'name=^/' + name + '$', '--format', '{{.ID}}']).splitlines()
    require(all(re.fullmatch(r'[0-9a-f]{64}', identity) for identity in ids), 'Invalid container identity')
    return ids


def container_observation(name):
    identities = docker_ids(name)
    require(len(identities) <= 1, 'Ambiguous container ownership')
    if not identities:
        return None
    try:
        info = json.loads(command(['docker', 'inspect', identities[0]]))[0]
    except (ValueError, subprocess.SubprocessError):
        current = docker_ids(name)
        require(len(current) <= 1, 'Ambiguous container ownership')
        if identities[0] not in current:
            return dict(id=identities[0], running=False, removed_during_observation=True,
                        replacement_container_ids=current)
        raise
    config = info['HostConfig']
    require(0 < config['Memory'] <= 6 * 1024 ** 3, 'Container memory is unbounded or exceeds 6 GiB')
    require(config['MemorySwap'] == config['Memory'], 'Container swap must be disabled explicitly')
    require(0 < config['NanoCpus'] <= 4 * 10 ** 9, 'Container CPU bound missing or exceeds four')
    require(config['NetworkMode'] == 'none', 'Heavy CAD must run offline')
    if not info['State']['Running']:
        return dict(id=identities[0], running=False)
    try:
        output = command(['docker', 'stats', '--no-stream', '--format', '{{.MemPerc}}', identities[0]])
        percent = float(output.strip().removesuffix('%'))
    except (ValueError, subprocess.SubprocessError):
        current = docker_ids(name)
        require(len(current) <= 1, 'Ambiguous container ownership')
        if identities[0] not in current:
            return dict(id=identities[0], running=False, removed_during_observation=True,
                        replacement_container_ids=current)
        raise
    require(0 <= percent <= 100, 'Invalid container memory observation')
    require(percent < 95, 'Container approaching memory limit')
    return dict(id=identities[0], running=True, memory_percent=percent,
                memory_limit_bytes=config['Memory'], memory_swap_bytes=config['MemorySwap'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--kind', choices=('lean', 'cad', 'cad-validation', 'host'), required=True)
    parser.add_argument('--timeout-seconds', type=int, required=True)
    parser.add_argument('--rss-mib', type=int, default=4096)
    parser.add_argument('--container-name')
    parser.add_argument('--input', type=Path, action='append', default=[])
    parser.add_argument('--validation-parent', type=Path,
                        help='Frozen existing artifact or receipt for CAD checks during the validation reserve')
    parser.add_argument('--deadline', default='2026-10-19T03:26:07+00:00')
    parser.add_argument('argv', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    require(re.fullmatch(r'[a-zA-Z0-9_-]+', args.tag), 'Unsafe attempt tag')
    require(1 <= args.timeout_seconds <= 14400, 'Invalid wall-time bound')
    require(128 <= args.rss_mib <= 6144, 'RSS bound outside campaign policy')
    if args.container_name:
        require(re.fullmatch(r'pinwheel-[a-zA-Z0-9_-]+', args.container_name), 'Unsafe owned container name')
    require(args.kind not in ('cad', 'cad-validation') or args.container_name,
            'CAD needs an exact owned container name')
    argv = args.argv[1:] if args.argv[:1] == ['--'] else args.argv
    require(argv, 'Missing command')
    deadline = datetime.fromisoformat(args.deadline)
    require(deadline.tzinfo is not None, 'Deadline requires timezone')
    remaining = admission_window(args.kind, deadline, datetime.now(timezone.utc))
    parent = validation_parent(args.kind, args.validation_parent)
    if parent is not None:
        args.input.append(Path(parent['path']))
    timeout = min(args.timeout_seconds, remaining - 20)
    BASE.mkdir(parents=True, exist_ok=True)
    require(not (BASE / 'cleanup-unconfirmed.json').exists(), 'Previous cleanup needs inspection')
    with (BASE / 'heavy.lock').open('a+') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ValueError('Another heavy job holds the lease') from error
        require(not (BASE / 'cleanup-unconfirmed.json').exists(), 'Previous cleanup needs inspection')
        out = BASE / args.tag
        out.mkdir(exist_ok=False)
        receipt = dict(schema='pinwheel.streaming-tt-resource-job.v1', qualified=False,
                       acceptance_claim=False, started_utc=utc(), argv=argv, kind=args.kind,
                       timeout_seconds=timeout, rss_mib=args.rss_mib, status='preflight',
                       validation_parent=parent,
                       supervisor_sha256=file_hashes([Path(__file__)])[str(Path(__file__).resolve())],
                       input_sha256=file_hashes(args.input), observations=[])
        target = out / 'report.json'
        tracked = {}
        process = None
        stop = None
        started = time.monotonic()
        previous_handlers = {}
        def interrupted(signum, frame):
            if signum == signal.SIGALRM:
                raise TimeoutError('Wall-time bound reached')
            raise InterruptedError('Signal ' + str(signum))
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGALRM):
            previous_handlers[sig] = signal.signal(sig, interrupted)
        try:
            sample = observation()
            gate(sample, admission=True)
            receipt['observations'].append(sample)
            table = process_table()
            foreign = [row for row in table.values() if Path(row['command']).name in ('lean', 'openroad', 'yosys')]
            require(not foreign, 'Existing Native proof/CAD process prevents admission')
            if shutil.which('docker'):
                require(not command(['docker', 'ps', '-q']).strip(), 'Existing container prevents heavy admission')
            if args.kind in ('cad', 'cad-validation'):
                require(not docker_ids(args.container_name), 'Container name already exists')
            write(target, receipt)
            with (out / 'native.log').open('w') as log:
                process = subprocess.Popen(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                           start_new_session=True)
                receipt.update(status='running', pid=process.pid)
                signal.setitimer(signal.ITIMER_REAL, max(.001, timeout - (time.monotonic() - started)))
                while process.poll() is None:
                    table = process_table()
                    current = live_owned(table, tracked)
                    current.update(descendants(table, process.pid))
                    current.update({pid: row for pid, row in table.items() if row['pgid'] == process.pid})
                    tracked.update(current)
                    sample = observation()
                    sample['owned_host_rss_kib'] = sum(row['rss_kib'] for row in current.values())
                    if args.container_name:
                        sample['container'] = container_observation(args.container_name)
                    receipt['observations'].append(sample)
                    gate(sample, admission=False, rss_kib=sample['owned_host_rss_kib'], rss_mib=args.rss_mib)
                    require(time.monotonic() - started < timeout, 'Wall-time bound reached')
                    write(target, receipt)
                    time.sleep(3)
                receipt.update(exit_code=process.returncode,
                               status='completed' if process.returncode == 0 else 'failed')
        except (OSError, ValueError, subprocess.SubprocessError) as error:
            stop = type(error).__name__ + ': ' + str(error)
            receipt.update(status='stopped', stop_reason=stop, exit_code=124)
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            for sig, handler in previous_handlers.items():
                signal.signal(sig, handler)
            cleanup_errors = []
            try:
                if process is not None:
                    table = process_table()
                    tracked.update(descendants(table, process.pid))
                    tracked.update({pid: row for pid, row in table.items() if row['pgid'] == process.pid})
                    signal_owned(tracked, signal.SIGTERM)
                if process is not None and args.container_name:
                    for identity in docker_ids(args.container_name):
                        command(['docker', 'stop', '--time', '5', identity])
                if process is not None:
                    try:
                        process.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        signal_owned(tracked, signal.SIGKILL)
                        process.wait(timeout=5)
                    # Also kill tracked orphaned subgroups from a failed controller.
                    signal_owned(tracked, signal.SIGKILL)
                # SIGKILL delivery is asynchronous. A single immediate ps can
                # still see the dying child even though no work can continue.
                # Require actual absence within a bounded observation window.
                remaining_owned = settle_owned(tracked) if process is not None else {}
                receipt['owned_processes_remaining'] = list(remaining_owned)
                require(not remaining_owned, 'Owned Native processes remain')
                receipt['cleanup_scope'] = 'spawned_controller_and_observed_children' if process is not None else 'no_job_spawned'
                if process is not None and args.container_name:
                    receipt['containers_remaining'] = docker_ids(args.container_name)
                    require(not receipt['containers_remaining'], 'Owned container remains')
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                cleanup_errors.append(str(error))
            receipt['cleanup_confirmed'] = not cleanup_errors
            receipt['cleanup_errors'] = cleanup_errors
            if cleanup_errors:
                receipt['status'] = 'cleanup_unconfirmed'
                write(BASE / 'cleanup-unconfirmed.json', dict(attempt=str(out), errors=cleanup_errors))
            try:
                receipt['inputs_unchanged'] = file_hashes(args.input) == receipt['input_sha256']
            except OSError:
                receipt['inputs_unchanged'] = False
            if not receipt['inputs_unchanged']:
                receipt['status'] = 'invalidated'
            receipt.update(finished_utc=utc(), elapsed_seconds=round(time.monotonic() - started, 3))
            write(target, receipt)
        print(target)
        return 0 if receipt['status'] == 'completed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
