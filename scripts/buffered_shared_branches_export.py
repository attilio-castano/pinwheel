"""Whole-case native export supervisor; no evaluator replacement.

Invoke under validation_run.Commands, so all exporter processes inherit its
managed process group. This module does not create a new session or mutate
shared command runners. Keep interpreter/native parity before calling it.
"""
import argparse
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

INPUT_SCHEMA = 'pinwheel-buffered-shared-branches-input-v1'
VECTOR_SCHEMA = 'pinwheel-buffered-shared-branches-vectors-v1'
ARTIFACTS = ('core.mlir', 'assembly.json')
CHECKER_PATH = Path(__file__).resolve().with_name('check-buffered-shared-branches.py')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_checker(path):
    resolved = Path(path).resolve(strict=True)
    require(resolved == CHECKER_PATH.resolve(strict=True), 'Checker must be the exact shared-branches gate')
    sys.path.insert(0, str(resolved.parent))
    spec = importlib.util.spec_from_file_location('shared_export_checker', resolved)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    checker = module.check_export
    require(callable(checker), 'Gate check_export is not callable')
    return checker


def plan(request, jobs=4):
    require(type(jobs) is int and 1 <= jobs <= 4, 'Export jobs must be an integer from 1 to 4')
    require(request.get('schema') == INPUT_SCHEMA, 'Wrong export request schema')
    cases = request.get('cases')
    require(isinstance(cases, list) and bool(cases), 'Export request needs cases')
    names = [c.get('name') for c in cases]
    require(all(type(n) is str and n for n in names), 'Invalid requested case name')
    require(len(names) == len(set(names)), 'Duplicate requested case name')
    require(all(isinstance(c.get('vectors'), list) for c in cases), 'Invalid requested vectors')
    count = min(jobs, len(cases))
    groups, loads = [[] for _ in range(count)], [0] * count
    for index in sorted(range(len(cases)), key=lambda k: (-len(cases[k]['vectors']), k)):
        shard = min(range(count), key=lambda k: (loads[k], k))
        groups[shard].append(index)
        loads[shard] += len(cases[index]['vectors'])
    return [dict(index=k, indices=sorted(indices), edges=loads[k])
            for k, indices in enumerate(groups) if indices]


def strict_json(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def merge(request, plans, exported):
    require(len(plans) == len(exported), 'Missing exported shard')
    expected = request['cases']
    indices = [k for shard in plans for k in shard['indices']]
    require(all(type(k) is int for k in indices) and sorted(indices) == list(range(len(expected))),
            'Shard plan omits or duplicates requested indices')
    combined = [None] * len(expected)
    for shard, result in zip(plans, exported, strict=True):
        require(result.get('schema') == VECTOR_SCHEMA, 'Wrong exported vectors schema')
        cases = result.get('cases')
        require(isinstance(cases, list), 'Missing exported cases')
        names = [c.get('name') for c in cases]
        wanted = [expected[k]['name'] for k in shard['indices']]
        require(names == wanted, 'Shard case order or coverage differs')
        for index, actual in zip(shard['indices'], cases, strict=True):
            vectors = actual.get('vectors')
            before = expected[index]['vectors']
            require(isinstance(vectors, list) and len(vectors) == len(before), 'Changed exported edge count')
            for source, value in zip(before, vectors, strict=True):
                require(strict_json(value.get('command')) == strict_json(source.get('command')),
                        'Changed exported command transcript')
                require(type(value.get('raw_inputs')) is int and
                        strict_json(value['raw_inputs']) == strict_json(source.get('raw_inputs')),
                        'Changed exported raw-input transcript')
                require(isinstance(value.get('state'), dict), 'Missing exported public state')
            require(combined[index] is None, 'Duplicate exported index')
            combined[index] = actual
    require(all(c is not None for c in combined), 'Missing exported index')
    return dict(schema=VECTOR_SCHEMA, cases=combined)


def validate_artifacts(directories, reference):
    result = {}
    for name in ARTIFACTS:
        before = (Path(reference) / name).read_bytes()
        for directory in directories:
            require((Path(directory) / name).read_bytes() == before,
                    'Export shard differs from native parity artifact: ' + name)
        result[name] = hashlib.sha256(before).hexdigest()
    return result


def supervise(executable, request_path, out, reference, *, jobs=4, timeout=1800, grace=0.5, validator=None):
    """Bounded supervisor; direct children inherit the caller's process group.

    Normal failure never returns until every exporter has been reaped. The
    existing outer Commands/process_group timeout is the final cancellation
    bound if a direct child fails to terminate. Reports may remain partial if
    that outer helper escalates to SIGKILL before this supervisor can finish.
    """
    require(callable(validator), 'A callable independent check_export validator is required')
    require(type(timeout) in (int, float) and math.isfinite(timeout) and timeout > 0,
            'Invalid export timeout')
    require(type(grace) in (int, float) and 0 < grace <= 1, 'Invalid cleanup grace')
    out, reference, request_path = Path(out), Path(reference), Path(request_path)
    request = json.loads(request_path.read_text())
    plans = plan(request, jobs)
    directory = out / 'export-shards'
    directory.mkdir(exist_ok=False)
    for name in (*ARTIFACTS, 'vectors.json'):
        require(not (out / name).exists(), 'Preserve earlier export artifact: ' + name)
    # Read/validate the passed parity anchor before launching any worker.
    for name in ARTIFACTS:
        (reference / name).read_bytes()
    records, children, logs = [], [], []
    started = time.monotonic()
    report = dict(schema='pinwheel-buffered-shared-branches-shards-v1', status='running',
        jobs=len(plans), cases=len(request['cases']), edges=sum(p['edges'] for p in plans),
        request_sha256=digest(request_path), timeout_seconds=timeout,
        process_group=os.getpgrp(), commands=records, shards=plans)
    report_path = directory / 'report.json'
    def save():
        scratch = directory / 'report.tmp'
        scratch.write_text(json.dumps(report, indent=2, allow_nan=False) + '\n')
        scratch.replace(report_path)
    cancelled = {'signal': None}
    def active():
        require(cancelled['signal'] is None, 'Export supervisor cancelled')
    def cancel(signum, _frame):
        # A flag avoids interrupting Popen before the child handle is retained.
        cancelled['signal'] = signum
    previous = {s: signal.getsignal(s) for s in (signal.SIGTERM, signal.SIGINT)}
    for s in previous:
        signal.signal(s, cancel)
    save()
    failure = None
    try:
        for shard in plans:
            active()
            own = directory / f"shard-{shard['index']:02d}"
            own.mkdir()
            subset = dict(schema=request['schema'], cases=[request['cases'][k] for k in shard['indices']])
            path = own / 'input.json'
            path.write_text(json.dumps(subset, indent=2) + '\n')
            target = own / 'output'
            target.mkdir()
            argv = [str(executable), str(path), str(target)]
            record = dict(label=f"export-shard-{shard['index']:02d}", argv=argv,
                expected_failure=False, status='starting', indices=shard['indices'],
                edges=shard['edges'], input_sha256=digest(path), log=str(own / 'export.log'))
            records.append(record)
            save()
            stream = (own / 'export.log').open('x')
            logs.append(stream)
            launch = time.monotonic()
            child = subprocess.Popen(argv, stdout=stream, stderr=subprocess.STDOUT)
            # Do not use start_new_session: parent Commands owns cancellation.
            children.append((child, record, launch, target))
            record.update(pid=child.pid, status='running', started_seconds=round(launch-started, 3))
            save()
        deadline = started + timeout
        while True:
            active()
            pending = False
            for child, record, launch, _target in children:
                code = child.poll()
                if code is None:
                    pending = True
                elif record['status'] == 'running':
                    record.update(exit_code=code, seconds=round(time.monotonic()-launch, 3),
                                  status='passed' if code == 0 else 'failed')
                    save()
                    require(code == 0, 'Native export shard failed: ' + record['label'])
            if not pending:
                break
            if time.monotonic() >= deadline:
                raise subprocess.TimeoutExpired([str(executable), str(request_path)], timeout)
            time.sleep(0.05)
        active()
        directories = [item[3] for item in children]
        hashes = validate_artifacts(directories, reference)
        vectors = [json.loads((d / 'vectors.json').read_text()) for d in directories]
        combined = merge(request, plans, vectors)
        checked = []
        for shard, result in zip(plans, vectors, strict=True):
            subset = dict(schema=request['schema'], cases=[request['cases'][k] for k in shard['indices']])
            checked.append(validator(subset, result))
            active()
        report['shard_checks'] = checked
        report['full_check'] = validator(request, combined)
        active()
        # Cancellation is checked immediately before each published artifact.
        for name in ARTIFACTS:
            active()
            with (out / name).open('xb') as stream:
                stream.write((reference / name).read_bytes())
        active()
        with (out / 'vectors.json').open('x') as stream:
            stream.write(json.dumps(combined, indent=2, sort_keys=True, allow_nan=False) + '\n')
        active()
        report.update(status='passed', artifact_sha256=hashes,
            vectors_sha256=digest(out / 'vectors.json'),
            boundary='Whole independent cases; same native executable and parity artifacts; deterministic recombination. No evaluator/compiler proof.')
    except BaseException as error:
        failure = error
        for record in records:
            if record['status'] == 'starting':
                record.update(status='failed', error=type(error).__name__)
        report.update(status='cancelled' if cancelled['signal'] is not None else 'failed',
                      error=type(error).__name__, detail=str(error), cleanup='running')
        save()
    finally:
        # Terminate all together, use one shared grace, then kill/reap all.
        alive = [p for p, _r, _t, _d in children if p.poll() is None]
        for child in alive:
            try:
                child.terminate()
            except ProcessLookupError:
                pass
        stop_at = time.monotonic() + grace
        while any(p.poll() is None for p in alive) and time.monotonic() < stop_at:
            time.sleep(0.01)
        for child in alive:
            if child.poll() is None:
                try:
                    child.kill()
                except ProcessLookupError:
                    pass
        for child, record, launch, _target in children:
            code = child.wait()
            if record['status'] in ('starting', 'running'):
                record.update(status='cancelled', exit_code=code,
                              seconds=round(time.monotonic()-launch, 3))
            record['direct_child_reaped'] = True
        for stream in logs:
            stream.close()
        report.update(cleanup='all direct children reaped',
                      elapsed_seconds=round(time.monotonic()-started, 3))
        save()
        for s, handler in previous.items():
            signal.signal(s, handler)
    if failure is not None:
        raise failure
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('executable', type=Path)
    parser.add_argument('request', type=Path)
    parser.add_argument('out', type=Path)
    parser.add_argument('native_parity', type=Path)
    parser.add_argument('--checker', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--timeout', type=float, default=1800)
    args = parser.parse_args()
    checker = load_checker(args.checker)
    report = supervise(args.executable, args.request, args.out, args.native_parity,
                       jobs=args.jobs, timeout=args.timeout, validator=checker)
    print(f"Native export shards passed: {report['jobs']} shards; {report['cases']} cases; {report['edges']} edges.")


if __name__ == '__main__':
    main()
