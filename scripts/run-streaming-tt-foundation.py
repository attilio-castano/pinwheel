#!/usr/bin/env python3
"""Bound one fresh foundation gate to exact installed Lean runtime observations."""
import argparse
from datetime import datetime, timezone
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[1]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def observe(binary_seal):
    seal = read(binary_seal)
    binaries = {Path(path) for path in seal['binaries']}
    prefixes = {path.parent.parent for path in binaries}
    require(len(prefixes) == 1, 'Ambiguous compiler prefix')
    prefix = prefixes.pop()
    require(all(sha(path) == seal['binaries'][str(path)] for path in binaries), 'Compiler binary changed')
    paths = set(binaries)
    for name in ('lean', 'lake'):
        selected = shutil.which(name)
        require(selected is not None, 'Missing compiler shim: ' + name)
        paths.add(Path(selected).absolute())
    for path in (prefix / 'lib/lean').rglob('*'):
        require(not (path.is_symlink() and path.is_dir()), 'Runtime directory alias')
        if path.is_file():
            paths.add(path)
    return {str(path): dict(resolved=str(path.resolve()), sha256=sha(path), bytes=path.stat().st_size)
            for path in sorted(paths)}


def archive_inputs(archive):
    # The whole Git archive remains bound independently; retain all source bytes' hashes.
    with tarfile.open(fileobj=io.BytesIO(archive)) as bundle:
        return {member.name: hashlib.sha256(bundle.extractfile(member).read()).hexdigest()
                for member in bundle.getmembers() if member.isfile()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--expected-runtime', type=Path, required=True)
    parser.add_argument('--original-runtime-before', type=Path, required=True)
    parser.add_argument('--binary-seal', type=Path, required=True)
    parser.add_argument('--timeout-seconds', type=int, default=6000)
    parser.add_argument('--lean-memory-mib', type=int, default=4096)
    args = parser.parse_args()
    require(re.fullmatch(r'[A-Za-z0-9_-]+', args.tag), 'Invalid fresh tag')
    require(1 <= args.timeout_seconds <= 6000 and 256 <= args.lean_memory_mib <= 4096,
            'Foundation exceeds this campaign controller bounds')
    out = ROOT / 'build/streaming-tt-foundation' / args.tag
    out.mkdir(parents=True, exist_ok=False)
    receipt_path = ROOT / 'build/validation' / args.tag / 'report.json'
    require(not receipt_path.parent.exists(), 'Preserve the previous foundation tag')
    selected = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    archive = subprocess.check_output(['git', 'archive', '--format=tar', selected], cwd=ROOT)
    committed = archive_inputs(archive)
    self_relative = Path(__file__).resolve().relative_to(ROOT).as_posix()
    require(committed.get(self_relative) == sha(__file__), 'Commit the exact controller before execution')
    source_inputs = {name: value for name, value in committed.items()
                     if name.endswith('.lean') or name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                        'scripts/check-foundation.py', 'scripts/check-foundation-snapshot.py',
                        'scripts/process_group.py', 'scripts/binary_v0.py', 'scripts/check-uart-rx.py',
                        'scripts/uart_rx_oracle.py', 'scripts/reactive-core-vectors.py', 'scripts/execution-vectors.py')}
    require(all((ROOT / name).is_file() and not (ROOT / name).is_symlink() and sha(ROOT / name) == value
                for name, value in source_inputs.items()), 'Working source differs from selected committed source wave')
    expected = read(args.expected_runtime)
    old = read(args.original_runtime_before)
    expected_map = expected['file_sha256_and_resolution']
    require(expected.get('passed') is True and len(expected_map) == expected['files'] == 14923,
            'Expected runtime observation is incomplete')
    require(old['observation']['files'] == expected_map and
            expected['formal_binary_seal_sha256'] == old['observation']['formal_binary_seal_sha256'] == sha(args.binary_seal),
            'Prior runtime or binary seal disagrees')
    inputs = {str(path.resolve()): sha(path) for path in
              (Path(__file__), args.expected_runtime, args.original_runtime_before, args.binary_seal)}
    runtime_before = observe(args.binary_seal)
    require(runtime_before == expected_map, 'Current full runtime membership/bytes/resolution differ')
    before_path = out / 'runtime-before.json'
    before_path.write_text(json.dumps(runtime_before, sort_keys=True, indent=2) + '\n')
    command = [sys.executable, '-B', str(ROOT / 'scripts/check-foundation-snapshot.py'), '--tag', args.tag,
               '--serial-build', '--retain-snapshot', '--timeout-seconds', str(args.timeout_seconds),
               '--lean-memory-mib', str(args.lean_memory_mib)]
    packet = dict(schema='pinwheel.streaming-tt-fresh-foundation-runtime.v1', qualified=False,
        proof_acceptance_claim=False, status='running', started_utc=datetime.now(timezone.utc).isoformat(),
        source_commit=selected, selected_archive_sha256=hashlib.sha256(archive).hexdigest(),
        committed_input_sha256=source_inputs, input_sha256=inputs, argv=command,
        runtime_before=dict(path=str(before_path), sha256=sha(before_path)), runtime_files=len(runtime_before),
        foundation_receipt=str(receipt_path), boundary='Exact installed compiler/shim/lib/lean identity plus fresh-source gate. '
        'No official archive membership, reproducible compiler build, host OS closure, RTL or physical acceptance claim.')
    report_path = out / 'report.json'
    report_path.write_text(json.dumps(packet, indent=2) + '\n')
    log = out / 'native.log'; started = time.monotonic(); timed_out = False
    with log.open('wb') as stream:
        child = subprocess.Popen(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = child.wait(timeout=args.timeout_seconds + 120)
        except subprocess.TimeoutExpired:
            timed_out = True
            try: os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError: pass
            try: child.wait(timeout=3)
            except subprocess.TimeoutExpired:
                try: os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                child.wait()
            code = 124
    try: os.killpg(child.pid, 0); closed = False
    except ProcessLookupError: closed = True
    after_path = out / 'runtime-after.json'
    runtime_after = observe(args.binary_seal)
    after_path.write_text(json.dumps(runtime_after, sort_keys=True, indent=2) + '\n')
    unchanged = all(Path(path).is_file() and sha(path) == value for path, value in inputs.items())
    same_source = all((ROOT / name).is_file() and sha(ROOT / name) == value for name, value in source_inputs.items())
    foundation = read(receipt_path) if receipt_path.exists() else {}
    foundation_ok = (foundation.get('passed') is True and foundation.get('modules') == 649 and
        foundation.get('source_commit') == selected and foundation.get('serial_build') is True and
        foundation.get('untrusted_axiom_rejected') is True and foundation.get('unused_private_axiom_rejected') is True and
        foundation.get('committed_input_membership_verified') is True and
        all(committed.get(name) == value for name, value in foundation.get('source_sha256', {}).items()) and
        bool(foundation.get('retained_library_artifact_sha256')))
    passed = code == 0 and not timed_out and closed and unchanged and same_source and runtime_before == runtime_after and foundation_ok
    packet.update(status='completed' if passed else 'failed', passed=passed, exit_code=code, timed_out=timed_out,
        native_process_group_closed=closed, inputs_unchanged=unchanged, sources_unchanged=same_source,
        foundation_complete_649=foundation_ok, runtime_unchanged=runtime_before == runtime_after,
        runtime_after=dict(path=str(after_path), sha256=sha(after_path)), native_log_sha256=sha(log),
        foundation_receipt_sha256=sha(receipt_path) if receipt_path.exists() else None,
        elapsed_seconds=time.monotonic()-started, finished_utc=datetime.now(timezone.utc).isoformat())
    report_path.write_text(json.dumps(packet, indent=2) + '\n')
    print(json.dumps(dict(status=packet['status'], runtime_files=len(runtime_before), foundation_modules=foundation.get('modules'),
                         report=str(report_path))), flush=True)
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()
