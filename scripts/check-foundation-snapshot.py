#!/usr/bin/env python3
"""Run the complete foundation gate in a fresh archive of one local commit."""
import argparse
from contextlib import contextmanager
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


@contextmanager
def snapshot_directory(out, retain):
    if retain:
        directory = Path(out) / 'snapshot'
        directory.mkdir(exist_ok=False)
        yield directory
    else:
        with tempfile.TemporaryDirectory(prefix='pinwheel-foundation-') as directory:
            yield Path(directory)


def library_artifacts(snapshot):
    library = Path(snapshot) / '.lake/build/lib/lean'
    if not library.is_dir():
        raise RuntimeError('Fresh retained library is absent')
    result = {}
    for path in sorted(library.rglob('*')):
        if path.is_symlink():
            raise RuntimeError('Retained project library contains a symbolic alias')
        if path.is_file():
            result[str(path.relative_to(library))] = hashlib.sha256(path.read_bytes()).hexdigest()
    if not result:
        raise RuntimeError('Fresh retained library is empty')
    return result


def check_environment(environment=None):
    environment = os.environ if environment is None else environment
    fixed = {'LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE_HOME', 'LAKE_PACKAGES_DIR',
             'LAKE_CACHE_DIR', 'PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP', 'LD_PRELOAD', 'LD_LIBRARY_PATH'}
    bad = sorted(name for name, value in environment.items()
                 if value and (name in fixed or name.startswith('DYLD_')))
    if bad:
        raise RuntimeError('Refuse inherited compiler/cache/loader overrides: ' + ', '.join(bad))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--serial-build', action='store_true')
    parser.add_argument('--retain-snapshot', action='store_true',
                        help='Retain the new source archive and freshly built library for subsequent proof imports')
    parser.add_argument('--timeout-seconds', type=int, default=7200)
    parser.add_argument('--lean-memory-mib', type=int, default=4096,
                        help='Forward the serial Lean memory ceiling, 256..6144 MiB')
    args = parser.parse_args()
    if not 1 <= args.timeout_seconds <= 43200:
        parser.error('Timeout must be between 1 and 43200 seconds')
    if not 256 <= args.lean_memory_mib <= 6144:
        parser.error('Serial Lean memory must be between 256 and 6144 MiB')
    if args.serial_build:
        check_environment()
    if not re.fullmatch(r'[A-Za-z0-9_-]+', args.tag):
        parser.error('Use letters, numbers, hyphens or underscores in tags')
    out = ROOT / 'build/validation' / args.tag
    if out.exists():
        raise RuntimeError('Choose a fresh tag to preserve previous gate evidence')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    driver_path = str(Path(__file__).resolve().relative_to(ROOT))
    committed_driver = subprocess.check_output(['git', 'show', head + ':' + driver_path], cwd=ROOT)
    if committed_driver != Path(__file__).read_bytes():
        raise RuntimeError('Snapshot driver must match the selected commit')
    archive = subprocess.check_output(['git', 'archive', '--format=tar', head], cwd=ROOT)
    out.mkdir(parents=True)
    started = time.monotonic()
    receipt = dict(passed=False, source_commit=head,
                   inherited_override_guard_checked=args.serial_build,
                   snapshot_archive_sha256=hashlib.sha256(archive).hexdigest(),
                   driver_sha256=hashlib.sha256(committed_driver).hexdigest(),
                   producer_workspace='Fresh temporary git archive; no prior .lake or build cache')
    try:
        with snapshot_directory(out, args.retain_snapshot) as directory:
            snapshot = Path(directory)
            if args.retain_snapshot:
                receipt['retained_snapshot'] = str(snapshot)
            with tarfile.open(fileobj=io.BytesIO(archive)) as committed:
                committed.extractall(snapshot, filter='data')
            if (snapshot / '.lake').exists() or (snapshot / 'build').exists():
                raise RuntimeError('Committed archive unexpectedly contains a build cache')
            command = [sys.executable, '-B', 'scripts/check-foundation.py', '--tag', args.tag]
            if args.serial_build:
                command.extend(['--serial-build', '--timeout-seconds', str(args.timeout_seconds),
                                '--lean-memory-mib', str(args.lean_memory_mib)])
            print('Fresh committed foundation gate: ' + head, flush=True)
            with (out / 'snapshot-driver.log').open('w') as log:
                result = subprocess.run(command, cwd=snapshot, stdout=log, stderr=subprocess.STDOUT)
            receipt['command'] = command
            receipt['exit_code'] = result.returncode
            child_out = snapshot / 'build/validation' / args.tag
            if child_out.exists():
                shutil.copytree(child_out, out, dirs_exist_ok=True)
            if result.returncode:
                raise RuntimeError('Foundation gate failed; see snapshot-driver.log and suite logs')
            child = json.loads((out / 'report.json').read_text())
            for relative, expected in child['source_sha256'].items():
                data = subprocess.check_output(['git', 'show', head + ':' + relative], cwd=ROOT)
                if hashlib.sha256(data).hexdigest() != expected:
                    raise RuntimeError('Gate input differs from selected committed source: ' + relative)
            receipt.update(child)
            receipt['committed_input_membership_verified'] = True
            if args.retain_snapshot:
                receipt['retained_library'] = str(snapshot / '.lake/build/lib/lean')
                receipt['retained_library_artifact_sha256'] = library_artifacts(snapshot)
                receipt['retained_private_control_module'] = 'Pinwheel/CI/FoundationPrivateControl.olean' if args.serial_build else None
            receipt['passed'] = True
    except Exception as error:
        receipt['error'] = str(error)
        raise
    finally:
        receipt['snapshot_elapsed_seconds'] = round(time.monotonic() - started, 3)
        (out / 'report.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'Fresh committed foundation gate passed: {out / "report.json"}', flush=True)


if __name__ == '__main__':
    main()
