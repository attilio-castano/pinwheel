#!/usr/bin/env python3
"""Run complete Python regression discovery in a retained committed-source archive.

Producer membership and selected test-source membership are separate. An older
source commit may be tested by this committed producer without changing or
cleaning the caller's working tree. No shared build/tools or cache is copied.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import time
import types

ROOT = Path(__file__).resolve().parents[1]
PRODUCER = ('scripts/check-python-snapshot.py', 'scripts/validation_run.py',
            'scripts/process_group.py', 'test/test_python_snapshot.py')
SCHEMA = 'pinwheel.python-snapshot.v1'
BOOTSTRAP = []


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(block)
    return value.hexdigest()


def git(*args):
    command = ['git', *args]
    started = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=30)
    BOOTSTRAP.append((dict(argv=command, exit_code=result.returncode, timeout_seconds=30,
        seconds=round(time.monotonic() - started, 3)), result.stdout + result.stderr))
    result.check_returncode()
    return result.stdout


def parse_tree(text):
    tree = {}
    for entry in text.split('\0'):
        if not entry:
            continue
        metadata, path = entry.split('\t', 1)
        mode, kind, oid = metadata.split()
        if (path in tree or Path(path).is_absolute() or '..' in Path(path).parts or
                '\n' in path or '\r' in path or kind != 'blob' or mode not in ('100644', '100755')):
            raise RuntimeError('Expected an unambiguous regular committed file: ' + path)
        tree[path] = oid
    if not tree:
        raise RuntimeError('Selected source tree is empty')
    return tree


def membership(root, tree, algorithm):
    """Check the actual bytes against each selected Git blob, including fixtures."""
    root = Path(root)
    hashes = {}
    for relative, oid in sorted(tree.items()):
        path = root / relative
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
            raise RuntimeError('Missing or redirected committed input: ' + relative)
        data = path.read_bytes()
        actual = hashlib.new(algorithm, f'blob {len(data)}\0'.encode() + data).hexdigest()
        if actual != oid:
            raise RuntimeError('Input differs from selected committed source: ' + relative)
        hashes[relative] = hashlib.sha256(data).hexdigest()
    return hashes


def fresh_snapshot(root):
    root = Path(root)
    if any((root / name).exists() for name in ('.git', '.lake', 'build')) or any(
            path.suffix in ('.pyc', '.olean') for path in root.rglob('*')):
        raise RuntimeError('Archive contains prior repository/build/cache state')


def python_identity(executable):
    executable = Path(executable)
    if not executable.is_absolute() or not executable.is_file():
        raise RuntimeError('Expected an absolute Python executable')
    return dict(path=str(executable), resolved=str(executable.resolve()), sha256=digest(executable))


def check_environment(environment=None):
    environment = os.environ if environment is None else environment
    bad = sorted(name for name in ('PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP', 'PYTHONPYCACHEPREFIX')
                 if environment.get(name))
    if bad:
        raise RuntimeError('Refuse Python import/cache overrides: ' + ', '.join(bad))


def test_summary(output):
    match = re.search(r'^Ran (\d+) tests? in [0-9.]+s\n\nOK(?: \(([^\n]*)\))?\s*\Z', output, re.M)
    if not match or int(match[1]) == 0:
        raise RuntimeError('Missing nonempty successful unittest discovery summary')
    details = match[2] or ''
    skipped = re.search(r'(?:^|, )skipped=(\d+)(?:,|$)', details)
    skips = [dict(test=name, reason=reason) for name, reason in
             re.findall(r'^(.*?) \.\.\. skipped (.+)$', output, re.M)]
    count = int(skipped[1]) if skipped else 0
    if len(skips) != count:
        raise RuntimeError('Verbose skipped-test inventory does not match unittest summary')
    return dict(tests_run=int(match[1]), skipped=count, skips=skips, summary=match[0].strip())


def load_helpers(root):
    for name in ('process_group', 'validation_run'):
        path = Path(root) / 'scripts' / (name + '.py')
        module = types.ModuleType(name)
        module.__file__ = str(path)
        sys.modules[name] = module
        exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return sys.modules['validation_run']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tag', required=True)
    parser.add_argument('--source-commit', default='HEAD')
    parser.add_argument('--timeout-seconds', type=int, default=1800)
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_-]+', args.tag):
        parser.error('Use letters, numbers, hyphens or underscores in tags')
    if not 1 <= args.timeout_seconds <= 43200:
        parser.error('Timeout must be between 1 and 43200 seconds')
    check_environment()
    BOOTSTRAP.clear()
    producer_commit = git('rev-parse', 'HEAD').strip()
    source_commit = git('rev-parse', '--verify', args.source_commit + '^{commit}').strip()
    algorithm = git('rev-parse', '--show-object-format').strip()
    producer_tree = parse_tree(git('ls-tree', '-r', '-z', producer_commit))
    if any(path not in producer_tree for path in PRODUCER):
        raise RuntimeError('Commit the producer and its refusal tests before a qualified run')
    producer_tree = {path: producer_tree[path] for path in PRODUCER}
    producer_hashes = membership(ROOT, producer_tree, algorithm)
    helper = load_helpers(ROOT)
    out = helper.fresh_directory(ROOT / 'build/validation', args.tag)
    logs = out / 'logs'
    logs.mkdir()
    run = helper.Commands(ROOT, logs, default_timeout=60)
    for index, (record, output) in enumerate(BOOTSTRAP):
        label = f'bootstrap-git-{index + 1}'
        (logs / (label + '.log')).write_text(output)
        run.records.append(dict(record, label=label, expected_failure=False))
    report = dict(schema=SCHEMA, passed=False, source_commit=source_commit,
        producer_commit=producer_commit, producer_sha256=producer_hashes,
        producer_git_objects=producer_tree, producer_membership_verified_before=True,
        started_utc=datetime.now(timezone.utc).isoformat(), commands=run.records,
        membership_scope='Every regular file in the retained selected Git archive; working-tree '
            'test/source/fixture membership is not asserted. Preexisting working changes are not used.',
        boundary='Complete Python unittest discovery. Fixture/tool-dependent skips are reported '
            'explicitly; unavailable CAD, macro, Lean export and RTL fixtures receive no qualification. '
            'No shared workspace build/tools/cache is copied. Python standard library, installed '
            'site initialization and host OS remain runtime trust assumptions.')
    started = time.monotonic()
    tree, hashes, executable, identity = None, None, None, None
    snapshot = out / 'snapshot'
    failure = None
    try:
        tree = parse_tree(run(['git', 'ls-tree', '-r', '-z', source_commit], 'selected-tree'))
        archive = out / 'selected-source.tar'
        run(['git', 'archive', '--format=tar', '--output', archive, source_commit], 'selected-archive')
        report['snapshot_archive_sha256'] = digest(archive)
        snapshot.mkdir()
        with tarfile.open(archive) as bundle:
            bundle.extractall(snapshot, filter='data')
        fresh_snapshot(snapshot)
        hashes = membership(snapshot, tree, algorithm)
        report.update(source_sha256=hashes, selected_git_objects=tree,
                      committed_archive_membership_verified_before=True)
        executable = Path(sys.executable).resolve()
        identity = python_identity(executable)
        report['python_before'] = identity
        report['python_version'] = run([executable, '--version'], 'python-version').strip()
        selected = run([executable, '-B', '-c', 'import sys; print(sys.executable)'], 'selected-python').strip()
        if Path(selected).resolve() != executable:
            raise RuntimeError('Python subprocess does not use the fingerprinted executable')
        command = [executable, '-B', '-m', 'unittest', 'discover', '-v', '-s', 'test', '-p', 'test_*.py']
        tests = helper.Commands(snapshot, logs, records=run.records, default_timeout=args.timeout_seconds)
        output = tests(command, 'python-unittest-discover', timeout=args.timeout_seconds)
        report['unittest'] = test_summary(output)
        report['passed'] = True
    except BaseException as error:
        failure = error
        report['error'] = type(error).__name__ + ': ' + str(error)
    finally:
        try:
            if membership(ROOT, producer_tree, algorithm) != producer_hashes:
                raise RuntimeError('Committed producer changed during validation')
            report['producer_membership_verified_after'] = True
            if report.get('snapshot_archive_sha256') is not None and digest(out / 'selected-source.tar') != report['snapshot_archive_sha256']:
                raise RuntimeError('Retained source archive changed during validation')
            if hashes is not None:
                if membership(snapshot, tree, algorithm) != hashes:
                    raise RuntimeError('Archived input changed during validation')
                report['committed_archive_membership_verified_after'] = True
            if identity is not None:
                report['python_after'] = python_identity(executable)
                if report['python_after'] != identity:
                    raise RuntimeError('Selected Python changed during validation')
                report['python_identity_unchanged'] = True
        except Exception as error:
            report.update(passed=False, closeout_error=str(error))
        report['elapsed_seconds'] = round(time.monotonic() - started, 3)
        try:
            files = [p for p in sorted(out.rglob('*')) if p.is_file() and p != out / 'report.json']
            if any(p.is_symlink() or not p.resolve().is_relative_to(out.resolve()) for p in files):
                raise RuntimeError('Retained artifact redirects outside the receipt')
            report['artifact_sha256'] = {str(p.relative_to(out)): digest(p) for p in files}
        except Exception as error:
            report.update(passed=False, inventory_error=str(error))
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    if failure is not None:
        raise failure
    if not report['passed']:
        raise RuntimeError('Python snapshot closeout rejected the run')
    print('Python snapshot receipt: ' + str(out / 'report.json'), flush=True)


if __name__ == '__main__':
    main()
