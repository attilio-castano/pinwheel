#!/usr/bin/env python3
"""Verify a local Git evidence bundle or restore indexed bytes without fetching.

The catalog is custody data, not evidence of CAD execution or qualification.
An overridden catalog reads payload-index.jsonl from its own directory.
Restore never overwrites a file. A late failure may leave earlier verified files
in the destination; retry into a fresh destination rather than merging output.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile

INDEX = 'docs/research/local-evidence/payload-index.jsonl'
HEX40 = re.compile(r'[0-9a-f]{40}\Z')
HEX64 = re.compile(r'[0-9a-f]{64}\Z')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def relative(value):
    require(isinstance(value, str) and value and '\\' not in value,
            'Invalid relative path')
    require(not value.startswith('/') and all(x not in ('', '.', '..') for x in value.split('/'))
            and all(ord(c) >= 32 and ord(c) != 127 for c in value), 'Unsafe relative path')
    require(str(PurePosixPath(value)) == value, 'Noncanonical relative path')
    return value


def absolute(value):
    path = Path(value)
    require(path.is_absolute() and str(path) == str(value), 'Absolute canonical path required')
    require('..' not in path.parts and '.' not in path.parts, 'Unsafe absolute path')
    for part in (path, *path.parents):
        require(not part.is_symlink(), 'Symlink path refused: ' + str(part))
    require(path.resolve() == path, 'Aliased path refused')
    return path


def regular(path):
    path = absolute(str(path))
    require(path.is_file(), 'Regular file required: ' + str(path))
    return path.read_bytes()


def pairs(items):
    result = {}
    for key, value in items:
        require(key not in result, 'Duplicate JSON key')
        result[key] = value
    return result


def decode(data):
    return json.loads(data, object_pairs_hook=pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError('Nonfinite JSON')))


def keys(value, expected):
    require(type(value) is dict and set(value) == set(expected), 'Unexpected metadata fields')


def byte_count(value):
    return type(value) is int and value >= 0


def load(catalog):
    path = absolute(str(catalog)); raw = regular(path); c = decode(raw)
    keys(c, ('schema', 'source_commit', 'source_tree', 'bundle', 'index', 'excluded_roots'))
    require(type(c['schema']) is int and c['schema'] == 1, 'Catalog schema must be integer 1')
    require(all(isinstance(c[k], str) and HEX40.fullmatch(c[k]) for k in ('source_commit', 'source_tree')),
            'Invalid source object ID')
    b, i = c['bundle'], c['index']
    keys(b, ('sha256', 'bytes', 'ref', 'path_hint')); keys(i, ('path', 'sha256', 'bytes', 'files'))
    require(isinstance(b['path_hint'], str), 'Invalid bundle hint')
    require(isinstance(b['ref'], str) and b['ref'].startswith('refs/heads/')
            and re.fullmatch(r'refs/heads/[A-Za-z0-9_./-]+', b['ref'])
            and '..' not in b['ref'] and not b['ref'].endswith(('/', '.')), 'Invalid bundle ref')
    for item in (b, i):
        require(isinstance(item['sha256'], str) and HEX64.fullmatch(item['sha256'])
                and byte_count(item['bytes']), 'Invalid digest or byte count')
    require(i['path'] == INDEX and byte_count(i['files']), 'Invalid index metadata')
    roots = c['excluded_roots']
    require(type(roots) is list and len(roots) == 3 and len(set(roots)) == 3, 'Three unique roots required')
    for root in roots:
        relative(root)
    require(not any(a != b and a.startswith(b + '/') for a in roots for b in roots), 'Overlapping roots')
    ip = path.parent / 'payload-index.jsonl'; iraw = regular(ip)
    require(len(iraw) == i['bytes'] and digest(iraw) == i['sha256'], 'Index bytes/digest mismatch')
    rows = [decode(line) for line in iraw.splitlines()]
    require(len(rows) == i['files'], 'Index file count mismatch')
    names = []
    for row in rows:
        keys(row, ('path', 'git_mode', 'git_blob', 'bytes', 'sha256'))
        name = relative(row['path']); names.append(name)
        require(any(name.startswith(root + '/') for root in roots), 'Path outside excluded roots')
        require(row['git_mode'] in ('100644', '100755') and isinstance(row['git_blob'], str)
                and HEX40.fullmatch(row['git_blob']) and isinstance(row['sha256'], str)
                and HEX64.fullmatch(row['sha256']) and byte_count(row['bytes']), 'Invalid index row')
    require(names == sorted(set(names)), 'Unsorted or duplicate index paths')
    require(all(any(n.startswith(r + '/') for n in names) for r in roots), 'Empty excluded root')
    return c, rows, {path: raw, ip: iraw}


def continuity(inputs):
    for path, raw in inputs.items():
        require(regular(path) == raw, 'Metadata changed: ' + str(path))


def git_env():
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    env.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
               GIT_OPTIONAL_LOCKS='0', GIT_NO_REPLACE_OBJECTS='1',
               GIT_NO_LAZY_FETCH='1', GIT_TERMINAL_PROMPT='0')
    return env


def command(repo, *args):
    prefix = ['git', '--no-replace-objects', '-c', 'core.hooksPath=' + os.devnull,
              '-c', 'protocol.allow=never', '-c', 'protocol.file.allow=always']
    return prefix + (['--git-dir=' + str(repo)] if repo is not None else []) + list(args)


def git(repo, *args):
    run = subprocess.run(command(repo, *args), env=git_env(), stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, check=False)
    require(run.returncode == 0, 'Git failed: ' + run.stderr.decode(errors='replace')[-2000:])
    return run.stdout


def tree(repo, c, rows):
    require(git(repo, 'rev-parse', '--is-bare-repository').strip() == b'true', 'Bare repository required')
    require(not (repo / 'objects/info/alternates').exists(), 'External object alternates refused')
    require(git(repo, 'rev-parse', 'refs/heads/evidence').decode().strip() == c['source_commit'],
            'Repository source commit mismatch')
    require(git(repo, 'rev-parse', c['source_commit'] + '^{tree}').decode().strip() == c['source_tree'],
            'Repository source tree mismatch')
    found = {}
    for entry in git(repo, 'ls-tree', '-r', '-z', '--full-tree', c['source_commit'], '--', *c['excluded_roots']).split(b'\0'):
        if not entry:
            continue
        header, name = entry.split(b'\t', 1); mode, kind, oid = header.decode().split()
        require(kind == 'blob' and mode in ('100644', '100755'), 'Unsupported tree object')
        found[name.decode()] = (mode, oid)
    require(found == {r['path']: (r['git_mode'], r['git_blob']) for r in rows}, 'Excluded tree/index mismatch')


def blobs(repo, rows, output=None):
    """Stream and hash raw blobs. No filters, checkout, network or payload execution."""
    process = subprocess.Popen(command(repo, 'cat-file', '--batch'), env=git_env(),
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        for row in rows:
            process.stdin.write((row['git_blob'] + '\n').encode()); process.stdin.flush()
            header = process.stdout.readline(256).decode().strip().split()
            require(header == [row['git_blob'], 'blob', str(row['bytes'])], 'Blob header mismatch')
            h = hashlib.sha256(); remaining = row['bytes']
            sink = output(row) if output else None
            try:
                while remaining:
                    data = process.stdout.read(min(1024 * 1024, remaining))
                    require(bool(data), 'Truncated blob'); remaining -= len(data); h.update(data)
                    if sink:
                        sink.write(data)
                require(process.stdout.read(1) == b'\n', 'Invalid blob delimiter')
                require(h.hexdigest() == row['sha256'], 'Blob SHA256 mismatch')
            finally:
                if sink:
                    sink.close()
        process.stdin.close()
        error = process.stderr.read(); require(process.wait() == 0, 'Blob reader failed: ' + error.decode(errors='replace'))
    finally:
        if process.poll() is None:
            process.kill(); process.wait()
        for stream in (process.stdin, process.stdout, process.stderr):
            if not stream.closed:
                stream.close()


def file_hash(path):
    absolute(str(path)); require(path.is_file(), 'Bundle must be a regular file')
    h = hashlib.sha256(); size = 0
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(data); size += len(data)
    return h.hexdigest(), size


def verify(c, rows, inputs, bundle, repository):
    bundle = absolute(bundle); repo = absolute(repository)
    require(not repo.exists() and repo.parent.is_dir(), 'Repository must be a fresh path with an existing parent')
    expected = (c['bundle']['sha256'], c['bundle']['bytes'])
    require(file_hash(bundle) == expected, 'Bundle bytes/digest mismatch')
    git(None, 'init', '--bare', '--', str(repo))
    git(repo, 'bundle', 'verify', str(bundle))
    git(repo, 'fetch', '--no-tags', '--no-write-fetch-head', '--', str(bundle),
        c['bundle']['ref'] + ':refs/heads/evidence')
    git(repo, 'fsck', '--full', '--strict'); tree(repo, c, rows); blobs(repo, rows)
    continuity(inputs); require(file_hash(bundle) == expected, 'Bundle changed during verification')
    return {'status': 'verified', 'repository': str(repo), 'source_commit': c['source_commit'],
            'source_tree': c['source_tree'], 'files': len(rows), 'bytes': sum(r['bytes'] for r in rows)}


def restore(c, rows, inputs, repository, destination, paths, all_paths):
    repo = absolute(repository); dest = absolute(destination); tree(repo, c, rows)
    require(bool(paths) != bool(all_paths), 'Choose --path or --all')
    wanted = [r['path'] for r in rows] if all_paths else paths
    require(len(wanted) == len(set(wanted)), 'Duplicate requested path')
    by_name = {r['path']: r for r in rows}
    for name in wanted:
        relative(name); require(name in by_name, 'Unknown payload path')
        target = absolute(str(dest / name)); require(not target.exists(), 'Destination already exists')
    selected = [by_name[n] for n in wanted]
    blobs(repo, selected); continuity(inputs)  # Refuse corrupt payload before producing output.
    temporary = []
    try:
        def output(row):
            target = absolute(str(dest / row['path'])); target.parent.mkdir(parents=True, exist_ok=True)
            absolute(str(target.parent)); require(not target.exists(), 'Destination already exists')
            f = tempfile.NamedTemporaryFile(prefix='.evidence-', dir=target.parent, delete=False)
            temporary.append((Path(f.name), target, row)); return f
        blobs(repo, selected, output); continuity(inputs); tree(repo, c, rows)
        for staged, target, row in temporary:
            absolute(str(target)); require(not target.exists(), 'Destination already exists')
            os.chmod(staged, 0o755 if row['git_mode'] == '100755' else 0o644)
            os.link(staged, target)  # Atomic no-overwrite publication, unlike replace().
        continuity(inputs)
    finally:
        for staged, _, _ in temporary:
            staged.unlink(missing_ok=True)
    return {'status': 'restored', 'destination': str(dest), 'source_commit': c['source_commit'],
            'files': len(selected), 'bytes': sum(r['bytes'] for r in selected)}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--catalog', default=str(Path(__file__).resolve().parents[1] / 'docs/research/local-evidence/archive.json'))
    sub = p.add_subparsers(dest='action', required=True)
    v = sub.add_parser('verify'); v.add_argument('--bundle', required=True); v.add_argument('--repository', required=True)
    r = sub.add_parser('restore'); r.add_argument('--repository', required=True); r.add_argument('--destination', required=True)
    choice = r.add_mutually_exclusive_group(required=True); choice.add_argument('--path', action='append'); choice.add_argument('--all', action='store_true')
    args = p.parse_args()
    try:
        c, rows, inputs = load(args.catalog)
        result = (verify(c, rows, inputs, args.bundle, args.repository) if args.action == 'verify'
                  else restore(c, rows, inputs, args.repository, args.destination, args.path, args.all))
        print(json.dumps(result, sort_keys=True)); return 0
    except (ValueError, OSError, UnicodeError, KeyError, TypeError) as error:
        print(json.dumps({'status': 'refused', 'error': str(error)}, sort_keys=True)); return 1


if __name__ == '__main__':
    sys.exit(main())
