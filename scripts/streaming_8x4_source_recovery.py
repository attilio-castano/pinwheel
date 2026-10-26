#!/usr/bin/env python3
"""Recover authenticated historical source, without executing it or qualifying CAD.

The production CLI pins its catalog. Verify imports the local bundle into a new
bare repository; restore writes its complete tracked tree into a new directory.
Use ignored build/streaming-8x4-source-recovery/ locations. Failures can leave a
partial owned repository/directory: preserve it for diagnosis and retry freshly.
Raw machine-specific evidence and historical absolute paths require separate
verification. No checkout, filters, hooks, network, or archived code is run.
"""
import argparse
import configparser
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import unicodedata

CATALOG = Path(__file__).resolve().parents[1] / 'docs/research/local-evidence/streaming-8x4-curation-20261026/source-catalog.json'
CATALOG_SHA256 = '222cb9800cfd30dd71eff925e9aeeab2b9505c7423cf5762a379f3cdcaaa51cf'
SCHEMA = 'pinwheel.streaming-8x4-source-catalog.v1'
SCOPE = ('Tracked source custody only. Untracked drafts, raw machine-specific build/PDK/runtime evidence, '
         'and historical absolute-path relocation are excluded. Source recovery does not establish '
         'physical acceptance, extraction-model qualification, or qualified timing.')
HEX40 = re.compile(r'[0-9a-f]{40}\Z')
HEX64 = re.compile(r'[0-9a-f]{64}\Z')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def relative(value):
    require(isinstance(value, str) and value and '\\' not in value, 'Invalid relative path')
    parts = value.split('/')
    require(not value.startswith('/') and all(p not in ('', '.', '..') and p.casefold() != '.git'
            and not p.endswith(('.', ' ')) for p in parts) and str(PurePosixPath(value)) == value
            and all(ord(c) >= 32 and ord(c) != 127 for c in value), 'Unsafe relative path')
    return value


def absolute(value):
    path = Path(value)
    require(path.is_absolute() and str(path) == str(value) and '..' not in path.parts,
            'Absolute canonical path required')
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


def decode(raw):
    return json.loads(raw, object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('Nonfinite JSON')))


def keys(value, expected):
    require(type(value) is dict and set(value) == set(expected), 'Unexpected metadata fields')


def count(value):
    return type(value) is int and value >= 0


def _load(catalog, expected_sha256):
    """Explicit digest argument supports synthetic private test fixtures only."""
    path = absolute(str(catalog)); raw = regular(path)
    require(HEX64.fullmatch(expected_sha256) and hashlib.sha256(raw).hexdigest() == expected_sha256,
            'Pinned catalog digest mismatch')
    c = decode(raw)
    keys(c, ('schema', 'source_commit', 'source_tree', 'source_files', 'source_bytes', 'bundle', 'index', 'scope'))
    require(c['schema'] == SCHEMA and c['scope'] == SCOPE, 'Unsupported source-only catalog')
    require(all(isinstance(c[k], str) and HEX40.fullmatch(c[k]) for k in ('source_commit', 'source_tree')),
            'Invalid source object ID')
    require(count(c['source_files']) and c['source_files'] > 0 and count(c['source_bytes']), 'Invalid source totals')
    b, i = c['bundle'], c['index']
    keys(b, ('sha256', 'bytes', 'ref', 'path_hint')); keys(i, ('path', 'sha256', 'bytes', 'files'))
    require(isinstance(b['path_hint'], str) and isinstance(b['ref'], str)
            and re.fullmatch(r'refs/heads/[A-Za-z0-9_./-]+', b['ref'])
            and '..' not in b['ref'] and not b['ref'].endswith(('/', '.')), 'Invalid bundle reference')
    for item in (b, i):
        require(isinstance(item['sha256'], str) and HEX64.fullmatch(item['sha256'])
                and count(item['bytes']), 'Invalid digest or byte count')
    require(i['path'] == 'sources-index.json' and count(i['files']), 'Invalid deferred index metadata')
    ip = path.parent / i['path']; iraw = regular(ip)
    require(len(iraw) == i['bytes'] and hashlib.sha256(iraw).hexdigest() == i['sha256'], 'Index bytes/digest mismatch')
    rows = decode(iraw)
    require(type(rows) is list and len(rows) == i['files'], 'Index file count mismatch')
    names = []
    for row in rows:
        keys(row, ('path', 'git_mode', 'git_blob', 'bytes', 'sha256'))
        names.append(relative(row['path']))
        require(row['git_mode'] in ('100644', '100755') and isinstance(row['git_blob'], str)
                and HEX40.fullmatch(row['git_blob']) and isinstance(row['sha256'], str)
                and HEX64.fullmatch(row['sha256']) and count(row['bytes']), 'Invalid index row')
    require(names == sorted(set(names)), 'Unsorted or duplicate deferred paths')
    return c, rows, {path: raw, ip: iraw}


def continuity(inputs):
    for path, raw in inputs.items():
        require(regular(path) == raw, 'Metadata changed: ' + str(path))


def git_env():
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    env.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull, GIT_OPTIONAL_LOCKS='0',
               GIT_NO_REPLACE_OBJECTS='1', GIT_NO_LAZY_FETCH='1', GIT_TERMINAL_PROMPT='0')
    return env


def command(repo, *args):
    prefix = ['git', '--no-replace-objects', '-c', 'core.hooksPath=' + os.devnull,
              '-c', 'core.fsmonitor=false', '-c', 'protocol.allow=never', '-c', 'protocol.file.allow=always']
    return prefix + (['--git-dir=' + str(repo)] if repo is not None else []) + list(args)


def git(repo, *args):
    run = subprocess.run(command(repo, *args), env=git_env(), stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, check=False)
    require(run.returncode == 0, 'Git failed: ' + run.stderr.decode(errors='replace')[-2000:])
    return run.stdout


def tree(repo, c, index):
    repo = absolute(str(repo)); require(repo.is_dir(), 'Bare repository required')
    for directory, dirs, files in os.walk(repo):
        require(not any((Path(directory) / n).is_symlink() for n in dirs + files), 'Repository symlink refused')
        require(not any(n.endswith('.promisor') for n in files), 'Partial object store refused')
    for name in ('objects/info/alternates', 'objects/info/http-alternates', 'shallow', 'info/grafts'):
        require(not (repo / name).exists(), 'External or incomplete object store refused')
    config = configparser.ConfigParser(interpolation=None)
    config.read_string(regular(repo / 'config').decode())
    core = config['core'] if config.sections() == ['core'] else {}
    require(not config.defaults() and {'repositoryformatversion', 'filemode', 'bare'} <= set(core)
            <= {'repositoryformatversion', 'filemode', 'bare', 'ignorecase', 'precomposeunicode'}
            and core['repositoryformatversion'] == '0' and core['bare'] == 'true'
            and all(v in ('true', 'false') for k, v in core.items() if k != 'repositoryformatversion'),
            'Modified bare repository configuration refused')
    require(git(repo, 'rev-parse', '--is-bare-repository').strip() == b'true', 'Bare repository required')
    require(git(repo, 'for-each-ref', '--format=%(objectname) %(refname)').decode().strip()
            == c['source_commit'] + ' refs/heads/source', 'Repository source reference mismatch')
    git(repo, 'fsck', '--full', '--strict')
    require(git(repo, 'rev-parse', c['source_commit'] + '^{tree}').decode().strip() == c['source_tree'],
            'Repository source tree mismatch')
    found = []
    for entry in git(repo, 'ls-tree', '-r', '-l', '-z', '--full-tree', c['source_commit']).split(b'\0'):
        if entry:
            header, name = entry.split(b'\t', 1); mode, kind, oid, size = header.decode().split()
            require(kind == 'blob' and mode in ('100644', '100755') and HEX40.fullmatch(oid), 'Unsupported source object')
            found.append(dict(path=relative(name.decode()), git_mode=mode, git_blob=oid, bytes=int(size)))
    require(len(found) == c['source_files'] and sum(r['bytes'] for r in found) == c['source_bytes'], 'Source totals mismatch')
    by_name = {r['path']: r for r in found}
    require(len(by_name) == len(found)
            == len({unicodedata.normalize('NFC', n).casefold() for n in by_name}), 'Colliding source paths')
    for row in index:
        require(by_name.get(row['path']) == {k: v for k, v in row.items() if k != 'sha256'}, 'Deferred tree/index mismatch')
        by_name[row['path']]['sha256'] = row['sha256']
    return sorted(found, key=lambda r: r['path'])


def file_identity(path):
    absolute(str(path)); require(path.is_file(), 'Regular file required')
    size = path.stat().st_size; oid = hashlib.sha1(b'blob ' + str(size).encode() + b'\0')
    sha = hashlib.sha256(); read = 0
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b''):
            oid.update(data); sha.update(data); read += len(data)
    require(read == size, 'File changed while hashing')
    return oid.hexdigest(), sha.hexdigest(), size


def blobs(repo, rows, destination=None):
    """Check every Git object ID and indexed SHA256 while streaming raw bytes."""
    process = subprocess.Popen(command(repo, 'cat-file', '--batch'), env=git_env(),
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        for row in rows:
            process.stdin.write((row['git_blob'] + '\n').encode()); process.stdin.flush()
            require(process.stdout.readline(256).decode().strip().split()
                    == [row['git_blob'], 'blob', str(row['bytes'])], 'Blob header mismatch')
            oid = hashlib.sha1(b'blob ' + str(row['bytes']).encode() + b'\0'); sha = hashlib.sha256()
            remaining = row['bytes']; sink = None
            if destination is not None:
                target = absolute(str(destination / row['path'])); target.parent.mkdir(parents=True, exist_ok=True)
                absolute(str(target.parent)); sink = target.open('xb')  # Never overwrite.
            try:
                while remaining:
                    data = process.stdout.read(min(1024 * 1024, remaining))
                    require(bool(data), 'Truncated blob'); remaining -= len(data); oid.update(data); sha.update(data)
                    if sink:
                        sink.write(data)
                require(process.stdout.read(1) == b'\n' and oid.hexdigest() == row['git_blob'], 'Blob object ID mismatch')
                require('sha256' not in row or sha.hexdigest() == row['sha256'], 'Deferred blob SHA256 mismatch')
            finally:
                if sink:
                    sink.close()
            if destination is not None:
                os.chmod(target, 0o755 if row['git_mode'] == '100755' else 0o644)
        process.stdin.close(); error = process.stderr.read()
        require(process.wait() == 0, 'Blob reader failed: ' + error.decode(errors='replace')[-2000:])
    finally:
        if process.poll() is None:
            process.kill(); process.wait()
        for stream in (process.stdin, process.stdout, process.stderr):
            if not stream.closed:
                stream.close()


def result(status, c, **location):
    return dict(status=status, source_commit=c['source_commit'], source_tree=c['source_tree'],
                files=c['source_files'], bytes=c['source_bytes'], source_only=True,
                physical_acceptance=False, model_qualified=False, qualified_timing=False,
                raw_evidence_restored=False, historical_paths_relocated=False, **location)


def verify(c, index, inputs, bundle, repository):
    bundle = absolute(bundle); repo = absolute(repository)
    require(not repo.exists() and repo.parent.is_dir(), 'Repository must be a fresh path with an existing parent')
    expected = (c['bundle']['sha256'], c['bundle']['bytes'])
    require(file_identity(bundle)[1:] == expected, 'Bundle bytes/digest mismatch')
    continuity(inputs)
    git(None, 'init', '--bare', '--template=', '--', str(repo))
    git(repo, 'bundle', 'verify', str(bundle))
    git(repo, 'fetch', '--no-tags', '--no-write-fetch-head', '--', str(bundle), c['bundle']['ref'] + ':refs/heads/source')
    rows = tree(repo, c, index); blobs(repo, rows)
    continuity(inputs); require(tree(repo, c, index) == rows, 'Source tree changed')
    require(file_identity(bundle)[1:] == expected, 'Bundle changed during verification')
    return result('source_verified', c, repository=str(repo))


def restore(c, index, inputs, repository, destination):
    repo = absolute(repository); dest = absolute(destination)
    require(not dest.exists() and dest.parent.is_dir(), 'Destination must be a fresh path with an existing parent')
    rows = tree(repo, c, index); blobs(repo, rows); continuity(inputs)
    dest.mkdir(mode=0o700); blobs(repo, rows, dest)
    require(tree(repo, c, index) == rows, 'Source tree changed'); continuity(inputs)
    found = []
    for directory, dirs, files in os.walk(dest):
        require(not any((Path(directory) / n).is_symlink() for n in dirs + files), 'Restored symlink refused')
        found.extend((Path(directory) / n).relative_to(dest).as_posix() for n in files)
    require(sorted(found) == [r['path'] for r in rows], 'Restored source membership mismatch')
    for row in rows:
        target = dest / row['path']; oid, sha, size = file_identity(target)
        require((oid, size) == (row['git_blob'], row['bytes'])
                and ('sha256' not in row or sha == row['sha256'])
                and target.stat().st_mode & 0o777 == (0o755 if row['git_mode'] == '100755' else 0o644),
                'Restored source identity/mode mismatch')
    continuity(inputs)
    return result('source_restored', c, destination=str(dest))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    v = sub.add_parser('verify'); v.add_argument('--bundle', required=True); v.add_argument('--repository', required=True)
    r = sub.add_parser('restore'); r.add_argument('--repository', required=True); r.add_argument('--destination', required=True)
    args = parser.parse_args()
    try:
        c, index, inputs = _load(CATALOG, CATALOG_SHA256)
        value = (verify(c, index, inputs, args.bundle, args.repository) if args.action == 'verify'
                 else restore(c, index, inputs, args.repository, args.destination))
        print(json.dumps(value, sort_keys=True)); return 0
    except (ValueError, OSError, UnicodeError, KeyError, TypeError, configparser.Error) as error:
        print(json.dumps({'status': 'refused', 'source_only': True, 'error': str(error)}, sort_keys=True)); return 1


if __name__ == '__main__':
    sys.exit(main())
