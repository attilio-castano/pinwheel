#!/usr/bin/env python3
"""Check staged Git blobs, or --base/--head trees, without changing the repository.

This is a cooperative publication policy, not a sandbox against changing the
policy/checker itself. Legacy exceptions pin exact bytes; provenance commits
are descriptive so squash merges do not require old local Git objects.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

POLICY = 'tools/artifact-policy.json'
MIB = 1024 * 1024
CACHE = {'build', '.lake', '__pycache__', '.pytest_cache', '.mypy_cache', '.cache'}
COMPILED = {'.pyc', '.pyo', '.olean', '.ilean', '.o', '.a', '.so', '.dylib', '.dll', '.exe', '.class', '.vvp', '.bc'}
RAW = {'.odb', '.gds', '.def', '.spef', '.sdf', '.vcd', '.fst', '.mlir', '.rpt',
       '.log', '.jsonl', '.gz', '.zip', '.tar', '.tgz', '.xz', '.zst', '.7z'}
HEX40 = re.compile(r'[0-9a-f]{40}\Z')
HEX64 = re.compile(r'[0-9a-f]{64}\Z')


def need(value, message):
    if not value:
        raise ValueError(message)


def git(repo, *args):
    discovery = {'GIT_CEILING_DIRECTORIES', 'GIT_DISCOVERY_ACROSS_FILESYSTEM'}
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_') or k in discovery}
    env.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
               GIT_OPTIONAL_LOCKS='0', GIT_NO_REPLACE_OBJECTS='1',
               GIT_NO_LAZY_FETCH='1', GIT_TERMINAL_PROMPT='0')
    result = subprocess.run(['git', '--no-replace-objects', '-C', str(repo),
                             '-c', 'core.fsmonitor=false', '-c', 'protocol.allow=never', *args],
                            env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    need(result.returncode == 0, 'Local Git input unavailable: ' + result.stderr.decode(errors='replace')[:500])
    return result.stdout


def relative(name):
    need(type(name) is str and name and '\\' not in name and
         not name.startswith('/') and all(x not in ('', '.', '..') for x in name.split('/'))
         and all(32 <= ord(c) != 127 for c in name), 'Noncanonical Git path')
    need(str(PurePosixPath(name)) == name, 'Noncanonical Git path')
    need(len(name.encode('utf-8')) <= 1024, 'Oversized path field')
    return name


def entries(repo, revision=None):
    result = {}
    args = ('ls-files', '--stage', '-z') if revision is None else ('ls-tree', '-r', '-z', '--full-tree', revision)
    for item in git(repo, *args).split(b'\0'):
        if not item:
            continue
        header, raw_name = item.split(b'\t', 1); fields = header.decode().split()
        mode, oid = (fields[0], fields[1]) if revision is None else (fields[0], fields[2])
        if revision is None:
            need(fields[2] == '0', 'Unmerged index refused')
        name = relative(raw_name.decode('utf-8'))
        need(name not in result, 'Duplicate Git path')
        result[name] = (mode, oid)
    return result


def object_bytes(repo, oid):
    return git(repo, 'cat-file', 'blob', oid)


def object_size(repo, oid):
    return int(git(repo, 'cat-file', '-s', oid))


def decode(raw):
    def pairs(items):
        value = {}
        for k, v in items:
            need(k not in value, 'Duplicate policy/index key'); value[k] = v
        return value
    return json.loads(raw, object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('Nonfinite JSON')))


def hard_path(name):
    p = PurePosixPath(name)
    return bool(set(p.parts) & CACHE) or p.suffix.lower() in COMPILED


def raw_path(name):
    return (name.startswith('docs/research/evidence/') or
            re.match(r'docs/research/[^/]*-tooling-[^/]+/', name) is not None or
            PurePosixPath(name).suffix.lower() in RAW)


def binary_payload(raw):
    return raw.startswith((b'\x7fELF', b'MZ', b'BC\xc0\xde', b'\xde\xc0\x17\x0b',
                           b'\xfe\xed\xfa\xce', b'\xce\xfa\xed\xfe', b'\xfe\xed\xfa\xcf',
                           b'\xcf\xfa\xed\xfe', b'\xca\xfe\xba\xbe', b'\x1f\x8b',
                           b'PK\x03\x04', b'\xfd7zXZ', b'\x28\xb5\x2f\xfd', b'7z\xbc\xaf'))


def validate_policy(policy):
    need(type(policy) is dict and set(policy) == {'schema', 'baseline_commit', 'max_blob_bytes',
         'max_changed_bytes', 'max_changed_files', 'bounded_index', 'exceptions'}, 'Policy fields differ')
    need(type(policy['schema']) is int and policy['schema'] == 1, 'Policy schema differs')
    for key, ceiling in [('max_blob_bytes', MIB), ('max_changed_bytes', 25*MIB), ('max_changed_files', 1000)]:
        need(type(policy[key]) is int and 0 < policy[key] <= ceiling, 'Unbounded policy budget: ' + key)
    baseline = policy['baseline_commit']; need(type(baseline) is str and HEX40.fullmatch(baseline), 'Full baseline commit required')
    exceptions = policy['exceptions']
    need(type(exceptions) is dict, 'Exception map required')
    checked = {}
    for name, row in exceptions.items():
        relative(name)
        need(not hard_path(name) and type(row) is dict and set(row) == {'sha256', 'bytes', 'git_mode', 'reason'}, 'Invalid exception')
        need(type(row['bytes']) is int and 0 <= row['bytes'] <= 16*MIB and
             type(row['sha256']) is str and HEX64.fullmatch(row['sha256']) and
             type(row['reason']) is str and row['reason'].strip(), 'Malformed legacy exception')
        need(row['git_mode'] in ('100644', '100755'), 'Invalid exception mode')
        checked[name] = (row['git_mode'], row['sha256'], row['bytes'])
    need(sum(x[2] for x in checked.values()) <= 64*MIB, 'Legacy exception budget exceeded')
    index = policy['bounded_index']
    need(type(index) is dict and set(index) == {'path', 'max_bytes', 'max_rows'} and
         index['path'] == 'docs/research/local-evidence/payload-index.jsonl' and
         type(index['max_bytes']) is int and 0 < index['max_bytes'] <= 4*MIB and
         type(index['max_rows']) is int and 0 < index['max_rows'] <= 16000, 'Unbounded index policy')
    return checked


def validate_index(raw, spec):
    need(len(raw) <= spec['max_bytes'], 'Archive index byte budget exceeded')
    lines = raw.splitlines(); need(0 < len(lines) <= spec['max_rows'], 'Archive index row budget exceeded')
    names = []
    for line in lines:
        row = decode(line)
        need(type(row) is dict and set(row) == {'path', 'git_mode', 'git_blob', 'bytes', 'sha256'}, 'Index cannot embed reports/payload')
        names.append(relative(row['path']))
        need(row['git_mode'] in ('100644', '100755') and type(row['git_blob']) is str and
             HEX40.fullmatch(row['git_blob']) and type(row['sha256']) is str and
             HEX64.fullmatch(row['sha256']) and type(row['bytes']) is int and row['bytes'] >= 0, 'Invalid index row')
    need(names == sorted(set(names)), 'Index paths unsorted/duplicated')


def check(repo, policy, *, base=None, head='HEAD'):
    # Resolve commits locally and read only index/tree objects, never working payload files.
    head = git(repo, 'rev-parse', '--verify', head + '^{commit}').decode().strip()
    exceptions = validate_policy(policy)
    versions = set(); commits = []; merge_base = None
    common = ['--no-ext-diff', '--no-textconv', '--no-renames', '--name-only', '--diff-filter=ACMRT', '-z']
    if base is None:
        selected = entries(repo)
        names = git(repo, 'diff', '--cached', *common, head).split(b'\0')
        versions.update((relative(n.decode()), *selected[n.decode()]) for n in names if n)
    else:
        base = git(repo, 'rev-parse', '--verify', base + '^{commit}').decode().strip()
        merge_base = git(repo, 'merge-base', base, head).decode().strip()
        commits = git(repo, 'rev-list', '--reverse', '--topo-order', base + '..' + head).decode().splitlines()
        for commit in commits:
            selected = entries(repo, commit)
            names = git(repo, 'diff-tree', '--root', '-r', '-m', '--no-commit-id', *common, commit).split(b'\0')
            versions.update((relative(n.decode()), *selected[n.decode()]) for n in names if n)
        base_entries = entries(repo, base)
        versions = {v for v in versions if (v[1], v[2]) != base_entries.get(v[0])}
    names = {v[0] for v in versions}
    errors = []; changed_bytes = 0; exempted = []; bounded = []
    if len(names) > policy['max_changed_files']:
        errors.append('Changed-file budget exceeded: ' + str(len(names)))
    for name, mode, oid in sorted(versions):
        size = object_size(repo, oid)
        if mode not in ('100644', '100755') or hard_path(name):
            errors.append('Build/cache/compiled/special path refused: ' + name); continue
        exception = exceptions.get(name)
        if exception and (mode, size) == (exception[0], exception[2]):
            if hashlib.sha256(object_bytes(repo, oid)).hexdigest() == exception[1]:
                exempted.append(name); continue
        changed_bytes += size
        if name == policy['bounded_index']['path']:
            try:
                need(size <= policy['bounded_index']['max_bytes'], 'Archive index byte budget exceeded')
                validate_index(object_bytes(repo, oid), policy['bounded_index']); bounded.append(name)
            except (ValueError, TypeError, KeyError) as error:
                errors.append(str(error) + ': ' + name)
        elif raw_path(name):
            errors.append('Raw execution/archive payload requires preserved evidence storage: ' + name)
        elif size > policy['max_blob_bytes']:
            errors.append('Per-blob byte budget exceeded: ' + name + ' (' + str(size) + ')')
        elif binary_payload(object_bytes(repo, oid)):
            errors.append('Compiled/archive payload signature refused: ' + name)
    if changed_bytes > policy['max_changed_bytes']:
        errors.append('Aggregate changed-byte budget exceeded: ' + str(changed_bytes))
    if base is None:
        need(entries(repo) == selected, 'Git index changed during inspection')
    return dict(schema='pinwheel.artifact-policy-result.v1', status='refused' if errors else 'passed',
                mode='commit-range' if base is not None else 'staged-index', base=base, head=head,
                comparison_merge_base=merge_base,
                changed_files=len(names), checked_blob_versions=len(versions), commits_checked=len(commits),
                budgeted_bytes=changed_bytes, legacy_exemptions=sorted(set(exempted)),
                bounded_indexes=bounded, errors=errors, execution_or_physical_acceptance=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', default='.')
    parser.add_argument('--base', help='Compare this local commit with --head instead of the staged index')
    parser.add_argument('--head', default='HEAD')
    parser.add_argument('--bootstrap-policy', type=Path,
                        help='Explicit source-review-only policy file before the first policy commit')
    parser.add_argument('--bootstrap-policy-sha256', help='Required exact SHA256 for --bootstrap-policy')
    args = parser.parse_args()
    try:
        repo = Path(git(args.repository, 'rev-parse', '--show-toplevel').decode().strip())
        need(args.base is not None or args.head == 'HEAD', '--head requires --base')
        head = git(repo, 'rev-parse', '--verify', args.head + '^{commit}').decode().strip()
        source = entries(repo, head if args.base is not None else None)
        if args.bootstrap_policy is not None:
            need(POLICY not in source, 'Bootstrap policy only before first policy commit')
            need(args.bootstrap_policy.stat().st_size <= 256*1024, 'Policy byte budget exceeded')
            raw = args.bootstrap_policy.read_bytes(); policy_origin = 'explicit-bootstrap-file'
            need(hashlib.sha256(raw).hexdigest() == args.bootstrap_policy_sha256, 'Bootstrap policy digest differs')
        else:
            need(args.bootstrap_policy_sha256 is None, 'Bootstrap digest requires bootstrap file')
            need(POLICY in source, 'Policy must be in selected Git index/tree')
            need(source[POLICY][0] == '100644', 'Policy must be a regular Git file')
            need(object_size(repo, source[POLICY][1]) <= 256*1024, 'Policy byte budget exceeded')
            raw = object_bytes(repo, source[POLICY][1]); policy_origin = 'selected-Git-blob'
        result = check(repo, decode(raw), base=args.base, head=head)
        need(entries(repo, head if args.base is not None else None) == source, 'Selected Git inputs changed')
        result.update(policy_sha256=hashlib.sha256(raw).hexdigest(), policy_origin=policy_origin)
        print(json.dumps(result, sort_keys=True)); return int(bool(result['errors']))
    except (ValueError, KeyError, TypeError, OSError, UnicodeError) as error:
        print(json.dumps(dict(status='refused', error=str(error)))); return 1


if __name__ == '__main__':
    sys.exit(main())
