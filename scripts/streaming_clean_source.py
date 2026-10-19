"""Explicit clean-v1 source identity; never a substitute for fresh proof gates.

The manifest admits exact reviewed input bytes, not a branch name or a state
count. Git history may be squashed. Historical intake remains a separate mode.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CHECKER = 'scripts/streaming_clean_source.py'
MANIFEST = 'physical/validation/clean-source-v1.json'
MANIFEST_SHA256 = '15bc948101a09761c20beb1afe1f2724e552cbed71874e22711daa6c3bbb4aea'
DATA = (MANIFEST, 'physical/validation/recipe-d7a5c0d.json',
        'physical/validation/recipe-71decd66.json')
ADAPTERS = ('scripts/streaming_tt_candidate.py', 'scripts/streaming_tt_opt_intake.py',
            'scripts/check-python-snapshot.py', 'test/test_python_snapshot.py',
            'test/test_streaming_tt_candidate.py')
ORIGIN = '99f75b65fe524f266aa21654dc3d7f7054dd1aa8'
ORIGIN_TREE = 'b291858eb0924b2675e52baaf229c3d2296a5fa0'
BUNDLE = '05a2be07f33ec5a401f87876336b2e7fb31c62ad7e6cb1a6e73822ca4fa7bf8a'
CLEAN_BASE = '31a8f62a7e42a0dd91787ec947d2fb8e8ee4c25b'


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pairs(items):
    result = {}
    for name, value in items:
        require(name not in result, 'Duplicate clean-source JSON key')
        result[name] = value
    return result


def regular(root, name):
    require(type(name) is str and name and not Path(name).is_absolute() and
            '\\' not in name and all(p not in ('', '.', '..') for p in name.split('/')),
            'Invalid clean-source relative path')
    root = Path(root).resolve(); path = root / name
    require(path.is_file() and path.resolve() == path and
            not any(p.is_symlink() for p in (path, *path.parents) if p.is_relative_to(root)),
            'Missing or aliased clean-source input: ' + name)
    return path


def manifest(root):
    raw = regular(root, MANIFEST).read_bytes()
    require(sha(raw) == MANIFEST_SHA256, 'Unreviewed clean-source manifest')
    value = json.loads(raw, object_pairs_hook=pairs)
    require(value['schema'] == 'pinwheel.clean-source-admission.v1' and
            value['origin_commit'] == ORIGIN and value['origin_tree'] == ORIGIN_TREE and
            value['bundle_sha256'] == BUNDLE and value['clean_baseline_provenance'] == CLEAN_BASE and
            value['qualified'] is False and value['physical_acceptance_claim'] is False and
            set(value['approved_adapters']) == set(ADAPTERS), 'Wrong clean-source authority')
    return value, raw


def data_inputs(root=ROOT, producer_sha256=None):
    """Explicit JSON dependencies for producer hashing and read-only staging."""
    value, raw = manifest(root); result = {MANIFEST: sha(raw)}
    for row in value['recipe_baselines'].values():
        data = regular(root, row['fixture']).read_bytes()
        require(len(data) == row['bytes'] and sha(data) == row['sha256'] and
                hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == row['git_blob'],
                'Recipe baseline bytes changed')
        result[row['fixture']] = sha(data)
    require(set(result) == set(DATA), 'Recipe data dependency membership differs')
    if producer_sha256 is not None:
        require(regular(root, CHECKER) == Path(__file__).resolve(), 'Live checker is outside staged producer')
        for name, expected in {CHECKER: sha(regular(root, CHECKER).read_bytes()), **result}.items():
            require(producer_sha256.get(name) == expected, 'Unbound staged validation input: ' + name)
    require(regular(root, MANIFEST).read_bytes() == raw, 'Clean-source manifest changed during use')
    return result


def recipe_bytes(name, root=ROOT, producer_sha256=None):
    inputs = data_inputs(root, producer_sha256); value, raw = manifest(root)
    row = value['recipe_baselines'][name]; data = regular(root, row['fixture']).read_bytes()
    require(sha(data) == inputs[row['fixture']], 'Recipe baseline changed during use')
    require(regular(root, MANIFEST).read_bytes() == raw, 'Clean-source manifest changed during use')
    return data


def in_scope(name):
    return (name in ('Pinwheel.lean', 'lean-toolchain', 'lake-manifest.json') or
            name.startswith('lakefile') or name.startswith('Pinwheel/') or
            name.startswith('test/') and name.count('/') == 1 and name.endswith('.lean') or
            name.startswith('scripts/') or
            name.startswith(('physical/', 'tools/')) or name in ADAPTERS)


def live_names(root):
    result = set()
    for directory in ('Pinwheel', 'scripts', 'physical', 'tools'):
        for path in (root/directory).rglob('*'):
            require(not path.is_symlink(), 'Aliased source directory entry')
            require(path.is_file() or path.is_dir(), 'Special source directory entry')
            if path.is_file():
                result.add(path.relative_to(root).as_posix())
    result.update(p.name for p in root.iterdir() if p.is_file() and in_scope(p.name))
    result.update(p.relative_to(root).as_posix() for p in (root/'test').glob('*.lean'))
    result.update(name for name in ADAPTERS if regular(root, name).is_file())
    return result


def git(root, *args, input=None):
    boundaries = {'GIT_CEILING_DIRECTORIES', 'GIT_DISCOVERY_ACROSS_FILESYSTEM'}
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_') or k in boundaries}
    env.update(GIT_OPTIONAL_LOCKS='0', GIT_NO_REPLACE_OBJECTS='1', GIT_NO_LAZY_FETCH='1',
               GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull)
    run = subprocess.run(['git', '--no-replace-objects', *args], cwd=root, env=env,
                         input=input, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(run.returncode == 0, 'Clean-source Git query failed: ' + run.stderr.decode(errors='replace')[-1000:])
    return run.stdout


def tree(root, commit):
    require(type(commit) is str and re.fullmatch('[0-9a-f]{40}', commit), 'Exact selected commit required')
    actual = {}
    for raw in git(root, 'ls-tree', '-r', '-l', '-z', commit).split(b'\0'):
        if not raw:
            continue
        header, name = raw.split(b'\t'); mode, kind, oid, size = header.decode().split()
        actual[name.decode()] = dict(git_mode=mode, git_blob=oid, bytes=int(size))
        require(kind == 'blob', 'Unsupported selected source object')
    return actual


def hashes(root, selected):
    require(sum(r['bytes'] for r in selected.values()) <= 128 * 1024 * 1024 and
            all(r['git_mode'] in ('100644', '100755') and r['bytes'] <= 16 * 1024 * 1024
                for r in selected.values()), 'Clean source size/mode limit exceeded')
    names = sorted(selected); payload = ''.join(selected[n]['git_blob'] + '\n' for n in names).encode()
    output = git(root, 'cat-file', '--batch', input=payload); offset = 0; result = {}
    for name in names:
        row = selected[name]; end = output.index(b'\n', offset)
        require(output[offset:end].decode().split() == [row['git_blob'], 'blob', str(row['bytes'])],
                'Selected source blob header differs')
        start = end + 1; end = start + row['bytes']; data = output[start:end]
        require(len(data) == row['bytes'] and output[end:end+1] == b'\n', 'Selected source blob truncated')
        result[name] = sha(data); offset = end + 1
    require(offset == len(output), 'Unexpected selected source blob output')
    return result


def admit(root, source_commit, archived_sha256=None):
    """Recheck exact admitted projection; requires no original-history objects."""
    root = Path(root).resolve()
    require((root/'.git').exists() and not (root/'.git').is_symlink(), 'Explicit clean repository required')
    require(Path(git(root, 'rev-parse', '--show-toplevel').decode().strip()).resolve() == root,
            'Clean repository discovery escaped selected root')
    authority, raw = manifest(root); selected_tree = tree(root, source_commit)
    expected = {name: dict(row) for name, row in authority['source_inputs'].items()}
    for name, row in authority['approved_adapters'].items():
        require(expected[name]['sha256'] == row['original_sha256'], 'Adapter origin projection differs')
        expected[name]['sha256'] = row['approved_sha256']
        expected[name]['bytes'] = row['bytes']; expected[name]['git_blob'] = row['git_blob']
    expected.update(authority['admitted_additions'])
    require(CHECKER not in expected and MANIFEST not in expected, 'Checker/manifest hash cycle')
    scoped = {n: r for n, r in selected_tree.items() if in_scope(n)}
    require(set(scoped) == set(expected) | {CHECKER, MANIFEST}, 'Unreviewed/missing scoped source membership')
    require(live_names(root) == set(scoped), 'Unreviewed live scoped source membership')
    selected_hashes = hashes(root, scoped)
    for name, row in expected.items():
        require(scoped[name] == {k: row[k] for k in ('git_mode', 'git_blob', 'bytes')} and
                selected_hashes[name] == row['sha256'], 'Unreviewed selected source: ' + name)
    require(selected_hashes[MANIFEST] == MANIFEST_SHA256 and
            regular(root, CHECKER) == Path(__file__).resolve() and
            sha(Path(__file__).read_bytes()) == selected_hashes[CHECKER],
            'Live clean checker/manifest differs from selected committed source')
    for name, expected_sha in selected_hashes.items():
        require(sha(regular(root, name).read_bytes()) == expected_sha,
                'Live input differs from selected committed source: ' + name)
        if archived_sha256 is not None:
            require(archived_sha256.get(name) == expected_sha, 'Fresh raw archive differs from clean source: ' + name)
    require(regular(root, MANIFEST).read_bytes() == raw and tree(root, source_commit) == selected_tree,
            'Clean source authority changed during admission')
    require(all(sha(regular(root, name).read_bytes()) == expected for name, expected in selected_hashes.items()),
            'Clean source changed before admission closeout')
    require(live_names(root) == set(scoped), 'Live source membership changed before admission closeout')
    return dict(schema='pinwheel.clean-source-identity.v1', mode='clean-v1', qualified=False,
        physical_acceptance_claim=False, source_identity_only=True, source_commit=source_commit,
        source_tree=git(root, 'rev-parse', source_commit + '^{tree}').decode().strip(),
        origin_commit=ORIGIN, origin_tree=ORIGIN_TREE, bundle_sha256=BUNDLE,
        clean_baseline_provenance=CLEAN_BASE, manifest_sha256=MANIFEST_SHA256,
        checker_path=str(Path(__file__).resolve()), checker_sha256=selected_hashes[CHECKER], source_sha256=selected_hashes,
        input_sha256={str(root/name): value for name, value in selected_hashes.items()},
        boundary='Exact reviewed source identity only. Fresh raw/kernel/audit/tool/archive/reimport gates remain required.')
