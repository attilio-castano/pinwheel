"""Complete missing checker dependencies using exact same-commit PDK blobs.

Every originally installed file and symlink is preserved. Only two official
JSON payloads are added in a fresh directory; no deck or rule value is edited.
Native execution and successful checks remain separate obligations.
"""
import argparse
import hashlib
import os
from pathlib import Path
import shutil

from streaming_tt_physical import ARCHIVE, ROOT, read, relative_path, require, sha, stage_pdk, verify_pdk

EXTRAS = frozenset((
    'ihp-sg13cmos5l/libs.tech/klayout/python/sg13cmos5l_pycell_lib/sg13cmos5l_tech_mod.json',
    'ihp-sg13g2/libs.tech/klayout/tech/drc/rule_decks/sg13g2_tech_default.json'))


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def verify_complete_pdk(directory, tool_lock, completion_lock, *, tree_path=None):
    directory = Path(directory).resolve()
    tree_path = tree_path or ARCHIVE / 'upstream/pdk-tree.json'
    base = verify_pdk(directory, tool_lock, tree_path=tree_path)
    require(completion_lock['pdk_completion_revision'] == tool_lock['pdk_revision'] and
        set(completion_lock['pdk_extra_files']) == EXTRAS, 'Changed PDK completion scope')
    tree = {entry['path']:entry for entry in read(tree_path)['tree']}
    installed = read(directory / 'installed.json')
    files = dict(installed['files_sha256'], **{'installed.json':sha(directory/'installed.json')})
    for name, identity in completion_lock['pdk_extra_files'].items():
        path = directory / relative_path(name)
        require(name not in files and name not in installed['symlinks'], 'PDK completion replaced an installed input')
        require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(directory),
            'Missing/aliased PDK completion file: ' + name)
        data = path.read_bytes()
        require(name in tree and tree[name]['mode'] in ('100644','100755') and
            tree[name]['sha'] == identity['git_blob'] == blob(data) and sha(path) == identity['sha256'],
            'PDK completion differs from pinned Git blob: ' + name)
        files[name] = identity['sha256']
    actual_files, actual_links = {}, {}
    for path in sorted(directory.rglob('*')):
        name = str(path.relative_to(directory))
        if path.is_symlink(): actual_links[name] = os.readlink(path)
        elif path.is_file(): actual_files[name] = sha(path)
        else: require(path.is_dir(), 'Unsupported PDK filesystem entry: ' + name)
    require(actual_files == files and actual_links == installed['symlinks'],
        'Completed PDK payload membership or bytes differ')
    return dict(base=base, regular_files=len(files), symlinks=len(actual_links),
        additions=completion_lock['pdk_extra_files'], complete_files_sha256=files,
        complete_symlink_targets=actual_links, rule_or_deck_edits=False, native_checker_pass=False)


def complete_pdk(source, destination, payload_root):
    source, destination, payload_root = map(lambda value:Path(value).resolve(), (source,destination,payload_root))
    tool_lock = read(ROOT / 'tools/physical-toolchain.json')
    completion_lock = read(ROOT / 'tools/streaming-tt-signoff.json')
    require(not destination.exists(), 'Refusing to overwrite a PDK completion')
    before = verify_pdk(source, tool_lock)
    # Validate extra source bytes against the independently pinned Git inventory
    # before copying. Full membership validation follows in the fresh copy.
    tree_path = ARCHIVE / 'upstream/pdk-tree.json'
    require(sha(tree_path) == tool_lock['pdk_tree_sha256'], 'Wrong PDK Git inventory')
    tree = {entry['path']:entry for entry in read(tree_path)['tree']}
    require(set(completion_lock['pdk_extra_files']) == EXTRAS and
        completion_lock['pdk_completion_revision'] == tool_lock['pdk_revision'], 'Changed PDK completion scope')
    frozen = {}
    for name, identity in completion_lock['pdk_extra_files'].items():
        path = payload_root / relative_path(name)
        require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(payload_root),
            'Missing/aliased official completion payload')
        require(blob(path.read_bytes()) == tree[name]['sha'] == identity['git_blob'] and sha(path) == identity['sha256'],
            'Official completion payload differs')
        frozen[name] = sha(path)
    stage_pdk(source, destination, tool_lock)
    for name in frozen:
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        require(not target.exists() and not target.is_symlink(), 'Completion would replace a PDK entry')
        shutil.copyfile(payload_root / name, target)
    result = verify_complete_pdk(destination,tool_lock,completion_lock)
    require(before == verify_pdk(source,tool_lock) and
        frozen == {name:sha(payload_root/name) for name in frozen}, 'PDK source changed during completion')
    return result


def main():
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('source','destination','payload-root'): parser.add_argument('--'+name,type=Path,required=True)
    args = parser.parse_args()
    print(json.dumps(complete_pdk(args.source,args.destination,args.payload_root),indent=2,sort_keys=True))


if __name__ == '__main__': main()
