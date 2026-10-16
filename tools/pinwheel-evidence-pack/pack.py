#!/usr/bin/env python3
"""Host-only receipt-bound evidence index/CAS. No CAD, restore, or image export."""
from __future__ import annotations
import argparse
from collections import deque
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys

HEX = re.compile(r'^[0-9a-f]{64}$')
SETTLED = {'passed', 'failed', 'timed_out', 'interrupted', 'deadline_exceeded', 'invalidated'}
JSON_LIMIT = 32 * 1024 * 1024
OPAQUE_LARGE_JSON = {'inventory.json', 'native-inventory.json', 'source-inventory.json'}
MAP_KEYS = ('input_sha256', 'artifact_sha256', 'source_sha256', 'protected_sources_sha256',
    'reference_files_sha256', 'staged_sha256', 'files_sha256', 'all_overlay_regular_files_sha256')


def require(condition, message):
    if not condition: raise ValueError(message)


def encode(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False) + '\n').encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def absolute(path, base=None):
    value = Path(path)
    return Path(os.path.abspath(value if value.is_absolute() else Path(base or Path.cwd()) / value))


def parse(raw):
    # A duplicated key could silently discard a conflicting input identity.
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=pairs)


def receipt_gate(document, path):
    require(document.get('schema') == 'pinwheel-owned-campaign-job-v1', 'Unsupported receipt: ' + path)
    require(document.get('status') in SETTLED and type(document.get('exit_code')) is int
        and type(document.get('finished_epoch')) in (int, float)
        and isinstance(document.get('input_sha256'), dict) and bool(document['input_sha256'])
        and isinstance(document.get('artifact_sha256'), dict) and bool(document['artifact_sha256'])
        and document.get('inputs_unchanged') is True
        and document.get('container_termination', {}).get('status') in ('absent', 'not_launched')
        and type(document.get('within_absolute_and_job_deadlines')) is bool
        and type(document.get('controller_must_stop')) is bool,
        'Incomplete/nonsettled or custody-invalid receipt: ' + path)
    if document['status'] == 'passed':
        require(document['exit_code'] == 0 and document['within_absolute_and_job_deadlines'] is True
            and document['controller_must_stop'] is False, 'Inconsistent passed receipt: ' + path)
    # Failure evidence remains failure evidence; a completed diagnostic failure
    # is not promoted or omitted just because a downstream repair cites it.


class Graph:
    """Expand only declared map contracts, never guess dependencies from prose."""
    def __init__(self, selection, selection_raw, selection_path, loader):
        require(selection['schema'] == 'pinwheel-evidence-selection-v1', 'Unsupported selection')
        require(selection['receipts'] and selection['anchors'], 'Select receipts and independent review anchors')
        runtime = selection['external_runtime']
        require(runtime['packed'] is False and runtime['remote_availability_proven'] is False
            and re.fullmatch(r'sha256:[0-9a-f]{64}', runtime['image_id']), 'Runtime must remain explicitly external/unpacked')
        self.selection, self.base, self.loader = selection, absolute(selection['origin_root']), loader
        self.files, self.links, self.receipts, self.documents = {}, {}, {}, set()
        self.pending = deque()
        self.add(selection_path, digest(selection_raw), 'selection')
        for role in ('receipts', 'anchors'):
            for record in selection[role]:
                require(Path(record['path']).is_absolute(), 'Root selections require exact absolute paths')
                self.add(record['path'], record['sha256'], role)
        self.root_receipts = {str(absolute(record['path'])) for record in selection['receipts']}
        self.expand()
        require(self.root_receipts <= set(self.receipts), 'Selected root is not a completed native producer receipt')
        candidate = selection.get('candidate')
        if candidate:
            require(self.files.get(str(absolute(candidate['checkpoint'])), {}).get('sha256')
                == candidate['checkpoint_sha256'], 'Selected candidate not in exact receipt closure')

    def add(self, path, sha, role, base=None):
        require(isinstance(sha, str) and HEX.fullmatch(sha), 'Malformed expected SHA256: ' + str(path))
        path = str(absolute(path, base or self.base))
        if path in self.files:
            require(self.files[path]['sha256'] == sha, 'Input hash conflict: ' + path)
            self.files[path]['roles'].add(role)
        else:
            self.files[path] = {'sha256': sha, 'roles': {role}}
            if Path(path).suffix.lower() == '.json': self.pending.append(path)

    def map(self, document, key, base, parent):
        if key not in document: return
        values = document[key]
        require(isinstance(values, dict), 'Unsupported declared hash map: ' + parent + ':' + key)
        for name, sha in values.items(): self.add(name, sha, parent + ':' + key, base)

    def expand(self):
        while self.pending:
            name = self.pending.popleft()
            if name in self.documents: continue
            self.documents.add(name)
            # Large inventories/native data are opaque evidence blobs, not
            # dependency manifests. Owned receipts and explicit manifests must
            # fit the finite metadata contract.
            raw = self.loader(name, self.files[name]['sha256'], JSON_LIMIT)
            if raw is None:
                require(Path(name).name in OPAQUE_LARGE_JSON,
                    'Unknown/dependency JSON exceeds finite metadata bound: ' + name)
                continue
            try: document = json.loads(raw)
            except (json.JSONDecodeError, UnicodeDecodeError):
                raise ValueError('Malformed declared JSON evidence: ' + name)
            if not isinstance(document, dict): continue
            # Native telemetry may contain duplicate nondependency keys. Keep
            # such data byte-exact and opaque. Strictly parse only documents
            # that declare dependency maps, or an actual owned receipt.
            if not (name in self.root_receipts or document.get('schema') == 'pinwheel-owned-campaign-job-v1'
                    or any(isinstance(document.get(key), dict) for key in MAP_KEYS)):
                continue
            document = parse(raw)
            parent = Path(name).parent
            if name in self.root_receipts or document.get('schema') == 'pinwheel-owned-campaign-job-v1':
                receipt_gate(document, name)
                self.receipts[name] = {key: document[key] for key in ('status', 'exit_code', 'inputs_unchanged',
                    'container_termination', 'within_absolute_and_job_deadlines', 'controller_must_stop')}
                self.map(document, 'input_sha256', self.base, name)
                self.map(document, 'artifact_sha256', parent, name)
            self.map(document, 'source_sha256', self.base, name)
            self.map(document, 'protected_sources_sha256', self.base, name)
            self.map(document, 'reference_files_sha256', self.base, name)
            self.map(document, 'staged_sha256', parent, name)
            self.map(document, 'files_sha256', parent, name)
            if 'all_overlay_regular_files_sha256' in document:
                overlay = absolute(document['overlay_PDK_root'])
                self.map(document, 'all_overlay_regular_files_sha256', overlay, name)
                targets = document['all_overlay_symlink_targets']
                require(isinstance(targets, dict), 'Missing overlay symlink identity map')
                for relative, target in targets.items():
                    link = str(absolute(relative, overlay))
                    require(isinstance(target, str), 'Malformed symlink text')
                    if link in self.links: require(self.links[link] == target, 'Symlink identity conflict: ' + link)
                    self.links[link] = target


def source_loader(path, expected, limit):
    p = Path(path)
    require(p.is_file(), 'Missing required source: ' + path)
    if p.stat().st_size > limit: return None
    raw = p.read_bytes()
    require(digest(raw) == expected, 'Metadata source hash mismatch: ' + path)
    return raw


def source_graph(selection_path, expected):
    require(HEX.fullmatch(expected), 'Pin the exact selection SHA256')
    selection_path = absolute(selection_path)
    raw = selection_path.read_bytes()
    require(digest(raw) == expected, 'Selection hash mismatch')
    return Graph(parse(raw), raw, str(selection_path), source_loader)


def source_identity(path):
    p = Path(path); info = p.lstat()
    require(p.is_file(), 'Required source is not a regular file or file symlink: ' + path)
    return {'kind': 'symlink_file' if p.is_symlink() else 'file',
        'mode': stat.S_IMODE(info.st_mode), 'symlink_target': os.readlink(p) if p.is_symlink() else None,
        'resolved_path': str(p.resolve()), 'size': p.stat().st_size}


def inspect_graph(graph):
    objects, logical, links = {}, 0, 0
    for name, record in graph.files.items():
        identity = source_identity(name); size = identity['size']; logical += size
        sha = record['sha256']
        require(sha not in objects or objects[sha] == size, 'Expected-content size conflict: ' + name)
        objects[sha] = size; links += identity['kind'] == 'symlink_file'
    return {'status': 'stat_estimate_not_a_hash_seal', 'files': len(graph.files), 'receipts': len(graph.receipts),
        'unique_expected_objects': len(objects), 'logical_bytes': logical, 'deduplicated_bytes_estimate': sum(objects.values()),
        'file_symlinks': links, 'declared_overlay_symlinks': len(graph.links), 'external_runtime_packed': False}


def transfer(path, expected, target=None):
    before = source_identity(path)
    output = target.open('xb') if target is not None else None
    sha = hashlib.sha256(); total = 0
    try:
        with Path(path).open('rb') as source:
            while chunk := source.read(1024 * 1024):
                sha.update(chunk); total += len(chunk)
                require(total <= before['size'], 'Source grew while collecting: ' + path)
                if output: output.write(chunk)
    finally:
        if output: output.close()
    require(sha.hexdigest() == expected and total == before['size'], 'Source content hash mismatch: ' + path)
    require(source_identity(path) == before, 'Source link/identity changed while collecting: ' + path)
    return before


def collect(selection_path, expected, output, *, index_only=False):
    graph = source_graph(selection_path, expected)
    output = absolute(output)
    # Graph/admission errors fail before mkdir. Any later failure leaves a new,
    # unsealed directory; it is never replaced or mistaken for a completed pack.
    output.mkdir(parents=True, exist_ok=False)
    objects_root = output / 'objects/sha256'
    if not index_only: objects_root.mkdir(parents=True)
    paths, objects = {}, {}
    for name, record in sorted(graph.files.items()):
        sha = record['sha256']; destination = objects_root / sha
        identity = transfer(name, sha, destination if not index_only and sha not in objects else None)
        objects[sha] = identity['size']
        paths[name] = {**identity, 'sha256': sha, 'roles': sorted(record['roles'])}
    links = {}
    for name, target in sorted(graph.links.items()):
        p = Path(name)
        require(p.is_symlink() and os.readlink(p) == target and p.exists(), 'Declared overlay symlink changed/missing: ' + name)
        links[name] = {'target': target, 'resolved_path': str(p.resolve()), 'target_is_directory': p.is_dir()}
    index = {'schema': 'pinwheel-receipt-evidence-index-v1', 'mode': 'index_only' if index_only else 'CAS_byte_copies',
        'selection_path': str(absolute(selection_path)), 'selection_sha256': expected,
        'selection': graph.selection, 'paths': paths, 'objects': objects, 'declared_overlay_symlinks': links,
        'producer_receipts': graph.receipts, 'external_runtime': graph.selection['external_runtime'],
        'scientific_claim_policy': 'Producer status, custody, scope, native diagnostic outcomes and physical acceptance remain separate. This seal proves byte identities only.',
        'absolute_paths_are_identity_only_no_restore_performed': True, 'physical_acceptance_claim': False}
    raw = encode(index); (output / 'index.json').write_bytes(raw)
    seal = {'schema': 'pinwheel-evidence-seal-v1', 'index_sha256': digest(raw), 'selection_sha256': expected,
        'objects_packed': not index_only, 'source_paths_verified': len(paths), 'unique_objects': len(objects),
        'unique_content_bytes': sum(objects.values()), 'external_runtime_packed': False, 'physical_acceptance_claim': False}
    (output / 'seal.json').write_bytes(encode(seal))
    return {'status': 'sealed_index_only' if index_only else 'sealed_CAS_pack', 'path': str(output),
        'seal_sha256': digest(encode(seal)), **seal}


def verify(pack, expected_seal, *, origins=False):
    require(HEX.fullmatch(expected_seal), 'Supply the externally recorded seal SHA256')
    pack = absolute(pack); raw = (pack / 'seal.json').read_bytes()
    require(digest(raw) == expected_seal, 'Seal hash mismatch')
    seal = parse(raw); raw_index = (pack / 'index.json').read_bytes()
    require(seal['schema'] == 'pinwheel-evidence-seal-v1' and digest(raw_index) == seal['index_sha256'], 'Index seal mismatch')
    index = parse(raw_index)
    require(index['schema'] == 'pinwheel-receipt-evidence-index-v1' and index['physical_acceptance_claim'] is False
        and index['mode'] in ('index_only', 'CAS_byte_copies'), 'Unsupported evidence index')
    require(seal['objects_packed'] == (index['mode'] == 'CAS_byte_copies'), 'Payload mode mismatch')
    require(seal['objects_packed'] or origins, 'Index-only seal needs --origins; payload objects were not packed')
    for sha, size in index['objects'].items():
        require(HEX.fullmatch(sha) and type(size) is int and size >= 0, 'Malformed object identity')
        if seal['objects_packed']:
            p = pack / 'objects/sha256' / sha
            require(p.is_file() and not p.is_symlink(), 'Missing/nonregular CAS object: ' + sha)
            require(transfer(str(p), sha)['size'] == size, 'CAS object size mismatch: ' + sha)
    if seal['objects_packed']:
        require({p.name for p in (pack/'objects/sha256').iterdir()} == set(index['objects']), 'Unexpected CAS payload object')
    for name, record in index['paths'].items():
        require(Path(name).is_absolute() and record['sha256'] in index['objects']
            and record['size'] == index['objects'][record['sha256']], 'Path/object identity mismatch: ' + name)
        if origins:
            require(transfer(name, record['sha256']) == {k:record[k] for k in ('kind','mode','symlink_target','resolved_path','size')},
                'Original source/link identity differs: ' + name)
    def packed_loader(name, expected, limit):
        require(name in index['paths'] and index['paths'][name]['sha256'] == expected, 'Incomplete dependency closure: ' + name)
        if origins and not seal['objects_packed']: return source_loader(name, expected, limit)
        p = pack / 'objects/sha256' / expected
        if p.stat().st_size > limit:return None
        return p.read_bytes()
    selection = index['selection']; selection_raw = packed_loader(index['selection_path'], index['selection_sha256'], JSON_LIMIT)
    require(parse(selection_raw) == selection and digest(selection_raw) == seal['selection_sha256'], 'Selected root identity mismatch')
    graph = Graph(selection, selection_raw, index['selection_path'], packed_loader)
    require(set(graph.files) == set(index['paths']) and graph.receipts == index['producer_receipts'], 'Dependency/producer ledger mismatch')
    require(all(record['sha256'] == index['paths'][name]['sha256'] for name,record in graph.files.items()),
        'Dependency blob digest mismatch')
    require(graph.links.keys() == index['declared_overlay_symlinks'].keys(), 'Symlink ledger incomplete')
    for name, target in graph.links.items():
        require(index['declared_overlay_symlinks'][name]['target'] == target, 'Symlink text identity mismatch')
        if origins:
            record = index['declared_overlay_symlinks'][name]
            path = Path(name)
            require(path.is_symlink() and path.exists() and os.readlink(path) == record['target']
                and str(path.resolve()) == record['resolved_path']
                and path.is_dir() is record['target_is_directory'],
                'Original declared overlay symlink identity differs: ' + name)
    require(seal['source_paths_verified'] == len(index['paths']) and seal['unique_objects'] == len(index['objects'])
        and seal['unique_content_bytes'] == sum(index['objects'].values()), 'Seal cardinalities inconsistent')
    return {'status': 'verified_pack_payloads' if seal['objects_packed'] else 'verified_index_against_current_origins',
        'files': len(index['paths']), 'objects': len(index['objects']), 'producer_receipts': len(graph.receipts),
        'external_runtime_packed': False, 'physical_acceptance_claim': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for command in ('plan', 'collect'):
        child = sub.add_parser(command); child.add_argument('--selection', type=Path, required=True)
        child.add_argument('--selection-sha256', required=True)
        if command == 'collect':
            child.add_argument('--out', type=Path, required=True)
            child.add_argument('--index-only', action='store_true')
    child = sub.add_parser('verify');child.add_argument('--pack',type=Path,required=True)
    child.add_argument('--seal-sha256',required=True);child.add_argument('--origins',action='store_true')
    args = parser.parse_args()
    if args.command == 'plan': result=inspect_graph(source_graph(args.selection,args.selection_sha256))
    elif args.command == 'collect': result=collect(args.selection,args.selection_sha256,args.out,index_only=args.index_only)
    else:result=verify(args.pack,args.seal_sha256,origins=args.origins)
    print(json.dumps(result,sort_keys=True))


if __name__ == '__main__':
    try:main()
    except (ValueError,KeyError,OSError) as error:
        print(json.dumps({'status':'rejected','error':str(error)}),file=sys.stderr)
        raise SystemExit(1)
