"""Recover immutable retained evidence without changing its recorded identities.

The saved current-v2 assessment is the dependency index. Its tracked result
manifest pins that index; each indexed file is checked before copying or replay.
Only locations change. Original receipts and original source bytes stay intact.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil


POLICY = 'pinwheel-paired-a-acceptance-v2-readback'
SELECTION = 'physical/experiments/design-acceptance-readback-inputs.json'
RESULT = 'physical/experiments/design-acceptance-readback-results.json'
BUNDLE_MANIFEST = 'inventory.json'
BLOCKERS = frozenset(('sram_qualification', 'timing_conditions', 'package_power'))
PROGRAMS = ('uart-tx', 'spi-mode0', 'i2c-stretched-read', 'uart-rx',
            'uart-rx-bad-stop', 'trigger-captured-high', 'trigger-captured-low', 'trigger-timeout')
DESIGN_PINS = frozenset(('Pinwheel.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
    'test/PairedChipEmit.lean', 'test/PairedValidationEmit.lean', 'test/PairedReadback.lean',
    'test/Loader.lean', 'test/paired_chip.sv', 'test/host_bridge.sv',
    'scripts/paired_execution.py', 'scripts/paired_image_certificate.py',
    'scripts/execution-vectors.py', 'scripts/pinwheel_host.py', 'scripts/pinwheel-host.py',
    'scripts/host_demo.py', 'scripts/pinwheel_sim.py'))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(block)
    return value.hexdigest()


def read_json(path):
    def pairs(items):
        value = {}
        for key, item in items:
            require(key not in value, 'Duplicate JSON field: ' + key)
            value[key] = item
        return value

    def invalid(value):
        raise ValueError('Nonfinite JSON value: ' + value)

    result = json.loads(Path(path).read_bytes(), object_pairs_hook=pairs,
                        parse_constant=invalid)
    require(isinstance(result, dict), 'Expected JSON object: ' + str(path))
    return result


def checked_path(value):
    require(isinstance(value, str) and value and '\\' not in value,
            'Invalid evidence path')
    path = Path(value)
    require('..' not in path.parts and str(path) == value, 'Noncanonical evidence path: ' + value)
    return path


def checked_inventory(values):
    require(isinstance(values, dict) and values, 'Missing retained inventory')
    for name, value in values.items():
        checked_path(name)
        require(isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value),
                'Invalid SHA-256: ' + name)
    return dict(values)


def original_assessment_root(report, index):
    """Recover the original root from eight commands in the hash-bound index.

    The saved checker generated each certificate inside its assessment output
    directory. Their absolute paths must all have the same root and the exact
    indexed output suffix. No caller-provided source prefix becomes authority.
    """
    commands = report.get('commands')
    require(isinstance(commands, list) and len(commands) == len(PROGRAMS),
            'Missing original assessment command roots')
    roots = set()
    folder = checked_path(index['path']).parent
    require(not folder.is_absolute(), 'Assessment index must have a relative path')
    for name, command in zip(PROGRAMS, commands):
        label = name + '-certificate'
        argv = command.get('argv')
        require(command.get('label') == label and command.get('exit_code') == 0 and
                command.get('expected_failure') is False and isinstance(argv, list) and
                len(argv) == 5 and argv[:4] == ['lake', 'env', 'lean', '-DwarningAsError=true'],
                'Unsupported original assessment command: ' + label)
        absolute = checked_path(argv[-1])
        suffix = folder / (label + '.lean')
        require(absolute.is_absolute() and absolute.parts[-len(suffix.parts):] == suffix.parts,
                'Wrong original assessment output path: ' + label)
        root = absolute
        for _ in suffix.parts:
            root = root.parent
        roots.add(str(root))
    require(len(roots) == 1, 'Inconsistent original assessment roots')
    return next(iter(roots))


def load_seed(source_root, anchor_root):
    """Read the complete saved inventory, bound to the tracked current-v2 root."""
    source_root, anchor_root = Path(source_root).absolute(), Path(anchor_root).absolute()
    anchor_path = anchor_root / RESULT
    anchor = read_json(anchor_path)
    require(anchor.get('schema') == 1 and anchor.get('policy') == POLICY and
            anchor.get('status') == 'assessed', 'Require the tracked current-v2 assessment')
    entry = anchor['report']
    report_path = source_root / checked_path(entry['path'])
    require(digest(report_path) == entry['sha256'], 'Changed retained assessment index')
    report = read_json(report_path)
    require(report.get('status') == 'assessed' and report.get('policy') == POLICY and
            report.get('A_accepted') is False and set(report.get('blockers', [])) == BLOCKERS,
            'Wrong retained assessment scope or verdict')
    require(report.get('selection') == anchor['selection'] and
            report['selection']['path'] == SELECTION, 'Require the explicit current-v2 selection')
    require(digest(anchor_root / SELECTION) == report['selection']['sha256'],
            'Current selection differs from retained v2')
    values = checked_inventory(report['verified_files'])
    require(report.get('verified_file_count') == len(values), 'Incomplete retained inventory')
    # The original assessment consumed only selected host sources. Recover the
    # complete freeze from that already hash-bound receipt so current emitter
    # identity and the snapshot's host entry points are checked as well.
    if 'host_observations' in report:
        host_entry = report['host_observations']['report']
        require(values.get(host_entry['path']) == host_entry['sha256'], 'Host receipt is not indexed')
        host_path = source_root / checked_path(host_entry['path'])
        require(digest(host_path) == host_entry['sha256'], 'Changed retained host receipt')
        for name, sha in checked_inventory(read_json(host_path)['source_sha256']).items():
            require(name not in values or values[name] == sha, 'Conflicting host source identity: ' + name)
            values[name] = sha
    for name, sha in ((RESULT, digest(anchor_path)), (entry['path'], entry['sha256']),
                      (SELECTION, report['selection']['sha256'])):
        require(name not in values or values[name] == sha, 'Conflicting seed identity: ' + name)
        values[name] = sha
    return dict(files=values, index=entry, selection=report['selection'],
                anchor=dict(path=RESULT, sha256=digest(anchor_path)),
                retained_verified_file_count=report['verified_file_count'])


def relocations(values):
    result = []
    for value in values:
        old, separator, new = value.partition('=')
        require(separator and old and new, 'Relocation must be OLD_ABSOLUTE=NEW_ABSOLUTE')
        old, new = checked_path(old), checked_path(new)
        require(old.is_absolute() and new.is_absolute(), 'Relocation prefixes must be absolute')
        require(old not in [a for a, b in result], 'Duplicate relocation prefix')
        result.append((old, new))
    return sorted(result, key=lambda pair: len(pair[0].parts), reverse=True)


def source_path(name, source_root, moves=()):
    path = Path(source_root).absolute() / checked_path(name)
    for old, new in moves:
        if path.is_relative_to(old):
            return new / path.relative_to(old)
    return path


def preflight(seed, source_root, moves=()):
    """Inspect every dependency; report all failures before creating an output."""
    files, issues = {}, []
    for name, sha in seed['files'].items():
        path = source_path(name, source_root, moves)
        try:
            actual = digest(path)
            if actual != sha:
                issues.append(dict(path=name, location=str(path), reason='changed',
                                   expected_sha256=sha, actual_sha256=actual))
            else:
                files[name] = dict(path=name, source=str(path), sha256=sha,
                                   bytes=path.stat().st_size)
        except OSError:
            issues.append(dict(path=name, location=str(path), reason='missing_or_unreadable',
                               expected_sha256=sha))
    return dict(status='ready' if not issues else 'invalid_evidence', policy=POLICY,
                file_count=len(seed['files']), verified_file_count=len(files),
                total_bytes=sum(item['bytes'] for item in files.values()),
                issues=issues, files=files, physical_evidence='retained, not rerun')


def bundle_path(name, sha):
    path = checked_path(name)
    if path.is_absolute():
        # A digest of the logical path avoids basename collisions and preserves
        # two independent logical references even when their bytes are equal.
        key = hashlib.sha256(name.encode()).hexdigest()
        return Path('external') / key / path.name
    return Path('root') / path


def create_bundle(destination, seed, prepared):
    require(prepared['status'] == 'ready' and not prepared['issues'] and
            set(prepared['files']) == set(seed['files']), 'Complete preflight required before bundling')
    destination = Path(destination).absolute()
    destination.mkdir(parents=True, exist_ok=False)
    entries = {}
    for name, sha in seed['files'].items():
        source = Path(prepared['files'][name]['source'])
        relative = bundle_path(name, sha)
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        with source.open('rb') as reader, target.open('xb') as writer:
            shutil.copyfileobj(reader, writer)
        require(digest(target) == sha and digest(source) == sha,
                'Evidence changed while copying: ' + name)
        target.chmod(0o555 if os.access(source, os.X_OK) else 0o444)
        entries[name] = dict(path=str(relative), sha256=sha, bytes=target.stat().st_size,
                             recovered_from=str(source))
    manifest = dict(schema=1, policy=POLICY, seed=seed, files=entries,
                    original_root=original_assessment_root(
                        read_json(destination / 'root' / seed['index']['path']), seed['index']),
                    physical_evidence='retained, hash-bound reuse; no physical rerun',
                    boundary='Location recovery preserves every original receipt and source identity.')
    path = destination / BUNDLE_MANIFEST
    with path.open('x') as stream:
        stream.write(json.dumps(manifest, indent=2) + '\n')
    path.chmod(0o444)
    return manifest


def load_bundle(bundle, anchor_root):
    bundle = Path(bundle).absolute()
    manifest = read_json(bundle / BUNDLE_MANIFEST)
    require(manifest.get('schema') == 1 and manifest.get('policy') == POLICY,
            'Require a current-v2 retained bundle')
    seed = load_seed(bundle / 'root', anchor_root)
    require(manifest.get('seed') == seed and set(manifest.get('files', {})) == set(seed['files']),
            'Bundle inventory differs from pinned retained assessment')
    issues = []
    for name, sha in seed['files'].items():
        item = manifest['files'][name]
        require(item.get('path') == str(bundle_path(name, sha)) and item.get('sha256') == sha,
                'Changed bundle location or identity: ' + name)
        path = bundle / item['path']
        # Copying the bundle is supported; links back to retired worktrees are not.
        require(not path.is_symlink() and path.resolve().is_relative_to(bundle.resolve()),
                'Bundle dependency escapes its directory: ' + name)
        try:
            actual = digest(path)
            if actual != sha or path.stat().st_size != item['bytes']:
                issues.append(dict(path=name, reason='changed'))
        except OSError:
            issues.append(dict(path=name, reason='missing_or_unreadable'))
    require(not issues, 'Invalid bundle dependencies: ' + json.dumps(issues))
    original_root = original_assessment_root(
        read_json(bundle / 'root' / seed['index']['path']), seed['index'])
    require(manifest.get('original_root', original_root) == original_root,
            'Bundle original root disagrees with pinned assessment commands')
    # Earlier bundles already hold all necessary immutable bytes. Derive this
    # alias in memory for them, without modifying their inventory or receipts.
    return dict(manifest, original_root=original_root)


def compare_current_design(bundle, manifest, current_root):
    """Snapshot scripts may differ; the actual Lean design and build pins may not."""
    current_root, bundle = Path(current_root), Path(bundle)
    require(DESIGN_PINS <= set(manifest['files']), 'Retained inventory lacks design/format pins')
    expected = {name: item['sha256'] for name, item in manifest['files'].items()
                if (name.startswith('Pinwheel/') and name.endswith('.lean')) or name in DESIGN_PINS}
    current_names = {str(path.relative_to(current_root)) for path in (current_root / 'Pinwheel').rglob('*.lean')}
    expected_names = {name for name in expected if name.startswith('Pinwheel/')}
    require(current_names == expected_names, 'Current Lean design has a different module inventory')
    issues = []
    for name, sha in expected.items():
        try:
            if digest(current_root / name) != sha:
                issues.append(name)
        except OSError:
            issues.append(name)
    require(not issues, 'Current Lean design differs from retained candidate: ' + ', '.join(issues))
    return dict(status='identical', files=len(expected), source_sha256=expected)


def relocated_evidence_class(original, bundle, manifest, fresh_output=None):
    """Extend only path lookup; original comparisons, verdicts and hashes stay intact."""
    bundle = Path(bundle).absolute()
    logical_by_location = {str(bundle / item['path']): name for name, item in manifest['files'].items()}
    original_root = Path(manifest['original_root'])

    class RelocatedEvidence(original):
        def name(self, path):
            path = Path(path)
            if not path.is_absolute():
                return str(path)
            if str(path) in logical_by_location:
                return logical_by_location[str(path)]
            if path.is_relative_to(original_root):
                return str(path.relative_to(original_root))
            return str(path.relative_to(self.root)) if path.is_relative_to(self.root) else str(path)

        def path(self, path):
            name = self.name(path)
            item = manifest['files'].get(name)
            if item:
                return bundle / item['path']
            require(fresh_output is not None and Path(name).is_relative_to(Path(fresh_output)),
                    'Unindexed retained dependency: ' + name)
            target = (self.root / path).absolute()
            require('..' not in Path(name).parts and target.resolve().is_relative_to(self.root.resolve()),
                    'Fresh assessment output escapes snapshot: ' + name)
            return target

    return RelocatedEvidence
