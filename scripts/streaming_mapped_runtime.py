"""Narrow membership audit for selected CAD runtimes in pinned native archives.

No archive is extracted.  This checks the existing tool-identity selection, not
the provenance of every installed file, Lean, Python, or operating-system code.
The historical identity's broader archive-membership flag remains false.
"""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import tarfile


SCHEMA = 'pinwheel.streaming-mapped-selected-cad-archive-membership.v1'
PINNED = {
    'circt': dict(release='firtool-1.159.0', directory='firtool-1.159.0',
        archive='circt-full-shared-macos-arm64.tar.gz',
        sha256='c52c3af2dce2edeeec73df3deca4b9f57c092875c7a8a0860125eb09c44a945e'),
    'oss-cad-suite': dict(release='2026-09-13', directory='oss-cad-suite',
        archive='oss-cad-suite-darwin-arm64-20260913.tgz',
        sha256='9d9a5401e2671d114c63b9354d2f4fdf4e9c43acfcf479dbe8f00928daffeb10'),
}
CAD_TOOLS = {'circt': ('circt', 'circt-opt'), 'yosys': ('oss-cad-suite', 'yosys'),
    'abc': ('oss-cad-suite', 'yosys-abc'), 'solver': ('oss-cad-suite', 'z3'),
    'iverilog': ('oss-cad-suite', 'iverilog'), 'vvp': ('oss-cad-suite', 'vvp')}
SHA256 = re.compile(r'[0-9a-f]{64}\Z')


def require(value, message):
    if not value:
        raise ValueError(message)


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def canonical_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def absolute(value):
    require(type(value) is str and value and '\\' not in value,
        'Runtime identity path must be an absolute canonical path')
    path = Path(value)
    require(path.is_absolute() and str(path) == value and '..' not in path.parts,
        'Runtime identity path must be an absolute canonical path')
    return path


def member_name(value):
    require(type(value) is str and value and '\\' not in value and not value.startswith('/'),
        'Unsafe runtime archive member path')
    parts = value.split('/')
    require(all(part not in ('', '.', '..') for part in parts), 'Unsafe runtime archive member path')
    return PurePosixPath(value)


def relative_target(parent, target, root):
    require(type(target) is str and target and '\\' not in target and not target.startswith('/'),
        'Runtime archive alias must have a relative target')
    parts = list(parent.parts)
    for part in target.split('/'):
        require(part != '', 'Unsafe runtime archive alias target')
        if part == '.':
            continue
        if part == '..':
            require(len(parts) > 1, 'Runtime archive alias escapes package')
            parts.pop()
        else:
            parts.append(part)
    require(parts and parts[0] == root, 'Runtime archive alias escapes package')
    return PurePosixPath(*parts)


def archive_inventory(path, root):
    inventory = {}
    counts = dict(regular=0, directory=0, symlink=0)
    with tarfile.open(path, 'r|gz') as archive:
        for item in archive:
            name = str(member_name(item.name))
            require(name.split('/')[0] == root, 'Runtime archive member outside selected package')
            require(name not in inventory, 'Duplicate runtime archive member')
            kind = 'regular' if item.isfile() else 'directory' if item.isdir() else 'symlink' if item.issym() else None
            require(kind is not None, 'Unsupported runtime archive member type')
            counts[kind] += 1
            inventory[name] = dict(kind=kind, bytes=item.size, target=item.linkname)
    require(inventory.get(root, {}).get('kind') == 'directory', 'Missing runtime archive package directory')
    return inventory, counts


def resolve_member(name, inventory, install):
    """Resolve every archive and filesystem component together, inside install."""
    root = install.name
    requested = member_name(name)
    require(requested.parts[0] == root, 'Runtime member outside package')
    pending, resolved, seen, aliases = list(requested.parts[1:]), [root], set(), []
    while pending:
        resolved.append(pending.pop(0))
        current = PurePosixPath(*resolved)
        key = str(current)
        require(key in inventory, 'Missing selected runtime archive member')
        item = inventory[key]
        physical = install.parent.joinpath(*current.parts)
        if item['kind'] == 'symlink':
            require(key not in seen, 'Cyclic runtime archive alias')
            seen.add(key)
            require(physical.is_symlink() and os.readlink(physical) == item['target'],
                'Installed runtime alias differs from archive')
            target = relative_target(current.parent, item['target'], root)
            aliases.append(dict(member=key, target=item['target']))
            pending = list(target.parts[1:]) + pending
            resolved = [root]
        elif pending:
            require(item['kind'] == 'directory' and physical.is_dir() and not physical.is_symlink(),
                'Runtime ancestor is not the archived directory')
        else:
            require(item['kind'] == 'regular' and physical.exists() and
                stat.S_ISREG(physical.lstat().st_mode), 'Selected runtime must resolve to a regular archived file')
    require(len(resolved) > 1, 'Selected runtime cannot be the package directory')
    final = str(PurePosixPath(*resolved))
    return final, aliases


def audit_package(identity, install, archive_path, pin):
    require(install.is_dir() and not install.is_symlink() and install.resolve() == install,
        'Runtime installation root must be an unaliased directory')
    require(archive_path.is_file() and not archive_path.is_symlink() and archive_path.resolve() == archive_path,
        'Runtime archive must be an unaliased regular file')
    before = digest(archive_path)
    require(before == pin['sha256'] and identity['archives'].get(str(archive_path)) == before,
        'Runtime archive pin or recorded identity differs')
    inventory, counts = archive_inventory(archive_path, install.name)
    selected = {name: value for name, value in identity['files'].items()
        if absolute(name).is_relative_to(install)}
    require(selected, 'No selected CAD runtime files for package')
    records, targets = {}, {}
    for name, value in sorted(selected.items()):
        require(type(value) is dict and set(value) == {'sha256', 'resolved'} and
            type(value['sha256']) is str and SHA256.fullmatch(value['sha256']),
            'Malformed selected CAD runtime identity')
        relative = str(PurePosixPath(install.name, *absolute(name).relative_to(install).parts))
        final, aliases = resolve_member(relative, inventory, install)
        physical = install.parent.joinpath(*PurePosixPath(final).parts)
        require(str(absolute(value['resolved'])) == str(physical) and Path(name).resolve(strict=True) == physical,
            'Recorded runtime resolution differs from archive')
        if final not in targets:
            targets[final] = dict(sha256=digest(physical), bytes=physical.stat().st_size)
        require(targets[final]['sha256'] == value['sha256'] and
            targets[final]['bytes'] == inventory[final]['bytes'],
            'Current runtime payload differs from selected identity or archive size')
        records[relative] = dict(resolved_member=final, sha256=value['sha256'],
            bytes=targets[final]['bytes'], aliases=aliases)
    payloads = {}
    with tarfile.open(archive_path, 'r|gz') as archive:
        for item in archive:
            if item.name not in targets:
                continue
            require(item.isfile() and item.name not in payloads, 'Selected archive payload changed')
            stream = archive.extractfile(item)
            require(stream is not None, 'Unreadable selected runtime archive payload')
            with stream:
                payloads[item.name] = dict(sha256=hashlib.file_digest(stream, 'sha256').hexdigest(), bytes=item.size)
    require(payloads == targets, 'Selected runtime payload is not an exact regular archive member')
    # Recheck both alias topology and installed payload bytes after the complete
    # archive pass; a changed alias cannot be hidden by equal target contents.
    checked = set()
    for relative, record in records.items():
        final, aliases = resolve_member(relative, inventory, install)
        require(final == record['resolved_member'] and aliases == record['aliases'], 'Runtime alias changed during audit')
        physical = install.parent.joinpath(*PurePosixPath(final).parts)
        require(Path(install.parent.joinpath(*PurePosixPath(relative).parts)).resolve(strict=True) == physical,
            'Runtime resolution changed during audit')
        if final not in checked:
            require(digest(physical) == record['sha256'], 'Runtime payload changed during audit')
            checked.add(final)
    after = digest(archive_path)
    require(after == before, 'Runtime archive changed during audit')
    return dict(install_directory=str(install), archive=str(archive_path), archive_sha256_before=before,
        archive_sha256_after=after, archive_members=counts, selected_files=len(records),
        selected_regular_members=len(targets), selected_aliases=sum(bool(record['aliases']) for record in records.values()),
        selected_regular_payload_bytes=sum(record['bytes'] for record in targets.values()), selected_members=records)


def audit(identity, manifest, tools):
    """Check all identity-selected CIRCT/OSS files without extracting archives.

    The returned dict is deterministic, so parent and immutable-export checks
    can independently recompute it. Counts derive from the actual selection.
    Only the fixed official archive pins below are accepted.
    """
    require(type(identity) is dict and identity.get('installed_payload_archive_membership_proved') is False and
        type(identity.get('files')) is dict and identity['files'] and type(identity.get('archives')) is dict,
        'Expected the unchanged historical runtime-identity boundary')
    require(type(manifest) is dict and manifest.get('platform') == 'darwin-arm64' and
        type(manifest.get('packages')) is dict and type(tools) is dict, 'Invalid CAD runtime manifest or tools')
    for package, pin in PINNED.items():
        actual = manifest['packages'].get(package)
        require(type(actual) is dict and all(actual.get(key) == value for key, value in pin.items()),
            'CAD runtime manifest differs from fixed archive pins')
    circt = absolute(tools.get('circt'))
    parent = circt.parent.parent.parent
    roots = {package: parent / pin['directory'] for package, pin in PINNED.items()}
    for tool, (package, executable) in CAD_TOOLS.items():
        path = absolute(tools.get(tool))
        require(path == roots[package] / 'bin' / executable and str(path) in identity['files'],
            'CAD tool is outside the selected pinned package or identity')
    packages = {}
    try:
        for package, pin in PINNED.items():
            packages[package] = audit_package(identity, roots[package], parent / pin['archive'], pin)
    except (OSError, tarfile.TarError) as error:
        raise ValueError('Unreadable CAD runtime/archive: ' + str(error)) from error
    excluded = {name: value for name, value in identity['files'].items()
        if not any(absolute(name).is_relative_to(root) for root in roots.values())}
    return dict(schema=SCHEMA, cad_selected_archive_membership_verified=True,
        installed_payload_archive_membership_proved=False, packages=packages,
        selected_cad_files=sum(package['selected_files'] for package in packages.values()),
        excluded_identity_files=len(excluded), excluded_identity_sha256=canonical_hash(excluded),
        exclusions=['Lean and Lake runtimes are separately frozen, not members of these CAD archives.',
            'Python, operating-system libraries, shell tools and initialization remain separate runtime assumptions.',
            'Unselected installed files and unselected archive payloads have no membership claim.'])
