"""Selected CAD archive provenance must fail closed without extraction."""
from copy import deepcopy
import hashlib
import io
import json
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import streaming_mapped_runtime as runtime


class RuntimeTests(unittest.TestCase):
    def fixture(self, root, *, extra=(), alias_target='libreal.dylib'):
        pins, tools, files, archives = deepcopy(runtime.PINNED), {}, {}, {}
        for package, pin in pins.items():
            install = root / pin['directory']
            (install / 'bin').mkdir(parents=True)
            (install / 'lib').mkdir()
            payloads = {}
            for tool, (owner, executable) in runtime.CAD_TOOLS.items():
                if package == owner:
                    path = install / 'bin' / executable
                    data = (package + ':' + tool).encode(); path.write_bytes(data)
                    payloads[str(path.relative_to(root))] = data
                    tools[tool] = str(path)
                    files[str(path)] = dict(sha256=hashlib.sha256(data).hexdigest(), resolved=str(path))
            payload = install / 'lib/libreal.dylib'; payload.write_bytes(b'actual runtime payload')
            alias = install / 'lib/libalias.dylib'; alias.symlink_to(alias_target)
            files[str(alias)] = dict(sha256=runtime.digest(payload), resolved=str(payload))
            payloads[str(payload.relative_to(root))] = payload.read_bytes()
            archive = root / pin['archive']
            entries = [(pin['directory'], tarfile.DIRTYPE, b'', ''),
                (pin['directory'] + '/bin', tarfile.DIRTYPE, b'', ''),
                (pin['directory'] + '/lib', tarfile.DIRTYPE, b'', '')]
            entries += [(name, tarfile.REGTYPE, data, '') for name, data in payloads.items()]
            entries += [(str(alias.relative_to(root)), tarfile.SYMTYPE, b'', alias_target)]
            entries += list(extra)
            with tarfile.open(archive, 'w:gz') as stream:
                for name, kind, data, target in entries:
                    entry = tarfile.TarInfo(name); entry.type = kind; entry.linkname = target
                    entry.size = len(data) if kind == tarfile.REGTYPE else 0
                    stream.addfile(entry, io.BytesIO(data) if entry.size else None)
            pin['sha256'] = runtime.digest(archive); archives[str(archive)] = pin['sha256']
        excluded = root / 'trusted-python'; excluded.write_bytes(b'separately frozen')
        files[str(excluded)] = dict(sha256=runtime.digest(excluded), resolved=str(excluded))
        identity = dict(files=files, archives=archives, installed_payload_archive_membership_proved=False)
        manifest = dict(platform='darwin-arm64', packages=deepcopy(pins))
        return pins, identity, manifest, tools

    def test_positive_is_deterministic_narrow_and_does_not_extract_or_upgrade_history(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root)
            original = deepcopy(identity)
            with patch.object(runtime, 'PINNED', pins), patch.object(tarfile.TarFile, 'extract', side_effect=AssertionError), \
                    patch.object(tarfile.TarFile, 'extractall', side_effect=AssertionError):
                first = runtime.audit(identity, manifest, tools)
                self.assertEqual(first, runtime.audit(identity, manifest, tools))
            self.assertEqual(identity, original)
            self.assertEqual(first['schema'], runtime.SCHEMA)
            self.assertIs(first['cad_selected_archive_membership_verified'], True)
            self.assertIs(first['installed_payload_archive_membership_proved'], False)
            self.assertEqual(first['selected_cad_files'], 8)
            self.assertEqual(first['excluded_identity_files'], 1)
            self.assertEqual(sum(value['selected_aliases'] for value in first['packages'].values()), 2)
            self.assertEqual(set(first['packages']), {'circt', 'oss-cad-suite'})
            json.dumps(first)

    def test_fixed_manifest_pins_cannot_be_replaced_by_matching_untrusted_archive(self):
        with tempfile.TemporaryDirectory() as temporary:
            _, identity, manifest, tools = self.fixture(Path(temporary).resolve())
            with self.assertRaisesRegex(ValueError, 'fixed archive pins'):
                runtime.audit(identity, manifest, tools)

    def test_archive_changed_even_when_selected_files_are_identical_refuses(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root)
            (root / pins['circt']['archive']).write_bytes(b'not the pinned compressed archive')
            with patch.object(runtime, 'PINNED', pins), self.assertRaisesRegex(ValueError, 'archive pin'):
                runtime.audit(identity, manifest, tools)

    def test_current_payload_and_recorded_resolution_are_both_checked(self):
        for mode in ('payload', 'recorded-hash', 'resolved'):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root)
                path = tools['circt']
                if mode == 'payload': Path(path).write_bytes(b'changed installed executable')
                elif mode == 'recorded-hash': identity['files'][path]['sha256'] = '0' * 64
                else: identity['files'][path]['resolved'] = str(root / 'trusted-python')
                with patch.object(runtime, 'PINNED', pins), self.assertRaises(ValueError):
                    runtime.audit(identity, manifest, tools)

    def test_matching_current_and_recorded_bytes_still_require_actual_archive_payload(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root)
            path = Path(tools['circt'])
            path.write_bytes(b'x' * path.stat().st_size)
            identity['files'][str(path)]['sha256'] = runtime.digest(path)
            with patch.object(runtime, 'PINNED', pins), self.assertRaisesRegex(ValueError, 'exact regular archive member'):
                runtime.audit(identity, manifest, tools)

    def test_equal_bytes_do_not_hide_changed_alias_topology(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root)
            install = root / pins['circt']['directory']; alias = install / 'lib/libalias.dylib'
            (install / 'lib/other.dylib').write_bytes((install / 'lib/libreal.dylib').read_bytes())
            alias.unlink(); alias.symlink_to('other.dylib')
            with patch.object(runtime, 'PINNED', pins), self.assertRaisesRegex(ValueError, 'alias differs'):
                runtime.audit(identity, manifest, tools)

    def test_alias_escape_absolute_cycle_and_missing_targets_refuse(self):
        for target in ('../../../outside', '/absolute/path', 'libalias.dylib', 'missing.dylib'):
            with self.subTest(target=target), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root, alias_target=target)
                with patch.object(runtime, 'PINNED', pins), self.assertRaises(ValueError):
                    runtime.audit(identity, manifest, tools)

    def test_duplicate_unsafe_hardlink_and_outside_members_refuse_even_when_unselected(self):
        for entry in (
                ('firtool-1.159.0/bin/circt-opt', tarfile.REGTYPE, b'duplicate', ''),
                ('firtool-1.159.0/../escape', tarfile.REGTYPE, b'bad', ''),
                ('firtool-1.159.0/hard', tarfile.LNKTYPE, b'', 'firtool-1.159.0/bin/circt-opt'),
                ('outside', tarfile.REGTYPE, b'bad', '')):
            with self.subTest(entry=entry[0]), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root, extra=[entry])
                with patch.object(runtime, 'PINNED', pins), self.assertRaises(ValueError):
                    runtime.audit(identity, manifest, tools)

    def test_tool_selection_cannot_escape_package_or_omit_identity(self):
        for mode in ('outside', 'omitted', 'noncanonical', 'wrong-boundary'):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root)
                if mode == 'outside': tools['vvp'] = str(root / 'trusted-python')
                elif mode == 'omitted': identity['files'].pop(tools['vvp'])
                elif mode == 'noncanonical': tools['vvp'] = str(root) + '/oss-cad-suite/bin/../bin/vvp'
                else: identity['installed_payload_archive_membership_proved'] = True
                with patch.object(runtime, 'PINNED', pins), self.assertRaises(ValueError):
                    runtime.audit(identity, manifest, tools)

    def test_selected_missing_member_and_symlinked_archive_refuse(self):
        for mode in ('member', 'archive'):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root)
                if mode == 'member':
                    path = root / pins['circt']['directory'] / 'lib/not-in-archive'
                    path.write_bytes(b'extra'); identity['files'][str(path)] = dict(sha256=runtime.digest(path), resolved=str(path))
                else:
                    path = root / pins['circt']['archive']; target = root / 'redirected-archive'
                    path.rename(target); path.symlink_to(target.name)
                with patch.object(runtime, 'PINNED', pins), self.assertRaises(ValueError):
                    runtime.audit(identity, manifest, tools)

    def test_every_ancestor_and_alias_chain_must_match_archive_topology(self):
        with tempfile.TemporaryDirectory() as temporary:
            install = Path(temporary).resolve() / 'package'
            (install / 'lib').mkdir(parents=True)
            (install / 'lib/payload').write_bytes(b'regular payload')
            (install / 'lib/alias').symlink_to('payload')
            (install / 'share').symlink_to('lib')
            inventory = {'package': dict(kind='directory'), 'package/lib': dict(kind='directory'),
                'package/lib/payload': dict(kind='regular'),
                'package/lib/alias': dict(kind='symlink', target='payload'),
                'package/share': dict(kind='symlink', target='lib')}
            final, aliases = runtime.resolve_member('package/share/alias', inventory, install)
            self.assertEqual(final, 'package/lib/payload')
            self.assertEqual(aliases, [dict(member='package/share', target='lib'),
                dict(member='package/lib/alias', target='payload')])
            # The same payload reached through an unexpected directory alias
            # must not pass merely because its final hash remains identical.
            (install / 'share').unlink(); (install / 'share').mkdir()
            (install / 'share/alias').symlink_to('../lib/payload')
            with self.assertRaisesRegex(ValueError, 'alias differs'):
                runtime.resolve_member('package/share/alias', inventory, install)

    def test_missing_recorded_archive_pin_and_malformed_selected_hash_refuse(self):
        for mode in ('archive', 'hash'):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root)
                if mode == 'archive': identity['archives'].clear()
                else: identity['files'][tools['circt']]['sha256'] = True
                with patch.object(runtime, 'PINNED', pins), self.assertRaises(ValueError):
                    runtime.audit(identity, manifest, tools)

    def test_payload_and_archive_mutations_during_audit_refuse(self):
        for mode in ('payload', 'archive'):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary).resolve(); pins, identity, manifest, tools = self.fixture(root)
                original = runtime.resolve_member; calls = 0
                selected_count = sum(Path(name).is_relative_to(root / pins['circt']['directory']) for name in identity['files'])
                def change_on_closeout(*args):
                    nonlocal calls
                    calls += 1
                    if calls == selected_count + 1:
                        if mode == 'payload': Path(tools['circt']).write_bytes(b'changed during archive pass')
                        else:
                            archive = root / pins['circt']['archive']
                            with archive.open('ab') as stream: stream.write(b'changed')
                    return original(*args)
                with patch.object(runtime, 'PINNED', pins), patch.object(runtime, 'resolve_member', side_effect=change_on_closeout), \
                        self.assertRaisesRegex(ValueError, 'changed during audit'):
                    runtime.audit(identity, manifest, tools)


if __name__ == '__main__':
    unittest.main()
