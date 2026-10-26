"""Synthetic Git custody fixtures; no CAD tools or historical evidence execute."""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HELPER = Path(__file__).resolve().parents[1] / 'scripts/streaming_8x4_source_recovery.py'
SPEC = importlib.util.spec_from_file_location('source_recovery', HELPER)
RECOVERY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RECOVERY)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class SourceRecoveryTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(); self.addCleanup(tmp.cleanup)
        self.base = Path(tmp.name).resolve(); self.source = self.base / 'original'
        self.source.mkdir(); self.git(None, 'init', '-b', 'source', str(self.source))
        self.git(self.source, 'config', 'user.name', 'Fixture')
        self.git(self.source, 'config', 'user.email', 'fixture@example.invalid')
        self.marker = self.base / 'MUST-NOT-EXECUTE'
        self.data = {'.gitattributes': b'payload.txt filter=evil\n', 'payload.txt': b'raw source\n',
                     'nested/binary.bin': b'\x00\xffbinary\r\n',
                     'nested/run.sh': ('#!/bin/sh\ntouch ' + str(self.marker) + '\n').encode()}
        for name, raw in self.data.items():
            target = self.source / name; target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(raw)
        (self.source / 'nested/run.sh').chmod(0o755)
        self.git(self.source, 'add', '.'); self.git(self.source, 'commit', '-m', 'Fixture')
        self.bundle = self.base / 'source.bundle'; self.repo = self.base / 'verified.git'; self.dest = self.base / 'output'
        self.catalog = self.base / 'catalog.json'; self.index = self.base / 'sources-index.json'
        self.c = dict(schema=RECOVERY.SCHEMA, scope=RECOVERY.SCOPE, source_commit='', source_tree='',
                      source_files=0, source_bytes=0,
                      bundle=dict(ref='refs/heads/source', path_hint='source.bundle', sha256='', bytes=0),
                      index=dict(path='sources-index.json', sha256='', bytes=0, files=0))
        self.refresh_source()

    def git(self, repo, *args, input=None):
        command = ['git'] + (['-C', str(repo)] if repo else []) + list(args)
        return subprocess.check_output(command, env=RECOVERY.git_env(), stderr=subprocess.PIPE, input=input)

    def refresh_source(self):
        self.bundle.unlink(missing_ok=True)
        self.git(self.source, 'bundle', 'create', str(self.bundle), 'refs/heads/source')
        self.c.update(source_commit=self.git(self.source, 'rev-parse', 'HEAD').decode().strip(),
                      source_tree=self.git(self.source, 'rev-parse', 'HEAD^{tree}').decode().strip())
        all_rows = []
        for raw in self.git(self.source, 'ls-tree', '-r', '-l', '-z', 'HEAD').split(b'\0'):
            if raw:
                header, name = raw.split(b'\t', 1); mode, kind, oid, size = header.decode().split()
                data = self.git(self.source, 'cat-file', 'blob', oid)
                all_rows.append(dict(path=name.decode(), git_mode=mode, git_blob=oid, bytes=int(size), sha256=sha(data)))
        self.c.update(source_files=len(all_rows), source_bytes=sum(r['bytes'] for r in all_rows))
        self.c['bundle'].update(sha256=sha(self.bundle.read_bytes()), bytes=self.bundle.stat().st_size)
        # The compact index intentionally covers a subset; the whole tree must recover.
        self.rows = [r for r in all_rows if r['path'] == 'payload.txt']; self.seal()

    def seal(self):
        raw = (json.dumps(self.rows, sort_keys=True) + '\n').encode(); self.index.write_bytes(raw)
        self.c['index'].update(sha256=sha(raw), bytes=len(raw), files=len(self.rows))
        self.catalog.write_text(json.dumps(self.c, sort_keys=True) + '\n', encoding='utf-8')

    def load(self):
        return RECOVERY._load(self.catalog, sha(self.catalog.read_bytes()))

    def verify(self, repo=None):
        return RECOVERY.verify(*self.load(), str(self.bundle), str(repo or self.repo))

    def restore(self, dest=None):
        return RECOVERY.restore(*self.load(), str(self.repo), str(dest or self.dest))

    def test_full_tree_roundtrip_binary_executable_and_source_only_claims(self):
        original = (self.catalog.read_bytes(), self.index.read_bytes(), self.bundle.read_bytes())
        verified = self.verify(); restored = self.restore()
        self.assertEqual(verified['status'], 'source_verified'); self.assertEqual(restored['status'], 'source_restored')
        self.assertEqual(restored['files'], 4); self.assertEqual(restored['bytes'], sum(map(len, self.data.values())))
        for name, raw in self.data.items():
            self.assertEqual((self.dest / name).read_bytes(), raw)
        self.assertEqual((self.dest / 'nested/run.sh').stat().st_mode & 0o777, 0o755)
        self.assertEqual(self.dest.stat().st_mode & 0o777, 0o700)
        for value in (verified, restored):
            self.assertIs(value['source_only'], True)
            for key in ('physical_acceptance', 'model_qualified', 'qualified_timing',
                        'raw_evidence_restored', 'historical_paths_relocated'):
                self.assertIs(value[key], False)
        self.assertEqual(original, (self.catalog.read_bytes(), self.index.read_bytes(), self.bundle.read_bytes()))
        self.assertFalse(self.marker.exists())

    def test_independent_restore_after_bundle_and_original_repository_removed(self):
        self.verify(); self.bundle.unlink(); shutil.rmtree(self.source)
        self.restore(); self.assertEqual((self.dest / 'nested/binary.bin').read_bytes(), self.data['nested/binary.bin'])
        self.assertFalse((self.repo / 'objects/info/alternates').exists())

    def test_bundle_corruption_and_missing_bundle_refused_before_creation(self):
        self.bundle.write_bytes(self.bundle.read_bytes() + b'changed')
        with self.assertRaisesRegex(ValueError, 'Bundle bytes/digest'):
            self.verify()
        self.assertFalse(self.repo.exists()); self.bundle.unlink()
        with self.assertRaises(ValueError):
            self.verify()
        self.assertFalse(self.repo.exists())

    def test_existing_repository_and_destination_never_overwritten(self):
        self.repo.mkdir(); keep = self.repo / 'keep'; keep.write_bytes(b'preserve')
        with self.assertRaisesRegex(ValueError, 'fresh path'):
            self.verify()
        self.assertEqual(keep.read_bytes(), b'preserve'); shutil.rmtree(self.repo); self.verify()
        self.dest.mkdir(); keep = self.dest / 'keep'; keep.write_bytes(b'preserve')
        with self.assertRaisesRegex(ValueError, 'fresh path'):
            self.restore()
        self.assertEqual(keep.read_bytes(), b'preserve')

    def test_wrong_ref_commit_tree_and_full_tree_totals_refused(self):
        original = copy.deepcopy(self.c)
        changes = [('source_commit', '0' * 40), ('source_tree', '0' * 40), ('source_files', 3), ('source_bytes', 0)]
        for number, (key, value) in enumerate(changes):
            with self.subTest(key=key):
                self.c = copy.deepcopy(original); self.c[key] = value; self.seal()
                with self.assertRaises(ValueError):
                    self.verify(self.base / ('bad-' + str(number)))
        self.c = original; self.c['bundle']['ref'] = 'refs/heads/absent'; self.seal()
        with self.assertRaises(ValueError):
            self.verify()

    def test_index_oid_mode_size_path_and_sha256_must_match_source(self):
        original = copy.deepcopy(self.rows)
        for number, (key, value) in enumerate([('git_blob', '0' * 40), ('git_mode', '100755'),
                                              ('bytes', 999), ('path', 'unknown'), ('sha256', '0' * 64)]):
            with self.subTest(key=key):
                self.rows = copy.deepcopy(original); self.rows[0][key] = value; self.seal()
                with self.assertRaises(ValueError):
                    self.verify(self.base / ('bad-' + str(number)))

    def test_unsafe_duplicate_and_unsorted_deferred_paths_refused(self):
        original = copy.deepcopy(self.rows)
        for name in ('../outside', '/absolute', 'a//b', 'a/./b', 'a/.git/config', 'a/.GIT/config', 'a\\b', 'a\nb', 'a. /b'):
            with self.subTest(path=name):
                self.rows = copy.deepcopy(original); self.rows[0]['path'] = name; self.seal()
                with self.assertRaises(ValueError):
                    self.load()
        self.rows = original * 2; self.seal()
        with self.assertRaises(ValueError):
            self.load()
        self.rows = [dict(original[0], path='z'), dict(original[0], path='a')]; self.seal()
        with self.assertRaises(ValueError):
            self.load()

    def test_catalog_and_index_pins_and_strict_json_types(self):
        with self.assertRaisesRegex(ValueError, 'Pinned catalog'):
            RECOVERY._load(self.catalog, '0' * 64)
        self.index.write_bytes(self.index.read_bytes() + b' ')
        with self.assertRaisesRegex(ValueError, 'Index bytes/digest'):
            self.load()
        self.seal(); self.c['source_files'] = True; self.seal()
        with self.assertRaises(ValueError):
            self.load()
        for raw in (b'{"schema":1,"schema":1}', b'{"schema":NaN}'):
            self.catalog.write_bytes(raw)
            with self.assertRaises(ValueError):
                self.load()
        self.assertFalse(self.repo.exists())

    def test_symlink_bundle_repository_parent_and_destination_refused(self):
        alias = self.base / 'alias.bundle'; alias.symlink_to(self.bundle)
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            RECOVERY.verify(*self.load(), str(alias), str(self.repo))
        self.verify(); alias = self.base / 'alias.git'; alias.symlink_to(self.repo, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            RECOVERY.restore(*self.load(), str(alias), str(self.dest))
        foreign = self.base / 'foreign'; foreign.mkdir(); alias = self.base / 'alias'
        alias.symlink_to(foreign, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            self.restore(alias / 'output')
        self.assertEqual(list(foreign.iterdir()), [])

    def test_alternates_http_alternates_partial_store_and_extra_refs_refused(self):
        self.verify()
        for name in ('objects/info/alternates', 'objects/info/http-alternates', 'shallow', 'info/grafts'):
            with self.subTest(name=name):
                target = self.repo / name; target.parent.mkdir(parents=True, exist_ok=True); target.write_text('/foreign\n')
                with self.assertRaisesRegex(ValueError, 'External or incomplete'):
                    self.restore()
                target.unlink()
        promisor = self.repo / 'objects/pack/fake.promisor'; promisor.write_bytes(b'')
        with self.assertRaisesRegex(ValueError, 'Partial object'):
            self.restore()
        promisor.unlink(); self.git(None, '--git-dir=' + str(self.repo), 'update-ref', 'refs/heads/extra', self.c['source_commit'])
        with self.assertRaisesRegex(ValueError, 'reference mismatch'):
            self.restore()
        self.assertFalse(self.dest.exists())

    def test_repository_symlinks_and_configuration_includes_refused(self):
        self.verify(); alias = self.repo / 'objects/foreign'; alias.symlink_to(self.source / '.git/objects')
        with self.assertRaisesRegex(ValueError, 'Repository symlink'):
            self.restore()
        alias.unlink()
        with (self.repo / 'config').open('a') as stream:
            stream.write('\n[include]\npath = /foreign/config\n')
        with self.assertRaisesRegex(ValueError, 'configuration refused'):
            self.restore()

    def test_git_environment_templates_filters_and_archived_scripts_cannot_execute(self):
        template = self.base / 'template'; (template / 'hooks').mkdir(parents=True)
        hook = template / 'hooks/post-update'; hook.write_text('#!/bin/sh\ntouch ' + str(self.marker) + '\n'); hook.chmod(0o755)
        poison = {'GIT_DIR': '/missing', 'GIT_OBJECT_DIRECTORY': '/missing/objects',
                  'GIT_ALTERNATE_OBJECT_DIRECTORIES': '/missing/alternates', 'GIT_TEMPLATE_DIR': str(template),
                  'GIT_CONFIG_COUNT': '1', 'GIT_CONFIG_KEY_0': 'filter.evil.smudge',
                  'GIT_CONFIG_VALUE_0': 'touch ' + str(self.marker)}
        with patch.dict(os.environ, poison):
            self.verify(); self.restore()
        self.assertFalse(self.marker.exists()); self.assertFalse((self.repo / 'hooks').exists())
        self.assertEqual((self.dest / 'payload.txt').read_bytes(), self.data['payload.txt'])

    def test_metadata_drift_refused_before_import_and_after_restore(self):
        loaded = self.load(); self.catalog.write_bytes(self.catalog.read_bytes() + b' ')
        with self.assertRaisesRegex(ValueError, 'Metadata changed'):
            RECOVERY.verify(*loaded, str(self.bundle), str(self.repo))
        self.assertFalse(self.repo.exists()); self.seal(); self.verify()
        original = RECOVERY.blobs
        def drift(repo, rows, destination=None):
            original(repo, rows, destination)
            if destination is not None:
                self.index.write_bytes(self.index.read_bytes() + b' ')
        with patch.object(RECOVERY, 'blobs', drift), self.assertRaisesRegex(ValueError, 'Metadata changed'):
            self.restore()

    def test_bundle_drift_during_verification_refused(self):
        original = RECOVERY.tree; calls = 0
        def drift(*args):
            nonlocal calls
            rows = original(*args); calls += 1
            if calls == 2:
                self.bundle.write_bytes(self.bundle.read_bytes() + b' ')
            return rows
        with patch.object(RECOVERY, 'tree', drift), self.assertRaisesRegex(ValueError, 'Bundle changed'):
            self.verify()

    def test_corrupt_git_blob_refused_before_output(self):
        self.verify()
        for pack in list((self.repo / 'objects/pack').glob('*.pack')):
            raw = pack.read_bytes()
            for name in (pack, pack.with_suffix('.idx'), pack.with_suffix('.rev')):
                name.unlink(missing_ok=True)
            self.git(None, '--git-dir=' + str(self.repo), 'unpack-objects', input=raw)
        oid = self.rows[0]['git_blob']; target = self.repo / 'objects' / oid[:2] / oid[2:]
        target.chmod(0o600); target.write_bytes(b'corrupted object')
        with self.assertRaises(ValueError):
            self.restore()
        self.assertFalse(self.dest.exists())

    def test_restored_file_final_recheck_detects_drift(self):
        self.verify(); original = RECOVERY.blobs
        def drift(repo, rows, destination=None):
            original(repo, rows, destination)
            if destination is not None:
                (destination / 'payload.txt').write_bytes(b'changed')
        with patch.object(RECOVERY, 'blobs', drift), self.assertRaisesRegex(ValueError, 'identity/mode mismatch'):
            self.restore()

    def test_source_tree_symlink_mode_refused(self):
        (self.source / 'link').symlink_to('payload.txt'); self.git(self.source, 'add', 'link')
        self.git(self.source, 'commit', '-m', 'Unsupported symlink'); self.refresh_source()
        with self.assertRaisesRegex(ValueError, 'Unsupported source object'):
            self.verify()

    def test_case_colliding_git_tree_refused_before_restore(self):
        oid = self.rows[0]['git_blob']
        raw = ''.join('100644 blob ' + oid + '\t' + name + '\n' for name in ('PAYLOAD.txt', 'payload.txt')).encode()
        tree = self.git(self.source, 'mktree', input=raw).decode().strip()
        commit = self.git(self.source, 'commit-tree', tree, '-p', 'HEAD', '-m', 'Case collision').decode().strip()
        self.git(self.source, 'update-ref', 'refs/heads/source', commit); self.refresh_source()
        with self.assertRaisesRegex(ValueError, 'Colliding source paths'):
            self.verify()
        self.assertFalse(self.dest.exists())

    def test_production_catalog_is_pinned_and_cli_has_no_catalog_or_run_override(self):
        c, rows, _ = RECOVERY._load(RECOVERY.CATALOG, RECOVERY.CATALOG_SHA256)
        self.assertEqual((c['source_files'], c['source_bytes'], len(rows)), (3628, 75784978, 85))
        cli_root = self.base / 'cli'; (cli_root / 'scripts').mkdir(parents=True)
        helper = cli_root / 'scripts' / HELPER.name; shutil.copyfile(HELPER, helper)
        folder = cli_root / RECOVERY.CATALOG.relative_to(HELPER.parents[1]).parent; folder.mkdir(parents=True)
        (folder / 'source-catalog.json').write_bytes(RECOVERY.CATALOG.read_bytes() + b' ')
        flags = ['-O'] if sys.flags.optimize else []
        run = subprocess.run([sys.executable, *flags, '-I', '-S', '-B', str(helper), 'verify', '--bundle', str(self.bundle),
                              '--repository', str(self.repo)], capture_output=True, check=False)
        self.assertEqual(run.returncode, 1); self.assertIn('Pinned catalog', json.loads(run.stdout)['error'])
        for args in (['--catalog', str(self.catalog)], ['run']):
            run = subprocess.run([sys.executable, '-I', '-S', '-B', str(HELPER), *args], capture_output=True, check=False)
            self.assertEqual(run.returncode, 2)
        self.assertFalse(self.repo.exists())


if __name__ == '__main__':
    unittest.main()
