"""Temporary Git fixtures exercise the real CLI; no historical data is edited."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import zlib

HELPER = Path(__file__).resolve().parents[1] / 'scripts/local-evidence.py'
ROOTS = ['docs/research/streaming-tt-routing-rc-tooling-20261019',
         'docs/research/streaming-tt-renewal-tooling-20261018',
         'docs/research/evidence/streaming-tt-20261018']


def sha(data):
    return hashlib.sha256(data).hexdigest()


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name).resolve(); self.original = self.base / 'original'
        self.original.mkdir(); self.git('init', '-b', 'evidence-source', str(self.original))
        self.git('-C', str(self.original), 'config', 'user.name', 'Fixture')
        self.git('-C', str(self.original), 'config', 'user.email', 'fixture@example.invalid')
        self.data = {ROOTS[0] + '/report.json': b'{"answer":42}\n',
                     ROOTS[1] + '/binary.gz': b'\x00\xffbinary\r\n',
                     ROOTS[2] + '/run.sh': b'#!/bin/sh\nexit 0\n'}
        for name, data in self.data.items():
            path = self.original / name; path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(data)
        (self.original / (ROOTS[2] + '/run.sh')).chmod(0o755)
        self.git('-C', str(self.original), 'add', '.')
        self.git('-C', str(self.original), 'commit', '-m', 'Fixture')
        self.commit = self.git('-C', str(self.original), 'rev-parse', 'HEAD').decode().strip()
        self.tree = self.git('-C', str(self.original), 'rev-parse', 'HEAD^{tree}').decode().strip()
        self.bundle = self.base / 'original.bundle'
        self.git('-C', str(self.original), 'bundle', 'create', str(self.bundle), 'refs/heads/evidence-source')
        self.rows = []
        for raw in self.git('-C', str(self.original), 'ls-tree', '-r', '-z', 'HEAD').split(b'\0'):
            if raw:
                head, name = raw.split(b'\t'); mode, kind, oid = head.decode().split(); name = name.decode()
                self.rows.append(dict(path=name, git_mode=mode, git_blob=oid,
                                      bytes=len(self.data[name]), sha256=sha(self.data[name])))
        self.rows.sort(key=lambda r: r['path'])
        self.catalog = self.base / 'catalog/archive.json'; self.catalog.parent.mkdir()
        self.index = self.catalog.parent / 'payload-index.jsonl'; self.repo = self.base / 'restored.git'
        self.c = dict(schema=1, source_commit=self.commit, source_tree=self.tree,
                      bundle=dict(sha256=sha(self.bundle.read_bytes()), bytes=self.bundle.stat().st_size,
                                  ref='refs/heads/evidence-source', path_hint='original.bundle'),
                      index=dict(path='docs/research/local-evidence/payload-index.jsonl', sha256='', bytes=0, files=3),
                      excluded_roots=ROOTS)
        self.seal_index()

    def git(self, *args, input=None):
        env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
        env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM='1', GIT_OPTIONAL_LOCKS='0')
        return subprocess.check_output(['git', *args], env=env, stderr=subprocess.PIPE, input=input)

    def seal_index(self):
        raw = b''.join((json.dumps(r, sort_keys=True) + '\n').encode() for r in self.rows)
        self.index.write_bytes(raw); self.c['index'].update(sha256=sha(raw), bytes=len(raw), files=len(self.rows))
        self.catalog.write_text(json.dumps(self.c), encoding='utf-8')

    def cli(self, *args, ok=True):
        flags = ['-O'] if sys.flags.optimize else []
        run = subprocess.run([sys.executable, *flags, '-I', '-S', '-B', str(HELPER), '--catalog', str(self.catalog), *args],
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        self.assertEqual(run.returncode == 0, ok, run.stdout.decode() + run.stderr.decode())
        value = json.loads(run.stdout); self.assertEqual(value['status'] == 'refused', not ok)
        return value

    def verify(self, ok=True):
        return self.cli('verify', '--bundle', str(self.bundle), '--repository', str(self.repo), ok=ok)

    def restore(self, *args, ok=True):
        return self.cli('restore', '--repository', str(self.repo), '--destination', str(self.base / 'output'), *args, ok=ok)

    def test_roundtrip_all_binary_executable_and_metadata_unchanged(self):
        original = (self.catalog.read_bytes(), self.index.read_bytes(), self.bundle.read_bytes())
        self.assertEqual(self.verify()['files'], 3); self.assertEqual(self.restore('--all')['files'], 3)
        for name, data in self.data.items():
            self.assertEqual((self.base / 'output' / name).read_bytes(), data)
        self.assertEqual((self.base / 'output' / (ROOTS[2] + '/run.sh')).stat().st_mode & 0o777, 0o755)
        self.assertEqual(original, (self.catalog.read_bytes(), self.index.read_bytes(), self.bundle.read_bytes()))

    def test_selective_restore_does_not_fetch_or_require_original_bundle(self):
        self.verify(); self.bundle.unlink()
        self.assertEqual(self.restore('--path', ROOTS[1] + '/binary.gz')['files'], 1)
        self.assertFalse((self.base / 'output' / (ROOTS[0] + '/report.json')).exists())

    def test_changed_bundle_refused_before_repository_creation(self):
        with self.bundle.open('ab') as f: f.write(b'changed')
        self.verify(ok=False); self.assertFalse(self.repo.exists())

    def test_missing_bundle_refused(self):
        self.bundle.unlink(); self.verify(ok=False); self.assertFalse(self.repo.exists())

    def test_changed_index_refused(self):
        with self.index.open('ab') as f: f.write(b' ')
        self.verify(ok=False); self.assertFalse(self.repo.exists())

    def test_index_blob_hash_refused(self):
        self.rows[0]['sha256'] = '0' * 64; self.seal_index(); self.verify(ok=False)

    def test_index_blob_id_refused(self):
        self.rows[0]['git_blob'] = self.rows[1]['git_blob']; self.seal_index(); self.verify(ok=False)

    def test_missing_tree_member_refused(self):
        self.rows.pop(); self.seal_index(); self.verify(ok=False)

    def test_extra_outside_root_refused(self):
        self.rows[0]['path'] = 'foreign/payload'; self.seal_index(); self.verify(ok=False)

    def test_duplicate_and_unsorted_index_paths_refused(self):
        self.rows.append(dict(self.rows[0])); self.seal_index(); self.verify(ok=False)
        self.rows.pop(); self.rows.reverse(); self.seal_index(); self.verify(ok=False)

    def test_schema_boolean_and_duplicate_json_key_refused(self):
        self.c['schema'] = True; self.seal_index(); self.verify(ok=False)
        self.catalog.write_text('{"schema":1,"schema":1}', encoding='utf-8'); self.verify(ok=False)

    def test_partial_or_existing_repository_refused(self):
        self.repo.mkdir(); self.verify(ok=False); self.assertEqual(list(self.repo.iterdir()), [])

    def test_wrong_commit_refused(self):
        self.c['source_commit'] = '0' * 40; self.seal_index(); self.verify(ok=False)

    def test_wrong_tree_refused(self):
        self.c['source_tree'] = '0' * 40; self.seal_index(); self.verify(ok=False)

    def test_unknown_traversal_and_duplicate_requests_refused(self):
        self.verify()
        for name in ('unknown', '../outside', '/absolute', ROOTS[0] + '/../../outside', ROOTS[0] + '//report.json'):
            self.restore('--path', name, ok=False)
        name = ROOTS[0] + '/report.json'; self.restore('--path', name, '--path', name, ok=False)
        self.assertFalse((self.base / 'output').exists())

    def test_overwrite_refused_without_change(self):
        self.verify(); name = ROOTS[0] + '/report.json'; path = self.base / 'output' / name
        path.parent.mkdir(parents=True); path.write_bytes(b'preserve')
        self.restore('--path', name, ok=False); self.assertEqual(path.read_bytes(), b'preserve')

    def test_symlink_parent_and_repository_alias_refused(self):
        self.verify(); foreign = self.base / 'foreign'; foreign.mkdir()
        output = self.base / 'output'; output.symlink_to(foreign, target_is_directory=True)
        self.restore('--all', ok=False); self.assertEqual(list(foreign.iterdir()), [])
        output.unlink(); alias = self.base / 'alias.git'; alias.symlink_to(self.repo, target_is_directory=True)
        self.cli('restore', '--repository', str(alias), '--destination', str(output), '--all', ok=False)

    def test_nested_symlink_parent_refused(self):
        self.verify(); output = self.base / 'output'; output.mkdir()
        foreign = self.base / 'foreign'; foreign.mkdir()
        (output / 'docs').symlink_to(foreign, target_is_directory=True)
        self.restore('--all', ok=False); self.assertEqual(list(foreign.iterdir()), [])

    def test_corrupt_loose_blob_refused_before_output(self):
        self.verify(); row = self.rows[0]; payload = b'x' * row['bytes']
        # Git may prefer packed objects over a conflicting loose object. Convert
        # this temporary repository to loose objects before injecting corruption.
        pack = next((self.repo / 'objects/pack').glob('*.pack')); packed = pack.read_bytes()
        for entry in (self.repo / 'objects/pack').iterdir(): entry.unlink()
        self.git('--git-dir=' + str(self.repo), 'unpack-objects', input=packed)
        target = self.repo / 'objects' / row['git_blob'][:2] / row['git_blob'][2:]
        target.parent.mkdir(exist_ok=True)
        target.chmod(0o600)
        target.write_bytes(zlib.compress(b'blob ' + str(len(payload)).encode() + b'\0' + payload))
        self.restore('--path', row['path'], ok=False); self.assertFalse((self.base / 'output').exists())

    def test_alternate_object_store_refused(self):
        self.verify(); path = self.repo / 'objects/info/alternates'; path.write_text('/foreign/objects\n')
        self.restore('--all', ok=False)


if __name__ == '__main__':
    unittest.main()
