"""Provenance refusal controls for the retained Python-only snapshot runner."""
import hashlib
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('python_snapshot', ROOT / 'scripts/check-python-snapshot.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def blob(data):
    return hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()


class PythonSnapshotTests(unittest.TestCase):
    def test_tree_rejects_redirected_ambiguous_or_untracked_entries(self):
        valid = '100644 blob ' + 'a' * 40 + '\ttest/test_one.py\0'
        self.assertEqual(gate.parse_tree(valid), {'test/test_one.py': 'a' * 40})
        for bad in ['', valid + valid, valid.replace('100644', '120000'),
                    valid.replace('blob', 'commit'), valid.replace('test/test_one.py', '../outside'),
                    valid.replace('test/test_one.py', '/absolute')]:
            with self.subTest(tree=bad), self.assertRaises(RuntimeError):
                gate.parse_tree(bad)

    def test_exact_blob_membership_and_changed_archived_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'source.py').write_bytes(b'print("committed")\n')
            tree = {'source.py': blob((root / 'source.py').read_bytes())}
            before = gate.membership(root, tree, 'sha1')
            self.assertEqual(before['source.py'], gate.digest(root / 'source.py'))
            (root / 'source.py').write_text('altered after test use\n')
            with self.assertRaisesRegex(RuntimeError, 'differs from selected committed source'):
                gate.membership(root, tree, 'sha1')

    def test_archive_membership_does_not_use_dirty_working_documents(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            snapshot, working = root / 'snapshot', root / 'working'
            snapshot.mkdir()
            working.mkdir()
            (snapshot / 'notes.md').write_text('committed\n')
            (working / 'notes.md').write_text('preexisting user changes\n')
            tree = {'notes.md': blob((snapshot / 'notes.md').read_bytes())}
            self.assertEqual(len(gate.membership(snapshot, tree, 'sha1')), 1)
            self.assertEqual((working / 'notes.md').read_text(), 'preexisting user changes\n')

    def test_symlinked_input_is_rejected_even_when_contents_match(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'original').write_bytes(b'committed')
            (root / 'alias').symlink_to(root / 'original')
            with self.assertRaisesRegex(RuntimeError, 'redirected committed input'):
                gate.membership(root, {'alias': blob(b'committed')}, 'sha1')

    def test_prior_cache_and_import_overrides_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            gate.fresh_snapshot(root)
            for name in ['build', '.lake', '.git', 'hidden.pyc', 'hidden.olean']:
                path = root / name
                path.write_text('old artifact')
                with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'prior repository/build/cache'):
                    gate.fresh_snapshot(root)
                path.unlink()
        for key in ['PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP', 'PYTHONPYCACHEPREFIX']:
            with self.subTest(key=key), self.assertRaisesRegex(RuntimeError, 'Python import/cache overrides'):
                gate.check_environment({key: '/external/cache'})
        gate.check_environment({})

    def test_nonempty_summary_requires_the_exact_verbose_skip_inventory(self):
        output = ('test_one (module.Suite) ... ok\n'
                  "setUpClass (module.Macro) ... skipped 'macro fixture unavailable'\n"
                  '\nRan 1 test in 0.001s\n\nOK (skipped=1)\n')
        summary = gate.test_summary(output)
        self.assertEqual((summary['tests_run'], summary['skipped']), (1, 1))
        self.assertIn('macro fixture unavailable', summary['skips'][0]['reason'])
        for bad in [output.replace('Ran 1', 'Ran 0'), output.replace('OK', 'FAILED'),
                    output.replace('(skipped=1)', '(skipped=2)'), 'no test execution\n']:
            with self.subTest(output=bad), self.assertRaises(RuntimeError):
                gate.test_summary(bad)

    def test_python_payload_changes_are_detected(self):
        with tempfile.TemporaryDirectory() as directory:
            executable = Path(directory) / 'python'
            executable.write_bytes(b'first executable bytes')
            before = gate.python_identity(executable)
            executable.write_bytes(b'second executable bytes')
            self.assertNotEqual(before, gate.python_identity(executable))
        with self.assertRaisesRegex(RuntimeError, 'absolute Python executable'):
            gate.python_identity('relative-python')

    def test_uncommitted_producer_is_refused_before_creating_a_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            environment = dict(os.environ, GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL='/dev/null')
            (root / 'source.py').write_text('# selected committed test source\n')
            for args in [('init', '-q'), ('add', 'source.py'),
                         ('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                          '-c', 'commit.gpgsign=false', '-c', 'core.hooksPath=/dev/null',
                          'commit', '-qm', 'fixture')]:
                subprocess.run(['git', *args], cwd=root, env=environment, check=True, timeout=30)
            with patch.object(gate, 'ROOT', root), patch.object(sys, 'argv', ['check', '--tag', 'qualified']):
                with self.assertRaisesRegex(RuntimeError, 'Commit the producer'):
                    gate.main()
            self.assertFalse((root / 'build').exists())


if __name__ == '__main__':
    unittest.main()
