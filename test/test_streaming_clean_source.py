"""Source-only migration controls in independent, newly created Git history.

No Lean/CAD/proof worker runs. Positive cases establish source identity only.
The optional environment variable is a test-fixture source location, not an
input to the production admission checker.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import types
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path(os.environ.get('PINWHEEL_CLEAN_TEST_ROOT', ROOT)).resolve()
HISTORICAL_POLICY = ROOT/'test/fixtures/clean-source-v1/artifact-policy.json'


def historical_policy_bytes(authority, fixture=HISTORICAL_POLICY):
    """Keep the old checkout independent of the current publication policy."""
    fixture = Path(fixture)
    if not fixture.is_file() or fixture.is_symlink():
        raise ValueError('Missing or aliased historical clean-source policy fixture')
    raw = fixture.read_bytes(); row = authority['admitted_additions']['tools/artifact-policy.json']
    blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    if (len(raw) != row['bytes'] or hashlib.sha256(raw).hexdigest() != row['sha256'] or
            blob != row['git_blob'] or row['git_mode'] != '100644'):
        raise ValueError('Historical clean-source policy fixture differs from authority')
    return raw


def git(root, *args):
    env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
    env.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull, GIT_OPTIONAL_LOCKS='0')
    return subprocess.check_output(['git', *args], cwd=root, env=env, stderr=subprocess.PIPE)


def checker(root):
    path = root/'scripts/streaming_clean_source.py'; m = types.ModuleType('fixture_clean_source')
    m.__file__ = str(path); exec(compile(path.read_bytes(), str(path), 'exec'), m.__dict__)
    return m


class CleanSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.owner = tempfile.TemporaryDirectory(); cls.addClassCleanup(cls.owner.cleanup)
        cls.base = Path(cls.owner.name).resolve(); cls.original = cls.base/'template'; cls.original.mkdir()
        authority = json.loads((ROOT/'physical/validation/clean-source-v1.json').read_bytes())
        rows = dict(authority['source_inputs']); rows.update(authority['admitted_additions'])
        names = (set(rows) | {'scripts/streaming_clean_source.py', 'physical/validation/clean-source-v1.json'} |
                 {p.relative_to(SOURCE).as_posix() for p in (SOURCE/'test').glob('*.py')})
        for name in names:
            source = ROOT/name if (ROOT/name).exists() else SOURCE/name
            target = cls.original/name; target.parent.mkdir(parents=True, exist_ok=True)
            raw = historical_policy_bytes(authority) if name == 'tools/artifact-policy.json' else source.read_bytes()
            target.write_bytes(raw)
            target.chmod(0o755 if rows.get(name, {}).get('git_mode') == '100755' else 0o644)
        git(cls.original, 'init', '-q', '-b', 'source')
        git(cls.original, 'config', 'user.name', 'Source fixture')
        git(cls.original, 'config', 'user.email', 'fixture@example.invalid')
        git(cls.original, 'add', '.')
        git(cls.original, 'commit', '-qm', 'Admitted bytes in independent history')

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name).resolve()/'checkout'
        git(self.base, '-c', 'protocol.file.allow=always', 'clone', '-q', '--no-local', str(self.original), str(self.repo))
        # Clone does not copy the template repository's local identity.
        git(self.repo, 'config', 'user.name', 'Source fixture')
        git(self.repo, 'config', 'user.email', 'fixture@example.invalid')
        self.S = checker(self.repo)

    def commit(self):
        git(self.repo, 'add', '.'); git(self.repo, 'commit', '-qm', 'Fixture mutation')
        return git(self.repo, 'rev-parse', 'HEAD').decode().strip()

    def head(self):
        return git(self.repo, 'rev-parse', 'HEAD').decode().strip()

    def child(self, code, ok=True):
        flags = ['-O'] if sys.flags.optimize else []
        program = 'import sys;sys.path.insert(0,' + repr(str(self.repo/'scripts')) + ');' + code
        run = subprocess.run([sys.executable, *flags, '-I', '-S', '-B', '-c', program],
                             cwd=self.repo, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(run.returncode == 0, ok, run.stdout.decode() + run.stderr.decode())
        return run

    def test_cloned_fixture_commits_without_identity_autodetection(self):
        git(self.repo, 'config', 'user.useConfigOnly', 'true')
        (self.repo/'identity-fixture.txt').write_text('fixture mutation\n')
        self.commit()
        identity = git(self.repo, 'log', '-1', '--format=%an <%ae>%n%cn <%ce>').decode().strip()
        expected = 'Source fixture <fixture@example.invalid>'
        self.assertEqual(identity, expected + '\n' + expected)

    def test_rewritten_history_without_original_objects_admits_identity_only(self):
        for old in (self.S.ORIGIN, self.S.CLEAN_BASE, '787260b07c7dffc06799feeee6fd604e0b290fe7',
                    'd7a5c0d9112d6b442f4447c643a4c2d57b9c986b'):
            with self.assertRaises(subprocess.CalledProcessError): git(self.repo, 'cat-file', '-e', old)
        result = self.S.admit(self.repo, self.head())
        self.assertTrue(result['source_identity_only']); self.assertFalse(result['qualified'])
        self.assertFalse(result['physical_acceptance_claim']); self.assertNotIn('passed', result)
        self.assertEqual(result['checker_sha256'], hashlib.sha256((self.repo/self.S.CHECKER).read_bytes()).hexdigest())
        self.assertEqual(self.S.admit(self.repo, self.head(), result['source_sha256']), result)

    def test_source_mutation_even_committed_is_not_admitted(self):
        p = self.repo/'Pinwheel.lean'; p.write_bytes(p.read_bytes() + b'\n-- changed\n')
        with self.assertRaisesRegex(ValueError, 'Unreviewed selected source'): self.S.admit(self.repo, self.commit())

    def test_adapter_mutation_even_committed_is_not_admitted(self):
        p = self.repo/'scripts/streaming_tt_opt_intake.py'; p.write_bytes(p.read_bytes() + b'\n# changed\n')
        with self.assertRaisesRegex(ValueError, 'Unreviewed selected source'): self.S.admit(self.repo, self.commit())

    def test_policy_mutation_is_not_admitted(self):
        p = self.repo/'tools/artifact-policy.json'; p.write_bytes(p.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'Unreviewed selected source'): self.S.admit(self.repo, self.commit())

    def test_historical_policy_fixture_is_selected_and_corruption_is_refused(self):
        authority = json.loads((ROOT/'physical/validation/clean-source-v1.json').read_bytes())
        raw = historical_policy_bytes(authority)
        self.assertEqual((self.repo/'tools/artifact-policy.json').read_bytes(), raw)
        fixture = self.repo/'corrupted-policy.json'; fixture.write_bytes(raw + b'\n')
        with self.assertRaisesRegex(ValueError, 'fixture differs from authority'):
            historical_policy_bytes(authority, fixture)

    def test_extra_generator_or_test_lean_is_not_admitted(self):
        for name in ('scripts/unreviewed.py', 'scripts/unreviewed.template', 'test/Unreviewed.lean'):
            p = self.repo/name; p.write_text('-- fixture\n')
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'membership'):
                self.S.admit(self.repo, self.commit())
            p.unlink(); self.commit()

    def test_untracked_source_is_not_a_live_fallback(self):
        (self.repo/'scripts/unreviewed.template').write_text('fixture\n')
        with self.assertRaisesRegex(ValueError, 'live scoped source membership'):
            self.S.admit(self.repo, self.head())

    def test_missing_source_is_not_admitted(self):
        (self.repo/'Pinwheel.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'membership'): self.S.admit(self.repo, self.commit())

    def test_manifest_tamper_is_not_admitted(self):
        p = self.repo/self.S.MANIFEST; p.write_bytes(p.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'Unreviewed clean-source manifest'):
            self.S.admit(self.repo, self.commit())

    def test_working_source_and_alias_are_not_admitted(self):
        p = self.repo/'Pinwheel.lean'; raw = p.read_bytes(); p.write_bytes(raw + b'\n')
        with self.assertRaisesRegex(ValueError, 'Live input'): self.S.admit(self.repo, self.head())
        p.unlink(); target = self.repo/'outside.lean'; target.write_bytes(raw); p.symlink_to(target)
        with self.assertRaisesRegex(ValueError, 'aliased'): self.S.admit(self.repo, self.head())

    def test_raw_projection_missing_or_wrong_value_is_not_admitted(self):
        result = self.S.admit(self.repo, self.head())
        for change in ('missing', 'wrong'):
            hashes = dict(result['source_sha256'])
            if change == 'missing': del hashes['Pinwheel.lean']
            else: hashes['Pinwheel.lean'] = '0'*64
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, 'Fresh raw archive'):
                self.S.admit(self.repo, self.head(), hashes)

    def test_late_input_mutation_is_refused(self):
        real = self.S.tree; calls = []
        def changed(*args):
            value = real(*args); calls.append(1)
            if len(calls) == 2:
                p = self.repo/'Pinwheel.lean'; p.write_bytes(p.read_bytes() + b'\n')
            return value
        self.S.tree = changed
        with self.assertRaisesRegex(ValueError, 'before admission closeout'): self.S.admit(self.repo, self.head())

    def test_parent_git_discovery_cannot_admit_plain_source_copy(self):
        nested = self.repo/'snapshot'; shutil.copytree(self.repo/'scripts', nested/'scripts')
        shutil.copytree(self.repo/'physical', nested/'physical')
        with self.assertRaisesRegex(ValueError, 'Explicit clean repository'):
            checker(nested).admit(nested, self.head())

    def test_clean_recipe_and_existing_refusals_work_without_old_git_objects(self):
        # Real existing candidate tests, with only their explicit mode change.
        flags = ['-O'] if sys.flags.optimize else []
        run = subprocess.run([sys.executable, *flags, '-I', '-S', '-B',
                              str(self.repo/'test/test_streaming_tt_candidate.py')],
                             cwd=self.repo, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(run.returncode, 0, run.stdout.decode() + run.stderr.decode())

    def test_historical_recipe_default_still_requires_historical_objects(self):
        self.child("import json,streaming_tt_candidate as C;C.recipe_experiment(json.load(open('physical/streaming-tt-candidate.json')))", ok=False)

    def test_explicit_staging_contains_all_validation_data_without_checkout_fallback(self):
        code = """import json,hashlib
from pathlib import Path
import streaming_tt_candidate as C,streaming_tt_physical as P,streaming_clean_source as S
from streaming_tt_intake import dependency_closure,stage_sources
root=Path.cwd();data=S.data_inputs(root);sources=P.producer_hashes(optimized=True);sources.update(data)
closure=dependency_closure(root,list(sources));assert set(closure['files'])==set(sources)
dest=root/'staged';stage_sources(root,dest,closure['files'],P.committed)
assert all((dest/n).stat().st_mode&0o222==0 for n in (*S.DATA,S.CHECKER))
assert not (dest/'.git').exists()
print(json.dumps({'staged':str(dest),'inputs':sources}))
"""
        out = self.child(code); info = json.loads(out.stdout); staged = Path(info['staged'])
        # A fresh process imports the staged modules, reads staged JSON and SDC,
        # and succeeds while original validation JSON is deliberately unavailable.
        for name in self.S.DATA: (self.repo/name).rename(self.repo/(name+'.held'))
        program = ('import sys,json;sys.path.insert(0,' + repr(str(staged/'scripts')) + ');'
                   'import streaming_tt_candidate as C;'
                   'C.recipe_experiment(json.load(open("physical/streaming-tt-candidate.json")),source_mode="clean-v1",producer_sha256=' + repr(info['inputs']) + ')')
        flags = ['-O'] if sys.flags.optimize else []
        run = subprocess.run([sys.executable,*flags,'-I','-S','-B','-c',program], cwd=self.repo,
                             stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        self.assertEqual(run.returncode,0,run.stderr.decode())

    def test_fake_pass_cannot_skip_full_raw_archive_and_worker_checks(self):
        report = self.repo/'fake/report.json'; report.parent.mkdir()
        report.write_text(json.dumps(dict(passed=True,stage='components',source_commit=self.head(),producer_commit=self.head())))
        (report.parent/'worker-config.json').write_text('{}')
        code = """import subprocess
import streaming_tt_opt_intake as I
real=subprocess.Popen
def only_git(argv,*a,**k):
    if not isinstance(argv,list) or argv[0]!='git': raise AssertionError('Unexpected non-Git process')
    return real(argv,*a,**k)
subprocess.Popen=only_git
try:I.validate_raw('fake/report.json',%r,source_mode='clean-v1')
except (ValueError,KeyError):print('refused')
else:raise AssertionError('Fake pass accepted')
""" % self.head()
        self.assertEqual(self.child(code).stdout.strip(), b'refused')

    def test_historical_raw_default_keeps_ancestry_refusal(self):
        report = self.repo/'fake/report.json'; report.parent.mkdir()
        report.write_text(json.dumps(dict(passed=True,stage='components',source_commit=self.head(),producer_commit=self.head())))
        (report.parent/'worker-config.json').write_text('{}')
        code = """import streaming_tt_opt_intake as I
try:I.validate_raw('fake/report.json',%r)
except ValueError as e:
    assert 'approved campaign lineage' in str(e);print('refused')
else:raise AssertionError('Historical lineage bypassed')
""" % self.head()
        self.assertEqual(self.child(code).stdout.strip(), b'refused')


if __name__ == '__main__': unittest.main()
