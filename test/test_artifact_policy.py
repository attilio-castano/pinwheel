"""Artifact publication controls in isolated temporary Git repositories only."""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / 'scripts/check-artifacts.py'
SPEC = importlib.util.spec_from_file_location('artifact_policy_guard', SCRIPT)
G = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(G)


class Repository:
    def __init__(self, policy=True):
        self.temp = tempfile.TemporaryDirectory(); self.root = Path(self.temp.name).resolve()
        self.git('init', '-q'); self.put('README.md', b'source\n'); self.commit()
        self.origin = self.git('rev-parse', 'HEAD').decode().strip()
        # Deliberately absent provenance object: runtime must survive squash merges.
        self.policy = dict(schema=1, baseline_commit='f'*40, max_blob_bytes=G.MIB,
                           max_changed_bytes=25*G.MIB, max_changed_files=1000,
                           bounded_index=dict(path='docs/research/local-evidence/payload-index.jsonl',
                                              max_bytes=4*G.MIB, max_rows=16000), exceptions={})
        if policy:
            self.install_policy(); self.commit()

    def git(self, *args, check=True):
        env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_')}
        env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM='1', GIT_TERMINAL_PROMPT='0')
        p = subprocess.run(['git', '-C', str(self.root), '-c', 'core.hooksPath='+os.devnull,
                            '-c', 'commit.gpgsign=false', '-c', 'user.name=Artifact fixture',
                            '-c', 'user.email=fixture@example.invalid', *args],
                           env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if check and p.returncode:
            raise AssertionError(p.stderr.decode())
        return p.stdout if check else p.returncode

    def put(self, name, raw):
        p = self.root/name; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(raw)
        return p

    def add(self, name, force=False):
        self.git('add', *(['-f'] if force else []), '--', name)

    def install_policy(self):
        self.put(G.POLICY, (json.dumps(self.policy)+'\n').encode()); self.add(G.POLICY)

    def commit(self):
        self.git('add', '-A'); self.git('commit', '-qm', 'isolated fixture')
        return self.git('rev-parse', 'HEAD').decode().strip()

    def cli(self, *args):
        p = subprocess.run([sys.executable, '-B', str(SCRIPT), '--repository', str(self.root), *args],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return p.returncode, json.loads(p.stdout)

    def close(self):
        self.temp.cleanup()


class ArtifactPolicyTests(unittest.TestCase):
    def setUp(self):
        self.r = Repository(); self.addCleanup(self.r.close)

    def result(self):
        return G.check(self.r.root, self.r.policy)

    def rejected(self):
        result = self.result(); self.assertEqual(result['status'], 'refused'); return result

    def test_source_formats_are_not_blanket_banned(self):
        for name in ('Pinwheel/Proof.lean', 'scripts/generator.py', 'physical/recipe.json', 'test/source.sv'):
            self.r.put(name, b'ordinary source\n'); self.r.add(name)
        self.assertEqual(self.result()['status'], 'passed')

    def test_forced_ignored_build_is_refused(self):
        self.r.put('.gitignore', b'build/\n'); self.r.add('.gitignore')
        self.r.put('build/run/report.json', b'{}'); self.r.add('build/run/report.json', force=True)
        self.assertIn('build/run/report.json', ' '.join(self.rejected()['errors']))

    def test_new_dated_tree_is_refused_even_if_python(self):
        name = 'docs/research/next-tooling-20300101/native.py'
        self.r.put(name, b'source copied into a raw archive'); self.r.add(name); self.rejected()

    def test_new_evidence_tree_is_not_a_compact_manifest_escape(self):
        name = 'docs/research/evidence/future-20300101/manifest.json'
        self.r.put(name, b'{}'); self.r.add(name); self.rejected()

    def test_cache_and_compiled_paths_refuse(self):
        for name in ('__pycache__/a.py', 'test/a.olean', '.lake/Proof.lean', 'src/a.pyc'):
            self.r.put(name, b'x'); self.r.add(name, force=True)
        self.assertEqual(len(self.rejected()['errors']), 4)

    def test_raw_payload_extension_refuses_outside_known_trees(self):
        self.r.put('notes/route.odb', b'raw'); self.r.add('notes/route.odb'); self.rejected()

    def test_exact_legacy_fixture_allowed_and_changed_bytes_refused(self):
        name = 'tools/example/tests/fixtures/report.rpt.gz'; raw = b'known gzip-like bytes'
        self.r.policy['exceptions'][name] = dict(sha256=hashlib.sha256(raw).hexdigest(),
            bytes=len(raw), git_mode='100644', reason='exact preserved fixture')
        self.r.install_policy(); self.r.put(name, raw); self.r.add(name)
        self.assertIn(name, self.result()['legacy_exemptions'])
        self.r.put(name, b'X'+raw[1:]); self.r.add(name); self.rejected()

    def test_exception_cannot_admit_compiled(self):
        self.r.policy['exceptions']['a.olean'] = dict(sha256='a'*64, bytes=1,
            git_mode='100644', reason='invalid')
        with self.assertRaises(ValueError): self.result()

    def test_legacy_exception_mode_change_refused(self):
        name = 'old.log'; raw = b'exact fixture'
        self.r.policy['exceptions'][name] = dict(sha256=hashlib.sha256(raw).hexdigest(),
            bytes=len(raw), git_mode='100644', reason='preserved fixture')
        self.r.put(name, raw); self.r.add(name); self.assertEqual(self.result()['status'], 'passed')
        self.r.git('update-index', '--chmod=+x', '--', name); self.rejected()

    def test_renamed_binary_signature_cannot_hide_as_text(self):
        self.r.put('notes.txt', b'\x7fELF'+b'x'*50); self.r.add('notes.txt'); self.rejected()

    def test_index_blob_wins_over_working_tree_payload(self):
        p = self.r.put('data.json', b'{}'); self.r.add('data.json'); p.write_bytes(b'x'*(G.MIB+1))
        self.assertEqual(self.result()['status'], 'passed')
        self.r.add('data.json'); p.write_bytes(b'{}'); self.rejected()

    def test_selected_policy_blob_wins_over_working_policy(self):
        self.r.put(G.POLICY, b'not JSON and never selected')
        code, result = self.r.cli(); self.assertEqual(code, 0)
        self.assertEqual(result['policy_origin'], 'selected-Git-blob')

    def test_late_index_change_refuses(self):
        from unittest.mock import patch
        self.r.put('first.py', b'ordinary'); self.r.add('first.py')
        original = G.object_size; changed = []
        def observe(repo, oid):
            if not changed:
                changed.append(True); self.r.put('late.py', b'late'); self.r.add('late.py')
            return original(repo, oid)
        with patch.object(G, 'object_size', side_effect=observe):
            with self.assertRaisesRegex(ValueError, 'index changed'):
                self.result()

    def test_git_discovery_limits_survive_environment_sanitization(self):
        from unittest.mock import patch
        isolated = self.r.root/'snapshot'/'nested'; isolated.mkdir(parents=True)
        with patch.dict(os.environ, GIT_CEILING_DIRECTORIES=str(self.r.root),
                        GIT_DISCOVERY_ACROSS_FILESYSTEM='0', GIT_DIR='/untrusted/missing'):
            with self.assertRaisesRegex(ValueError, 'Local Git input unavailable'):
                G.git(isolated, 'rev-parse', '--show-toplevel')
            self.assertEqual(G.git(self.r.root, 'rev-parse', '--show-toplevel').decode().strip(), str(self.r.root))

    def test_per_blob_and_aggregate_budgets(self):
        self.r.put('huge.json', b'x'*(G.MIB+1)); self.r.add('huge.json'); self.rejected()
        self.r.git('reset', '-q', '--', 'huge.json'); (self.r.root/'huge.json').unlink()
        self.r.policy['max_changed_bytes'] = 5
        for name in ('a.json', 'b.json'):
            self.r.put(name, b'123'); self.r.add(name)
        self.assertIn('Aggregate', ' '.join(self.rejected()['errors']))

    def test_changed_file_budget(self):
        self.r.policy['max_changed_files'] = 1
        for name in ('a.py', 'b.py'):
            self.r.put(name, b'x'); self.r.add(name)
        self.assertIn('Changed-file', ' '.join(self.rejected()['errors']))

    def test_special_git_mode_refuses(self):
        self.r.put('target', b'ordinary'); os.symlink('target', self.r.root/'alias.py')
        self.r.add('target'); self.r.add('alias.py'); self.rejected()

    def index_row(self, name):
        return dict(path=name, git_mode='100644', git_blob='a'*40, bytes=12, sha256='b'*64)

    def test_bounded_index_accepts_large_structured_rows(self):
        rows = [self.index_row('docs/research/old/file-'+str(n).zfill(5)+'.json') for n in range(6000)]
        raw = b'\n'.join(json.dumps(r).encode() for r in rows)+b'\n'; self.assertGreater(len(raw), G.MIB)
        name = self.r.policy['bounded_index']['path']; self.r.put(name, raw); self.r.add(name)
        self.assertEqual(self.result()['bounded_indexes'], [name])

    def test_index_embedded_payload_duplicate_nonfinite_and_count_refuse(self):
        row = self.index_row('a'); spec = self.r.policy['bounded_index']
        for rows in ([dict(row, payload='hidden')], [row, row], [dict(row, bytes=True)]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                G.validate_index(b'\n'.join(json.dumps(r).encode() for r in rows), spec)
        with self.assertRaises(ValueError): G.validate_index(b'{"x":NaN}', spec)
        tiny = dict(spec, max_rows=1)
        with self.assertRaises(ValueError):
            G.validate_index(b'\n'.join(json.dumps(self.index_row(n)).encode() for n in ('a','b')), tiny)

    def test_commit_range_scans_removed_intermediate_payload(self):
        base = self.r.git('rev-parse', 'HEAD').decode().strip()
        p = self.r.put('route.odb', b'raw'); self.r.add('route.odb'); self.r.commit()
        p.unlink(); self.r.commit()
        self.assertEqual(self.result()['status'], 'passed')
        result = G.check(self.r.root, self.r.policy, base=base)
        self.assertEqual(result['status'], 'refused'); self.assertEqual(result['commits_checked'], 2)

    def test_rewritten_history_without_provenance_object_passes(self):
        self.assertNotEqual(self.r.git('cat-file', '-e', self.r.policy['baseline_commit'], check=False), 0)
        self.r.put('proof.lean', b'theorem fixture : True := True.intro\n'); self.r.add('proof.lean'); head = self.r.commit()
        code, result = self.r.cli('--base', self.r.origin, '--head', head)
        self.assertEqual(code, 0); self.assertGreater(result['commits_checked'], 0)

    def test_advanced_pr_base_need_not_be_ancestor_of_head(self):
        fork = self.r.git('rev-parse', 'HEAD').decode().strip()
        self.r.put('main-side.py', b'main advanced'); base = self.r.commit()
        self.r.git('checkout', '-qb', 'feature-fixture', fork)
        self.r.put('feature.py', b'source'); head = self.r.commit()
        result = G.check(self.r.root, self.r.policy, base=base, head=head)
        self.assertEqual(result['status'], 'passed'); self.assertEqual(result['comparison_merge_base'], fork)
        self.assertEqual(result['commits_checked'], 1)

    def test_base_merge_excludes_only_exact_selected_base_versions(self):
        fork = self.r.git('rev-parse', 'HEAD').decode().strip()
        raw = b'base-only historical payload'
        self.r.put('base-route.odb', raw); base = self.r.commit()
        self.r.git('checkout', '-qb', 'feature-fixture', fork)
        self.r.put('feature.py', b'source'); self.r.commit()
        self.r.git('merge', '-q', '--no-ff', base, '-m', 'merge base fixture')
        result = G.check(self.r.root, self.r.policy, base=base)
        self.assertEqual(result['status'], 'passed'); self.assertEqual(result['changed_files'], 1)
        self.r.put('base-route.odb', b'new feature payload'); self.r.commit()
        self.r.put('base-route.odb', raw); self.r.commit()
        result = G.check(self.r.root, self.r.policy, base=base)
        self.assertEqual(result['status'], 'refused')
        self.assertIn('base-route.odb', ' '.join(result['errors']))

    def test_missing_local_range_object_refuses_without_fetch(self):
        code, result = self.r.cli('--base', 'a'*40)
        self.assertEqual(code, 1); self.assertEqual(result['status'], 'refused')

    def test_bootstrap_requires_digest_and_cannot_override_selected_policy(self):
        r = Repository(policy=False); self.addCleanup(r.close)
        p = r.put(G.POLICY, (json.dumps(r.policy)+'\n').encode()); digest = hashlib.sha256(p.read_bytes()).hexdigest()
        code, _ = r.cli('--bootstrap-policy', str(p), '--bootstrap-policy-sha256', '0'*64); self.assertEqual(code, 1)
        code, result = r.cli('--bootstrap-policy', str(p), '--bootstrap-policy-sha256', digest)
        self.assertEqual(code, 0); self.assertEqual(result['policy_origin'], 'explicit-bootstrap-file')
        code, _ = self.r.cli('--bootstrap-policy', str(p), '--bootstrap-policy-sha256', digest); self.assertEqual(code, 1)


if __name__ == '__main__':
    unittest.main()
