"""Pure refusal controls for the compact streaming evidence exporter."""
import copy
import gzip
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('streaming_evidence_export', ROOT / 'scripts/export-streaming-evidence.py')
E = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(E)
COMMIT = 'a' * 40
HASH = 'b' * 64
FOUNDATION = '''SUITES = [('Binary', []), ('UARTRx', []), ('Last', ['--strict'])]
KERNEL_SUITES = ['Base']
def main():
    return dict(boundary='Original claims. Does not run physical tools.')
'''


class StreamingEvidenceTests(unittest.TestCase):
    def test_duplicate_json_keys_refused_at_any_depth(self):
        self.assertEqual(E.read_json('{"a":{"b":1}}'), {'a': {'b': 1}})
        for value in ('{"a":1,"a":2}', '{"a":{"b":1,"b":1}}'):
            with self.assertRaises(RuntimeError): E.read_json(value)

    def test_all_three_same_full_commit_receipts_required(self):
        good = {kind: dict(passed=True, source_commit=COMMIT) for kind in ('full', 'foundation', 'python')}
        self.assertEqual(E.same_source(good), COMMIT)
        for kind, change in [('full', {'passed': False}), ('python', {'source_commit': 'c' * 40}),
                ('foundation', {'source_commit': 'HEAD'}), ('full', {'source_commit': []})]:
            value = copy.deepcopy(good)
            value[kind].update(change)
            with self.assertRaises(RuntimeError): E.same_source(value)
        with self.assertRaises(RuntimeError): E.same_source({'full': good['full']})

    def test_paths_and_redirected_artifacts_refused(self):
        for name in ('/absolute', '../escape', 'a/../../b', 'bad\nname', '', None):
            with self.assertRaises(RuntimeError): E.safe_relative(name)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'a').write_bytes(b'payload')
            self.assertEqual(E.inventory(root), {'a': E.sha(b'payload')})
            (root / 'link').symlink_to(root / 'a')
            with self.assertRaises(RuntimeError): E.inventory(root)
            with self.assertRaises(RuntimeError): E.regular(root / 'link', root)

    def test_only_additive_streaming_default_imports(self):
        old = 'import Pinwheel.Old\n\nimport Pinwheel.Last\n'
        addition = 'import Pinwheel.Program.StreamingProof\n'
        self.assertEqual(E.additive_imports(old, old + addition), [addition.strip()])
        for new in (old.replace('Old', 'Changed'), old + 'import Pinwheel.Buffered.New\n',
                old + addition * 2, 'import Pinwheel.Last\n'):
            with self.assertRaises(RuntimeError): E.additive_imports(old, new)

    def test_foundation_additions_preserve_old_suites_code_and_boundary(self):
        good = FOUNDATION.replace("('Last', ['--strict'])]", "('Last', ['--strict']), ('StreamingNew', [])]")
        good = good.replace("['Base']", "['Base', 'StreamingKernel']")
        good = good.replace('Original claims. Does not', 'Original claims; bounded streaming proof. Does not')
        result = E.additive_foundation(FOUNDATION, good)
        self.assertEqual(result['added_suites'], [('StreamingNew', [])])
        for text in (good.replace("'StreamingNew'", "'Unrelated'"),
                good.replace("('Binary', []), ", ''), good.replace('Does not run physical tools.', 'Runs physical tools.'),
                good + '\nprint("changed gate behavior")\n', good.replace('Original claims;', 'Weaker claims;')):
            with self.assertRaises(RuntimeError): E.additive_foundation(FOUNDATION, text)

    def test_frozen_baseline_deleted_or_modified_file_refused(self):
        base = {'Pinwheel.lean': b'import Pinwheel.Old\n',
            'scripts/check-foundation.py': FOUNDATION.encode(), 'existing.txt': b'fixed'}
        current = dict(base)
        self.assertEqual(E.preserve_base(base, current)['baseline_files'], 3)
        current['existing.txt'] = b'changed'
        with self.assertRaises(RuntimeError): E.preserve_base(base, current)
        current.pop('existing.txt')
        with self.assertRaises(RuntimeError): E.preserve_base(base, current)

    def test_exact_foundation_labels_order_and_expected_failure(self):
        expected = [('version', False), ('build', False), ('axioms', False), ('reject-untrusted-axiom', True),
            ('Base-kernel', False), ('Binary', False), ('independent-binary', False), ('UARTRx', False),
            ('independent-uart-rx', False), ('Last-strict', False)]
        self.assertEqual(E.foundation_labels(FOUNDATION), expected)
        good = dict(commands=[dict(label=name, exit_code=1 if rejected else 0) for name, rejected in expected])
        self.assertEqual(E.check_foundation(good, FOUNDATION), len(expected))
        for index, code in ((3, 0), (1, 2), (0, False)):
            bad = copy.deepcopy(good)
            bad['commands'][index]['exit_code'] = code
            with self.assertRaises(RuntimeError): E.check_foundation(bad, FOUNDATION)
        good['commands'] = list(reversed(good['commands']))
        with self.assertRaises(RuntimeError): E.check_foundation(good, FOUNDATION)

    def test_foundation_complete_sources_and_native_audit_verified(self):
        source = FOUNDATION + "\nsources = [ROOT / p for p in ['Pinwheel.lean', 'scripts/check-foundation.py']]\n"
        files = {'Pinwheel.lean': b'import Pinwheel.Old\n', 'scripts/check-foundation.py': source.encode(),
            'Pinwheel/Old.lean': b'-- library', 'test/Fixture.lean': b'-- test', 'unrelated.py': b'pass'}
        report = dict(modules=2, audited_declarations=100, audited_theorems=60,
            source_sha256={name: E.sha(value) for name, value in files.items() if name != 'unrelated.py'},
            commands=[dict(label=label, exit_code=1 if rejected else 0)
                for label, rejected in E.foundation_labels(source)])
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for label, rejected in E.foundation_labels(source):
                (root / (label + '.log')).write_text('Unapproved axioms in Pinwheel.CI.untrusted' if rejected else 'ok')
            (root / 'axioms.log').write_text('Pinwheel audit: 100 declarations, 60 theorems; standard axioms only.\n')
            self.assertEqual(E.foundation_evidence(report, files, root, {})['source_files'], 4)
            bad = copy.deepcopy(report)
            bad['source_sha256'].pop('test/Fixture.lean')
            with self.assertRaises(RuntimeError): E.foundation_evidence(bad, files, root, {})
            (root / 'axioms.log').write_text('Pinwheel audit: 101 declarations, 60 theorems; standard axioms only.\n')
            with self.assertRaises(RuntimeError): E.foundation_evidence(report, files, root, {})

    def test_python_inventory_and_native_summary_must_match(self):
        text = ('test_a (fixture.Tests.test_a) ... ok\n'
            'test_skip (fixture.Tests.test_skip) ... skipped \'tool unavailable\'\n'
            '\nRan 2 tests in 0.010s\n\nOK (skipped=1)\n')
        report = dict(unittest=dict(tests_run=2, skipped=1,
            skips=[dict(test='test_skip (fixture.Tests.test_skip)', reason="'tool unavailable'")],
            summary='Ran 2 tests in 0.010s\n\nOK (skipped=1)'))
        files = {'scripts/check-python-snapshot.py': (ROOT / 'scripts/check-python-snapshot.py').read_bytes()}
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'logs').mkdir()
            (root / 'logs/python-unittest-discover.log').write_text(text)
            report['artifact_sha256'] = E.inventory(root)
            self.assertTrue(E.check_python_retained(report, root, {}, files)['native_summary_verified'])
            bad = copy.deepcopy(report)
            bad['unittest']['tests_run'] = 3
            with self.assertRaises(RuntimeError): E.check_python_retained(bad, root, {}, files)
            (root / 'extra').write_bytes(b'unrecorded artifact')
            with self.assertRaises(RuntimeError): E.check_python_retained(report, root, {}, files)

    def test_input_freeze_union_changed_and_missing_bytes_refused(self):
        expected = {'a': HASH, 'b': 'c' * 64}
        self.assertEqual(E.freeze_journal([{}, {'a': HASH}, expected], expected, expected), 2)
        for journal, actual in (([{'a': HASH}, {'a': 'd' * 64}], expected),
                ([{'a': HASH}], expected), ([expected], {'a': HASH}), ([{'../bad': HASH}], expected)):
            with self.assertRaises(RuntimeError): E.freeze_journal(journal, expected, actual)

    def test_native_command_intent_and_failure_reason_required(self):
        intents = [dict(index=0, label='positive', argv=['lean', 'P'], options={}),
            dict(index=1, label='negative', argv=['lean', 'N'], options={'reject': 'Unapproved axioms'})]
        commands = [dict(label='positive', argv=['lean', 'P'], exit_code=0, expected_failure=False),
            dict(label='negative', argv=['lean', 'N'], exit_code=1, expected_failure=True)]
        E.check_journal(intents, commands, lambda label: 'Unapproved axioms in private')
        for field, value in (('argv', ['different']), ('exit_code', 0), ('expected_failure', False), ('error', 'Timeout')):
            bad = copy.deepcopy(commands)
            bad[1][field] = value
            with self.assertRaises(RuntimeError): E.check_journal(intents, bad, lambda label: 'Unapproved axioms')
        with self.assertRaises(RuntimeError): E.check_journal(intents, commands, lambda label: 'unrelated syntax error')
        intents[1]['index'] = True
        with self.assertRaises(RuntimeError): E.check_journal(intents, commands, lambda label: 'Unapproved axioms')

    def test_git_blob_membership_cache_still_checks_reported_inventory(self):
        calls = []
        E.source_objects.cached = {}
        def run(argv, label):
            calls.append((argv, label))
            return '100644 blob ' + '1' * 40 + '\ta\0' + '100755 blob ' + '2' * 40 + '\tb\0'
        self.assertEqual(E.source_objects(run, COMMIT, {'a': HASH}), {'a': '1' * 40})
        self.assertEqual(E.source_objects(run, COMMIT, {'b': HASH}), {'b': '2' * 40})
        self.assertEqual(len(calls), 1)
        with self.assertRaises(RuntimeError): E.source_objects(run, COMMIT, {'a': HASH}, {'a': '3' * 40})
        with self.assertRaises(RuntimeError): E.source_objects(run, COMMIT, {'missing': HASH})

    def test_raw_wire_and_cost_are_actual_byte_bindings(self):
        artifacts, wire, binding = {}, {}, {}
        for depth in (2, 4):
            paths = [f'raw/core-d{depth}/core.sv', 'raw/frontend/frontend.sv',
                f'actual-wrappers/d{depth}/package.sv', f'actual-wrappers/d{depth}/tt.sv',
                f'actual-wrappers/d{depth}/bridge.sv']
            for path in paths: artifacts[path] = E.sha(path.encode())
            wire[str(depth)] = {path: artifacts[path] for path in paths}
            names = dict(zip(('core.sv', 'frontend.sv', 'package.sv', 'tt.sv'), paths[:4]))
            for name in ('core.mlir', 'frontend.mlir'):
                path = f'emitted/d{depth}/' + name
                artifacts[path] = E.sha(path.encode())
                names[name] = path
            for name, path in names.items():
                target = f'cost/emitted/d{depth}/' + name
                artifacts[target] = binding[target] = artifacts[path]
        raw = {name: dict(proof_input_sha256_before={stem + '.sv': artifacts['raw/' + name + '/' + stem + '.sv']})
            for name, stem in [('frontend', 'frontend'), ('core-d2', 'core'), ('core-d4', 'core')]}
        worker = dict(stages={'public-wire': dict(result=dict(source_binding=wire)),
            'matched-cost': dict(result=dict(raw_certified_input_binding=binding)), 'raw-components': dict(result=raw)})
        self.assertEqual(E.actual_bindings(worker, artifacts, ROOT)['raw_cost_equalities'], 12)
        for path in ('cost/emitted/d2/core.sv', 'raw/core-d4/core.sv'):
            bad = dict(artifacts)
            bad[path] = '0' * 64
            with self.assertRaises(RuntimeError): E.actual_bindings(worker, bad, ROOT)

    def test_complete_closeout_and_matched_library_required(self):
        good = dict(schema='pinwheel.streaming-continuation.v1', stage='full', full_qualification=True,
            committed_archive_membership_verified_before=True, committed_archive_membership_verified_after=True,
            tool_identity_unchanged=True, library_unchanged=True, tool_identity_before={'files': {'tool': HASH}},
            tool_identity_after={'files': {'tool': HASH}}, library_identity_before={
                'sha256': '34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad'})
        good['library_identity_after'] = dict(good['library_identity_before'])
        E.full_contract(good)
        for field, value in (('stage', 'components'), ('library_unchanged', False),
                ('tool_identity_after', {}), ('error', 'failed'), ('committed_archive_membership_verified_after', False)):
            bad = dict(good, **{field: value})
            with self.assertRaises(RuntimeError): E.full_contract(bad)

    def test_custody_and_progress_targets_cannot_fall_back_to_old_fourteen(self):
        E.check_join_apis(E.MIN_JOIN_APIS)
        E.check_join_apis([*E.MIN_JOIN_APIS, 'additional_checked_target'])
        for names in (E.MIN_JOIN_APIS[:14], E.MIN_JOIN_APIS[:-1],
                [*E.MIN_JOIN_APIS, E.MIN_JOIN_APIS[0]]):
            with self.assertRaises(RuntimeError): E.check_join_apis(names)

    def test_existing_export_destination_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            destination = root / E.DESTINATION
            destination.mkdir(parents=True)
            sentinel = destination / 'manifest.json'
            sentinel.write_bytes(b'original immutable manifest')
            arguments = ['exporter', '--tag', 'export', '--full-tag', 'full', '--foundation-tag', 'foundation',
                '--python-tag', 'python']
            with patch.object(E, 'ROOT', root), patch('sys.argv', arguments):
                with self.assertRaisesRegex(RuntimeError, 'destination must be fresh'): E.main()
            self.assertEqual(sentinel.read_bytes(), b'original immutable manifest')
            self.assertFalse((root / 'build').exists())

    def test_retained_archive_and_input_cannot_be_substituted(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            file = root / 'a'
            file.write_bytes(b'initial')
            frozen = {}
            E.checked_map(root, {'a': E.sha(b'initial')}, frozen)
            E.retained_archive(root, 'a', E.sha(b'initial'), frozen)
            self.assertEqual(frozen[file], E.sha(b'initial'))
            file.write_bytes(b'altered')
            with self.assertRaises(RuntimeError): E.checked_map(root, {'a': E.sha(b'initial')}, {})
            with self.assertRaises(RuntimeError): E.retained_archive(root, 'a', E.sha(b'initial'), {})
            with self.assertRaises(RuntimeError): E.checked_path('/outside', (root,), {}, HASH)

    def test_deterministic_receipt_roundtrip_does_not_change_source(self):
        raw = (json.dumps(dict(passed=True, values=list(range(100)))) + '\n').encode()
        first, second = E.deterministic_gzip(raw), E.deterministic_gzip(raw)
        self.assertEqual(first, second)
        self.assertEqual(first[4:8], b'\0\0\0\0')
        self.assertEqual(gzip.decompress(first), raw)
        with self.assertRaises((OSError, EOFError)): gzip.decompress(first[:-4])


if __name__ == '__main__': unittest.main()
