"""Refusal tests for mapped immutable evidence, without invoking a gate/tool."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import types
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))


def load(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


E = load('_mapped_evidence_tests', 'scripts/export-streaming-mapped-evidence.py')
U = load('_mapped_shared_tests', 'scripts/export-streaming-uart-evidence.py')
M = load('_mapped_master_tests', 'scripts/check-streaming-mapped.py')
import streaming_mapped_campaign as C

COMMIT = 'a' * 40
FOUNDATION = """SUITES = [('Binary', [])]
KERNEL_SUITES = ['Base']
def main():
    return dict(boundary='Existing proof. Does not run physical tools.')
"""


def full():
    return dict(schema=E.FULL_SCHEMA, passed=True, full_qualification=True, source_commit=COMMIT,
        producer_commit=COMMIT, committed_archive_membership_verified_before=True,
        committed_archive_membership_verified_after=True, tool_identity_unchanged=True,
        library_unchanged=True, tool_identity_before={'files': {'native': 'hash'}},
        tool_identity_after={'files': {'native': 'hash'}}, library={'sha256': E.LIBRARY},
        cad_runtime_archive_membership=dict(cad_selected_archive_membership_verified=True,
            installed_payload_archive_membership_proved=False),
        raw_stage={'partial_input_only': True})


class EvidenceTests(unittest.TestCase):
    def test_sealed_uart_checkpoint_and_original_evidence_bytes_are_pinned(self):
        self.assertEqual(E.BASE, '3dfbc7cbe7f6d0ca64dd7b8b5392f4fa1c02cde2')
        for name, expected in {
                'docs/research/evidence/streaming-uart-continuation-20261017/manifest.json':
                    '05fa1723258debeb1aad53e135d4a8774bfc1d62fad7c002b5a910d193d617c9',
                'Pinwheel/Program/StreamingUART.lean':
                    'f2090c8f4f3431eebe2fe2ce3b2eb452b5ff928e84ac9cf49d689b3ace0dd3fd'}.items():
            with self.subTest(name=name): self.assertEqual(E.digest(ROOT / name), expected)

    def test_exact_three_accepted_same_source_and_producer_receipts(self):
        good = {kind: dict(passed=True, source_commit=COMMIT, producer_commit=COMMIT)
            for kind in ('full', 'foundation', 'python')}
        self.assertEqual(E.same_source(good), COMMIT)
        for kind, field, value in [('full', 'passed', False), ('python', 'source_commit', 'b' * 40),
                ('full', 'producer_commit', 'b' * 40), ('foundation', 'source_commit', 'HEAD'),
                ('foundation', 'source_commit', [])]:
            bad = copy.deepcopy(good); bad[kind][field] = value
            with self.subTest(kind=kind, field=field), self.assertRaises(RuntimeError): E.same_source(bad)
        del good['foundation']
        with self.assertRaises(RuntimeError): E.same_source(good)

    def test_duplicate_receipt_fields_refuse_before_contract_validation(self):
        self.assertEqual(E.read_json('{"a":{"b":1}}'), {'a': {'b': 1}})
        for data in ('{"passed":true,"passed":false}', '{"a":{"x":1,"x":1}}'):
            with self.assertRaises(RuntimeError): E.read_json(data)

    def test_frozen_uart_ready_sources_reports_evidence_cannot_change(self):
        base = {'Pinwheel.lean': b'import Pinwheel.Old\n', 'scripts/check-foundation.py': FOUNDATION.encode(),
            'Pinwheel/Program/StreamingUART.lean': b'qualified UART source',
            'docs/research/evidence/streaming-uart-continuation-20261017/manifest.json': b'sealed UART receipt',
            'docs/research/streaming-uart-morning-report.md': b'qualified report'}
        current = dict(base)
        current['Pinwheel.lean'] += b'import Pinwheel.Hardware.StreamingMapped.Word\n'
        current['scripts/check-foundation.py'] = FOUNDATION.replace('Existing proof. Does not',
            'Existing proof; mapped streaming digital proof. Does not').encode()
        result = E.preserve_base(U, base, current, COMMIT)
        self.assertEqual(result['base'], COMMIT)
        self.assertEqual(result['foundation']['added_kernel_suites'], [])
        separate = FOUNDATION.replace('Existing proof. Does not',
            'Existing proof. Includes mapped infrastructure and first-terminal source timing. Does not')
        self.assertTrue(E.mapped_foundation(U, FOUNDATION, separate)['boundary_preserved'])
        for name in base:
            if name in ('Pinwheel.lean', 'scripts/check-foundation.py'): continue
            bad = dict(current); bad[name] += b'\nchanged'
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'Sealed baseline file changed'):
                E.preserve_base(U, base, bad, COMMIT)
            del bad[name]
            with self.assertRaises(RuntimeError): E.preserve_base(U, base, bad, COMMIT)

    def test_only_mapped_imports_and_boundary_append_no_new_or_reordered_suites(self):
        base = {'Pinwheel.lean': b'import Pinwheel.Old\n', 'scripts/check-foundation.py': FOUNDATION.encode()}
        candidates = []
        value = dict(base); value['Pinwheel.lean'] += b'import Pinwheel.Program.StreamingOther\n'; candidates.append(value)
        value = dict(base); value['scripts/check-foundation.py'] = FOUNDATION.replace("['Base']", "['Base', 'StreamingNew']").encode(); candidates.append(value)
        value = dict(base); value['scripts/check-foundation.py'] = FOUNDATION.replace("[('Binary', [])]", "[('Binary', []), ('StreamingNew', [])]").encode(); candidates.append(value)
        value = dict(base); value['scripts/check-foundation.py'] = (FOUNDATION + '\nprint("extra action")\n').encode(); candidates.append(value)
        for value in candidates:
            with self.assertRaises(RuntimeError): E.preserve_base(U, base, value, COMMIT)
        with self.assertRaises(RuntimeError): E.preserve_base(U, base, base, 'HEAD')

    def test_full_contract_refuses_partial_stale_tool_library_and_unclosed_receipts(self):
        E.full_contract(full())
        changes = [(key, False) for key in ('passed', 'full_qualification',
            'committed_archive_membership_verified_before', 'committed_archive_membership_verified_after',
            'tool_identity_unchanged', 'library_unchanged')]
        changes += [('schema', 'pinwheel.streaming-uart-continuation.v1'), ('error', 'interrupted'),
            ('closeout_error', 'changed'), ('tool_identity_after', {'different': True}),
            ('library', {'sha256': '0' * 64}), ('raw_stage', {'partial_input_only': False}),
            ('cad_runtime_archive_membership', {'cad_selected_archive_membership_verified': False}),
            ('cad_runtime_archive_membership', {'cad_selected_archive_membership_verified': True,
                'installed_payload_archive_membership_proved': True})]
        for key, value in changes:
            bad = full(); bad[key] = value
            with self.subTest(key=key), self.assertRaises(RuntimeError): E.full_contract(bad)

    def test_historical_raw_snapshot_and_worker_paths_cannot_seed_a_fresh_tag(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = (Path(temporary) / 'fresh-full').resolve()
            config = dict(worker_out=str(directory / 'worker'), snapshot=str(directory.parent / 'fresh-full-raw/selected'))
            raw = dict(report=str(directory.parent / 'fresh-full-raw/report.json'), partial_input_only=True)
            self.assertEqual(E.fresh_layout(directory, config, raw)[1].name, 'fresh-full-raw')
            for mode in ('worker', 'snapshot', 'report', 'full-claim'):
                candidate, stage = dict(config), dict(raw)
                if mode == 'worker': candidate['worker_out'] = str(directory.parent / 'historical/worker')
                elif mode == 'snapshot': candidate['snapshot'] = str(directory.parent / 'historical-raw/selected')
                elif mode == 'report': stage['report'] = str(directory.parent / 'historical-raw/report.json')
                else: stage['partial_input_only'] = False
                with self.subTest(mode=mode), self.assertRaises(RuntimeError): E.fresh_layout(directory, candidate, stage)

    def test_actual_native_runtime_archives_and_resolved_paths_are_rechecked(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); binary = root / 'native'; archive = root / 'archive'
            binary.write_bytes(b'actual native'); archive.write_bytes(b'actual archive')
            identity = dict(installed_payload_archive_membership_proved=False,
                files={str(binary): dict(sha256=E.digest(binary), resolved=str(binary.resolve()))},
                archives={str(archive): E.digest(archive)})
            frozen = {}; self.assertEqual(E.checked_tool_files(identity, frozen), 1)
            self.assertEqual(set(frozen), {binary.resolve(), archive})
            alias = root / 'native-alias'; alias.symlink_to(binary)
            aliases = copy.deepcopy(identity)
            aliases['files'][str(alias)] = dict(sha256=E.digest(binary), resolved=str(binary.resolve()))
            self.assertEqual(E.checked_tool_files(aliases, {}), 2)
            alias.unlink(); alias.symlink_to(archive)
            with self.assertRaises(RuntimeError): E.checked_tool_files(aliases, {})
            for field in ('resolved', 'sha256'):
                bad = copy.deepcopy(identity); bad['files'][str(binary)][field] = 'changed'
                with self.assertRaises(RuntimeError): E.checked_tool_files(bad, {})
            archive.write_bytes(b'changed archive')
            with self.assertRaises(RuntimeError): E.checked_tool_files(identity, {})
            archive.write_bytes(b'actual archive'); binary.write_bytes(b'changed native')
            with self.assertRaises(RuntimeError): E.checked_tool_files(identity, {})
            identity['installed_payload_archive_membership_proved'] = True
            with self.assertRaises(RuntimeError): E.checked_tool_files(identity, {})

    def test_campaign_intents_require_real_exit_status_matching_parent_journal_and_logs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); (root / 'logs').mkdir()
            (root / 'logs/checked.log').write_text('native checked')
            command = dict(label='checked', argv=['/native/lean', 'Proof.lean'], exit_code=0, expected_failure=False)
            intent = dict(index=0, label='checked', argv=command['argv'])
            (root / 'command-intents.jsonl').write_text(json.dumps(intent) + '\n')
            report = dict(commands=[command], campaign=dict(commands=[dict(label='checked', argv=command['argv'],
                expected_failure=False, external_runner=True, expected_outcome_completed=True)]))
            self.assertIn('checked', E.native_commands(U, M, report, root))
            for mode in ('argv', 'exit', 'missing', 'intent', 'log'):
                bad = copy.deepcopy(report)
                if mode == 'argv': bad['campaign']['commands'][0]['argv'] = ['/different/lean']
                elif mode == 'exit': bad['commands'][0]['exit_code'] = None
                elif mode == 'missing': bad['campaign']['commands'][0]['expected_outcome_completed'] = False
                elif mode == 'intent': (root / 'command-intents.jsonl').write_text(json.dumps(dict(intent, argv=['wrong'])) + '\n')
                else: (root / 'logs/checked.log').unlink()
                with self.subTest(mode=mode), self.assertRaises(RuntimeError): E.native_commands(U, M, bad, root)
                (root / 'command-intents.jsonl').write_text(json.dumps(intent) + '\n')

    def test_actual_engine_cut_json_roundtrip_preserves_every_endpoint(self):
        from streaming_mapped_wrapper import ENGINE, PADS, cut_engine
        ports, cursor = {}, 2
        for name, (direction, width) in PADS.items():
            ports[name] = dict(direction=direction, bits=list(range(cursor, cursor + width)))
            cursor += width
        connections = {}
        for name, (_, width) in ENGINE.items():
            connections[name] = ports['clk']['bits'] if name == 'clk' else list(range(cursor, cursor + width))
            cursor += width
        actual = dict(modules={'actualTop': dict(ports=ports, cells={'actualEngine': dict(type='actualPackage',
            parameters={}, port_directions={name: direction for name, (direction, _) in ENGINE.items()},
            connections=connections)})})
        cut, boundary = cut_engine(actual, 'actualTop', 'actualPackage')
        retained_cut = json.loads(json.dumps(cut))
        retained_boundary = json.loads(json.dumps(boundary))
        self.assertNotEqual(boundary, retained_boundary)
        E.check_cut_boundary(cut, boundary, retained_cut, retained_boundary)
        for mode in ('width', 'direction', 'missing-endpoint', 'clock', 'instance', 'cut-wire', 'primitive-type', 'cut-primitive-type'):
            changed_cut, changed_boundary = copy.deepcopy(retained_cut), copy.deepcopy(retained_boundary)
            if mode == 'width': changed_boundary['expected_cut']['ui_in'][1] += 1
            elif mode == 'direction': changed_boundary['expected_cut']['ui_in'][0] = 'output'
            elif mode == 'missing-endpoint': del changed_boundary['expected_cut']['engine_boundary_mosi']
            elif mode == 'clock': changed_boundary['clock']['bits'][0] += 1
            elif mode == 'instance': changed_boundary['instance'] = 'otherEngine'
            elif mode == 'cut-wire': changed_cut['modules']['actualTop']['ports']['engine_boundary_raw_inputs']['bits'][0] += 1
            elif mode == 'cut-primitive-type': changed_cut['modules']['actualTop']['ports']['engine_boundary_raw_inputs']['bits'][0] = float(changed_cut['modules']['actualTop']['ports']['engine_boundary_raw_inputs']['bits'][0])
            else: changed_boundary['expected_cut']['ui_in'][1] = float(changed_boundary['expected_cut']['ui_in'][1])
            with self.subTest(mode=mode), self.assertRaisesRegex(RuntimeError, 'package cut differs'):
                E.check_cut_boundary(cut, boundary, changed_cut, changed_boundary)

    def test_all_positive_owners_and_private_controls_are_part_of_final_audit(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); (root / 'logs').mkdir(); proof = root / 'campaign/wrapper'; proof.mkdir(parents=True)
            owners = ['A', 'PositiveUnchanged', 'FinalRequired']
            commands = [dict(label=name, argv=['lean', '-o', name + '.olean', name + '.lean'], expected_failure=False)
                for name in owners]
            commands.insert(1, dict(label='UnsafePrivateControl', argv=['lean', '-o', 'UnsafePrivateControl.olean',
                'UnsafePrivateControl.lean'], expected_failure=False))
            commands += [dict(label='MappedWrapperAudit', argv=['lean'], expected_failure=False),
                dict(label='MappedWrapperPrivateAuditControl', argv=['lean'], expected_failure=True)]
            (proof / 'MappedWrapperAudit.lean').write_text(C.audit_source(owners))
            (proof / 'MappedWrapperPrivateAuditControl.lean').write_text(C.audit_source([*owners, 'MappedWrapperPrivateControl']))
            (root / 'logs/MappedWrapperAudit.log').write_text('Mapped audit: 100 declarations, 80 theorems; standard axioms only.\n')
            (root / 'logs/MappedWrapperPrivateAuditControl.log').write_text('Unapproved axioms in hidden')
            report = dict(commands=commands, campaign=dict(components={}))
            by_label = {row['label']: row for row in commands}
            result = E.check_audits(U, C, report, root, by_label)
            self.assertEqual(result['final_owner_modules'], 3)
            (proof / 'MappedWrapperAudit.lean').write_text(C.audit_source(['A', 'FinalRequired']))
            with self.assertRaisesRegex(RuntimeError, 'owner'): E.check_audits(U, C, report, root, by_label)
            (proof / 'MappedWrapperAudit.lean').write_text(C.audit_source(owners))
            (root / 'logs/MappedWrapperPrivateAuditControl.log').write_text('unrelated compiler failure')
            with self.assertRaises(RuntimeError): E.check_audits(U, C, report, root, by_label)

    def test_every_required_compact_source_log_cost_and_native_journal_must_exist(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); wrapper = root / 'campaign/wrapper'; wrapper.mkdir(parents=True); (root / 'logs').mkdir()
            for name in ('StreamingMappedSessionD2', 'StreamingMappedSessionD4', 'StreamingMappedPackageD2',
                    'StreamingMappedPackageD4', 'StreamingMappedTinyD2', 'StreamingMappedTinyD4',
                    'StreamingMappedUARTTimingD2', 'StreamingMappedUARTTimingD4',
                    'StreamingMappedRequiredTargets', 'MappedWrapperAudit'):
                (wrapper / (name + '.lean')).write_text('-- retained checked source\n')
            for name in ('StreamingMappedRequiredTargets', 'MappedWrapperAudit', 'MappedWrapperPrivateAuditControl'):
                (root / 'logs' / (name + '.log')).write_text('retained native output')
            for depth in (2, 4):
                directory = root / 'campaign/device' / ('d' + str(depth)); directory.mkdir(parents=True)
                for name in ('cost.json', 'native-intent.json', 'native.jsonl'): (directory / name).write_text('{}\n')
            result = E.compact_sources(U, root)
            self.assertEqual(len(result), 19)
            (root / 'campaign/device/d4/native.jsonl').unlink()
            with self.assertRaises(RuntimeError): E.compact_sources(U, root)


if __name__ == '__main__': unittest.main()
