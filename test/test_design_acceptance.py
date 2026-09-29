"""Refusal controls for the implementation evidence joins and acceptance report."""
from copy import deepcopy
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from design_acceptance import (Evidence, POLICY, REQUIREMENTS, ROOT_ROLES,
    bind_certificate, certificate_bytes, decision, liberty_conditions,
    parse_json, passed_receipt, protected_repair, same_signal, check_readback_scope)


class AcceptanceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.evidence = Evidence(self.root)

    def file(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        data = value if isinstance(value, bytes) else json.dumps(value).encode()
        path.write_bytes(data)
        return dict(path=name, sha256=hashlib.sha256(data).hexdigest())

    def test_missing_or_changed_artifact_refuses(self):
        entry = self.file('artifact', b'original')
        (self.root / 'artifact').write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'Changed evidence'):
            self.evidence.load(entry)
        (self.root / 'artifact').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing or unreadable evidence'):
            self.evidence.load(entry)

    def test_conflicting_bindings_refuse(self):
        entry = self.file('artifact', {})
        self.evidence.load(entry)
        with self.assertRaisesRegex(ValueError, 'Conflicting document identity'):
            self.evidence.load(dict(entry, sha256='0' * 64))

    def test_parsed_snapshot_cannot_hide_late_edit(self):
        entry = self.file('artifact', {'value': 1})
        self.assertEqual(self.evidence.load(entry), {'value': 1})
        self.file('artifact', {'value': 2})
        with self.assertRaisesRegex(ValueError, 'changed during assessment'):
            self.evidence.close()

    def test_equal_named_artifacts_from_different_candidates_refuse(self):
        a = self.file('a/report.json', {'value': 1})
        b = self.file('b/report.json', {'value': 2})
        with self.assertRaisesRegex(ValueError, 'Disconnected evidence'):
            self.evidence.same('candidate identity', a, b)

    def test_receipt_must_consume_selected_input(self):
        a = self.file('a', b'a')
        b = self.file('b', b'b')
        report = {'inputs_sha256': {a['path']: a['sha256']}}
        with self.assertRaisesRegex(ValueError, 'does not consume selected artifact'):
            self.evidence.consumed('source', {}, report, b)

    def test_duplicate_or_nonfinite_json_refuses(self):
        for data in (b'{"A_accepted":false,"A_accepted":true}', b'{"slack":NaN}', b'{"slack":Infinity}'):
            with self.subTest(data=data), self.assertRaises(ValueError):
                parse_json(data)

    def test_success_label_is_insufficient(self):
        base = {'status': 'passed', 'inputs_unchanged': True,
                'commands': [{'label': 'proof', 'exit_code': 0}]}
        passed_receipt(base)
        for change in ({'commands': []}, {'inputs_unchanged': False},
                       {'commands': [{'label': 'proof', 'exit_code': None}]},
                       {'commands': [{'label': 'negative', 'expected_failure': True, 'exit_code': 0}]}):
            with self.subTest(change=change), self.assertRaises(ValueError):
                passed_receipt(dict(base, **change))

    def test_missing_or_duplicate_requirement_refuses(self):
        rows = [dict(id=k, verdict='blocked') for k in sorted(REQUIREMENTS)]
        self.assertFalse(decision(rows)['A_accepted'])
        for broken in (rows[:-1], rows + rows[:1], [dict(r, verdict='unknown') for r in rows]):
            with self.subTest(broken=broken), self.assertRaises(ValueError):
                decision(broken)

    def test_passing_screens_do_not_override_qualification(self):
        blockers = {'sram_qualification', 'timing_conditions', 'typed_circuit_to_rtl', 'package_power'}
        rows = [dict(id=k, verdict='blocked' if k in blockers else 'passed', A_accepted=True)
                for k in sorted(REQUIREMENTS)]
        result = decision(rows)
        self.assertFalse(result['A_accepted'])
        self.assertEqual(set(result['blockers']), blockers)
        self.assertFalse(result['complete_design_iteration'])

    def readback_report(self):
        report = dict(schema=1, status='passed', inputs_unchanged=True, commands=[], modules={},
            session_theorem='Pinwheel.Artifact.Paired.Package.rtl_initialized_session')
        def command(label, negative=False):
            report['commands'].append(dict(label=label, exit_code=1 if negative else 0,
                                           expected_failure=negative))
        for name in ('build', 'guards', 'guards-optimized', 'emit', 'hint-labels', 'chip.Session'):
            command(name)
        for kind, namespace, counts, defects in [
            ('core', 'Core', (81, 1469, 37, 157), ('upload-cursor', 'parameter-bank', 'sram-write')),
            ('chip', 'Package', (110, 1592, 7, 99), ('sampler', 'mailbox-valid', 'package-output'))]:
            report['modules'][kind] = dict(zip(('registers', 'register_bits', 'outputs', 'output_bits'), counts),
                audit={'standard_axioms_only': True}, shared_equations=45, local_equalities=1,
                component_theorem='Pinwheel.Artifact.Paired.' + namespace + '.component_correct',
                mutation_controls=['unchanged', *defects])
            for name in ('import', 'Design', 'Hints', 'Graphs', 'HintEquations', 'Equations',
                         'Sources', 'LocalProofs', 'Links', 'Model', 'Endpoints', 'Proof', 'Audit', 'RejectAxiom'):
                command(kind + '.' + name, name == 'RejectAxiom')
            for defect in ['unchanged', *defects]:
                for name in ('import', 'MutantGraphs', 'MutantModel', 'Reject'):
                    command(kind + '.mutations.' + defect + '.' + name,
                            name == 'Reject' and defect != 'unchanged')
        return report

    def test_interpretation_requires_both_total_interfaces_and_standard_axioms(self):
        report = self.readback_report()
        check_readback_scope(report)
        for kind in ('core', 'chip'):
            for field, value in [('registers', 1), ('outputs', 1), ('register_bits', 1),
                                 ('output_bits', 1), ('shared_equations', 44), ('local_equalities', 0),
                                 ('component_theorem', 'another_theorem'), ('mutation_controls', [])]:
                with self.subTest(kind=kind, field=field):
                    bad = deepcopy(report)
                    bad['modules'][kind][field] = value
                    with self.assertRaises(ValueError): check_readback_scope(bad)
            bad = deepcopy(report)
            bad['modules'][kind]['audit']['standard_axioms_only'] = False
            with self.assertRaises(ValueError): check_readback_scope(bad)
        bad = deepcopy(report)
        del bad['modules']['chip']
        with self.assertRaises(ValueError): check_readback_scope(bad)
        bad = deepcopy(report)
        bad['session_theorem'] = 'unconnected'
        with self.assertRaises(ValueError): check_readback_scope(bad)

    def test_interpretation_cannot_omit_or_relabel_a_fault_check(self):
        report = self.readback_report()
        for label in ('chip.Session', 'core.Audit', 'chip.RejectAxiom',
                      'chip.mutations.sampler.Reject', 'core.mutations.unchanged.Reject'):
            bad = deepcopy(report)
            bad['commands'] = [c for c in bad['commands'] if c['label'] != label]
            with self.subTest(label=label), self.assertRaises(ValueError):
                check_readback_scope(bad)
        bad = deepcopy(report)
        for c in bad['commands']:
            if c['label'] == 'chip.mutations.sampler.Reject':
                c.update(expected_failure=False, exit_code=0)
        with self.assertRaises(ValueError): check_readback_scope(bad)

    def test_rtl_proof_does_not_waive_physical_qualification(self):
        physical = {'sram_qualification', 'timing_conditions', 'package_power'}
        rows = [dict(id=k, verdict='blocked' if k in physical else 'passed') for k in REQUIREMENTS]
        result = decision(rows)
        self.assertEqual(set(result['blockers']), physical)
        self.assertFalse(result['A_accepted'])
        self.assertFalse(result['B_admitted'])

    def program(self):
        return json.dumps(dict(format='pinwheel-paired32-v1', words=[4], last=0,
                               idle_levels=0, idle_enabled=0)).encode()

    def test_certificate_binds_program_metadata_and_upload(self):
        original = self.program()
        certificate, words = certificate_bytes('fixture', original)
        self.assertEqual(len(words), 290)
        self.assertEqual(bind_certificate('fixture', original, certificate), words)
        changed = json.loads(original)
        changed['idle_levels'] = 1
        with self.assertRaisesRegex(ValueError, 'certificate disagree'):
            bind_certificate('fixture', json.dumps(changed).encode(), certificate)
        with self.assertRaisesRegex(ValueError, 'certificate disagree'):
            bind_certificate('fixture', original, certificate.replace(b'def uploaded', b'def different'))

    def test_legacy_format_cannot_enter_paired_proof(self):
        changed = json.loads(self.program())
        changed['format'] = 'pinwheel-e64-v1'
        with self.assertRaisesRegex(ValueError, 'wrong image format'):
            certificate_bytes('fixture', json.dumps(changed).encode())

    def circuit(self):
        return {'modules': {'tt_um_pinwheel': {'ports': {
            'clk': {'direction': 'input', 'bits': [1]}, 'data': {'direction': 'input', 'bits': [2]},
            'out': {'direction': 'output', 'bits': [3]}}, 'cells': {
            'state': {'type': 'ff', 'connections': {'CLK': [1], 'D': [2], 'Q': [3]},
                      'port_directions': {'CLK': 'input', 'D': 'input', 'Q': 'output'}}}},
            'sg13cmos5l_fill_1': {'ports': {}}}}

    def test_only_signal_free_finishing_cells_may_disappear(self):
        before = self.circuit()
        after = deepcopy(before)
        after['modules']['tt_um_pinwheel']['cells']['fill'] = {
            'type': 'sg13cmos5l_fill_1', 'connections': {}, 'port_directions': {}}
        a, b = self.file('before.json', before), self.file('after.json', after)
        same_signal(self.evidence, 'finishing', a, b)
        after['modules']['tt_um_pinwheel']['cells']['fill']['connections'] = {'A': [1]}
        c = self.file('wrong.json', after)
        with self.assertRaisesRegex(ValueError, 'signal terminal'):
            same_signal(self.evidence, 'finishing', a, c)

    def test_clock_change_and_hidden_state_survive_normalization(self):
        before = self.circuit()
        a = self.file('before.json', before)
        clock = deepcopy(before)
        clock['modules']['tt_um_pinwheel']['cells']['state']['connections']['CLK'] = [2]
        hidden = deepcopy(before)
        hidden['modules']['tt_um_pinwheel']['cells']['hidden'] = deepcopy(
            hidden['modules']['tt_um_pinwheel']['cells']['state'])
        for name, changed in [('clock', clock), ('hidden', hidden)]:
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'Signal circuit mismatch'):
                same_signal(self.evidence, name, a, self.file(name + '.json', changed))

    def test_declared_protection_requires_the_exact_receiver(self):
        before = self.circuit()['modules']['tt_um_pinwheel']
        after = deepcopy(before)
        after['cells']['buffer'] = {'type': 'sg13cmos5l_buf_4',
            'connections': {'A': [2], 'X': [4]}, 'port_directions': {'A': 'input', 'X': 'output'}}
        after['cells']['state']['connections']['D'] = [4]
        after['cells']['diode'] = {'type': 'sg13cmos5l_antennanp',
            'connections': {'A': [4]}, 'port_directions': {'A': 'input'}}
        protection = dict(instance='diode', cell='sg13cmos5l_antennanp', pin='A', protected_receiver='state/D')
        master = {'ports': {'A': {'direction': 'input', 'bits': [1]}}}
        self.assertTrue(protected_repair(before, after, protection, master)['buffer_contracted_connectivity'])
        changed = deepcopy(after)
        changed['cells']['diode']['connections']['A'] = [1]
        with self.assertRaisesRegex(ValueError, 'separated from its declared receiver'):
            protected_repair(before, changed, protection, master)
        changed = deepcopy(after)
        changed['cells']['another_diode'] = deepcopy(changed['cells']['diode'])
        with self.assertRaisesRegex(ValueError, 'only pinned buffer changes'):
            protected_repair(before, changed, protection, master)
        master['ports']['A']['direction'] = 'output'
        with self.assertRaisesRegex(ValueError, 'not input-only'):
            protected_repair(before, after, protection, master)

    def test_operating_conditions_are_read_from_liberty(self):
        text = b'''library(test) { nom_process : 1; nom_voltage : 1.32; nom_temperature : -55;
        default_operating_conditions : fast; operating_conditions(fast) {
        process : 1; voltage : 1.32; temperature : -55; } }'''
        self.assertEqual(liberty_conditions(text), dict(process=1., voltage=1.32, temperature=-55.))
        with self.assertRaisesRegex(ValueError, 'conditions disagree'):
            liberty_conditions(text.replace(b'temperature : -55; }', b'temperature : -40; }'))

    def test_invalid_cli_publishes_only_a_refusal_and_preserves_output(self):
        spec = importlib.util.spec_from_file_location('acceptance_cli', ROOT / 'scripts/check-design-acceptance.py')
        cli = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cli)
        cli.ROOT = self.root
        self.file('test/test_design_acceptance.py', b'fixture')
        self.file('scripts/execution-vectors.py', b'fixture')
        missing = dict(path='missing.json', sha256='0' * 64)
        selection = self.file('selection.json', dict(schema=1, policy=POLICY, roots={r: missing for r in ROOT_ROLES}))
        argv = ['check-design-acceptance.py', '--tag', 'refusal', '--selection', selection['path']]
        with patch.object(sys, 'argv', argv), contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(cli.main(), 1)
        report = self.root / 'build/validation/refusal/report.json'
        before = report.read_bytes()
        data = json.loads(before)
        self.assertEqual(data['status'], 'invalid_evidence')
        self.assertFalse(data['A_accepted'])
        self.assertIn('missing.json', data['error'])
        self.assertIn('scripts/execution-vectors.py', {p['path'] for p in data['checker_sources']})
        self.assertEqual(data['commands'], [])
        with patch.object(sys, 'argv', argv), self.assertRaises(FileExistsError):
            cli.main()
        self.assertEqual(report.read_bytes(), before)

    def test_refusal_checks_survive_python_optimization(self):
        script = "from design_acceptance import require; require(False, 'refused')"
        result = subprocess.run([sys.executable, '-OO', '-c', script], cwd=ROOT / 'scripts',
                                capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('ValueError: refused', result.stderr)


if __name__ == '__main__':
    unittest.main()
