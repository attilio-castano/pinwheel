"""Pure refusal controls for the coordinator, not artifact qualification."""
from copy import deepcopy
import hashlib
import importlib.util
from pathlib import Path
import sys
import tempfile
import types
import unittest


ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('_continuation_under_test',
    ROOT / 'scripts/check-streaming-continuation.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def raw_report(kind, address_bits):
    prefix = 'CoreD' + str(2 ** address_bits) if kind == 'core' else 'QuadFrontend'
    names = ('unchanged', 'program-bank', 'owner-output') if kind == 'core' else (
        'unchanged', 'retained-export', 'ready-output')
    return dict(passed=True, kind=kind, addr_bits=address_bits, all_state=True,
        all_outputs=True, frozen_inputs_unchanged=True, registers=1, state_bits=3,
        outputs=1, source_nodes=2, rtl_nodes=2, partitions=1,
        compiled_modules=[prefix + suffix for suffix in ('Hints', 'Sources', 'Graphs',
            'LocalProofs', 'Links', 'Model', 'Endpoints', 'Proof')],
        emitted_input_sha256_before={name: 'sha' for name in (
            'core.mlir', 'frontend.mlir', 'assembly.json', 'frontend-assembly.json')},
        emitted_input_sha256_after={name: 'sha' for name in (
            'core.mlir', 'frontend.mlir', 'assembly.json', 'frontend-assembly.json')},
        axiom_audit='Pinwheel audit: 123 declarations, 50 theorems; standard axioms only.',
        mutations=[dict(name=name, passed=True, expected_rejection=index != 0,
            all_state_reimport=index == 0, operation='test fixture')
            for index, name in enumerate(names)], private_axiom_rejected=True,
        positive_proof_closure={'positive': 'hash'}, private_control_proof_closure={'private': 'hash'})


def wrapper_report():
    return dict(passed=True, inputs_unchanged=True, mutations=[dict(name=name,
        passed=True, expected_rejection=index != 0, proof_directory='fixture/' + name,
        module='Fixture') for index, name in enumerate(
            ('unchanged', 'package-wire', 'package-clock', 'tiny-output'))])


def component_receipt():
    assembly = dict(registers=[dict(width=3)], outputs=[dict(width=1)])
    report = dict(schema=gate.SCHEMA, stage='components', passed=True,
        full_qualification=False, source_commit='source', producer_commit='producer',
        required_targets=[], stages={name: dict(passed=True) for name in
            ('library', 'emission', 'raw-components', 'actual-wrappers')},
        commands=[dict(exit_code=0, expected_failure=False)] +
            [dict(exit_code=1, expected_failure=True) for _ in range(15)])
    report['stages']['emission']['result'] = dict(interfaces={str(a):
        dict(core=assembly, frontend=assembly) for a in (1, 2)})
    report['stages']['raw-components']['result'] = {
        'frontend': raw_report('frontend', 1), 'core-d2': raw_report('core', 1),
        'core-d4': raw_report('core', 2)}
    report['stages']['actual-wrappers']['result'] = {
        '2': wrapper_report(), '4': wrapper_report()}
    return report, dict(stage='components', source_commit='source', producer_commit='producer')


class CoordinatorControls(unittest.TestCase):
    def test_retained_archives_are_rechecked_at_closeout(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            report = {}
            helper = types.SimpleNamespace(digest=lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest())
            for name in ('selected', 'producer'):
                path = root / (name + '-source.tar')
                path.write_bytes((name + ' committed archive').encode())
                report[name + '_archive_sha256'] = helper.digest(path)
            gate.archive_closeout(helper, root, report)
            for name in ('selected', 'producer'):
                path = root / (name + '-source.tar')
                original = path.read_bytes()
                path.write_bytes(b'changed retained archive')
                with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'archive changed'):
                    gate.archive_closeout(helper, root, report)
                path.write_bytes(original)
                target = root / (name + '-copy.tar')
                target.write_bytes(original)
                path.unlink()
                path.symlink_to(target)
                with self.subTest(symlink=name), self.assertRaisesRegex(RuntimeError, 'archive changed'):
                    gate.archive_closeout(helper, root, report)
                path.unlink()
                path.write_bytes(original)
            (root / 'producer-source.tar').unlink()
            with self.assertRaisesRegex(RuntimeError, 'archive changed'):
                gate.archive_closeout(helper, root, report)

    def test_stage_inputs_require_initialization_and_input_bridge_only_for_full(self):
        full = gate.required_inputs('full')
        for name in ('SessionCorrespondence', 'Initialization', 'InputCorrespondence', 'InitializedSession'):
            path = 'Pinwheel/Hardware/Streaming/' + name + '.lean'
            self.assertIn(path, full)
            self.assertNotIn(path, gate.required_inputs('wire'))
        self.assertIn('scripts/streaming_adversarial.py', full)
        self.assertIn('scripts/streaming_staging_race.py', full)
        self.assertIn('Pinwheel/Program/StreamingTiming.lean', full)
        with self.assertRaises(ValueError): gate.required_inputs('reused-receipt')

    def test_partial_components_can_pass_without_claiming_full_qualification(self):
        report, config = component_receipt()
        gate.validate_worker(report, config)
        report['full_qualification'] = True
        with self.assertRaisesRegex(RuntimeError, 'exact requested'):
            gate.validate_worker(report, config)

    def test_partial_scope_cannot_advertise_full_targets(self):
        report, config = component_receipt()
        report['required_targets'] = list(gate.TARGETS)
        with self.assertRaisesRegex(RuntimeError, 'exact requested'):
            gate.validate_worker(report, config)

    def test_source_producer_and_stage_identity_must_match(self):
        report, config = component_receipt()
        for key in ('source_commit', 'producer_commit', 'stage'):
            changed = deepcopy(report)
            changed[key] = 'wrong'
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                gate.validate_worker(changed, config)

    def test_missing_depth_or_duplicate_raw_component_is_rejected(self):
        report, config = component_receipt()
        report['stages']['raw-components']['result'].pop('core-d4')
        with self.assertRaisesRegex(RuntimeError, 'three distinct'):
            gate.validate_worker(report, config)

    def test_missing_wrapper_boundary_is_rejected(self):
        report, config = component_receipt()
        report['stages']['actual-wrappers']['result'].pop('4')
        with self.assertRaisesRegex(RuntimeError, 'Both actual wrapper'):
            gate.validate_worker(report, config)

    def test_incomplete_stage_and_unfinished_or_wrong_exit_commands_refuse(self):
        baseline, config = component_receipt()
        for command in ({'expected_failure': True}, {'exit_code': 0, 'expected_failure': True},
                {'exit_code': 1, 'expected_failure': False},
                {'exit_code': 1, 'expected_failure': True, 'error': 'TimeoutError'}):
            report = deepcopy(baseline)
            report['commands'].append(command)
            with self.subTest(command=command), self.assertRaisesRegex(RuntimeError, 'command outcome'):
                gate.validate_worker(report, config)
        baseline['stages']['library']['passed'] = False
        with self.assertRaisesRegex(RuntimeError, 'Incomplete mandatory'):
            gate.validate_worker(baseline, config)

    def test_control_count_cannot_be_replaced_by_positive_commands(self):
        report, config = component_receipt()
        report['commands'][-1] = dict(exit_code=0, expected_failure=False)
        with self.assertRaisesRegex(RuntimeError, 'expected-failure'):
            gate.validate_worker(report, config)

    def test_closeout_requires_all_immutable_checks(self):
        report, config = component_receipt()
        keys = ('archived_inputs_unchanged', 'producer_unchanged',
            'tool_identity_unchanged', 'frozen_artifacts_unchanged')
        report.update({key: True for key in keys})
        gate.validate_worker(report, config, closeout=True)
        for key in keys:
            changed = deepcopy(report)
            changed[key] = False
            with self.subTest(key=key), self.assertRaisesRegex(RuntimeError, 'immutable'):
                gate.validate_worker(changed, config, closeout=True)

    def test_raw_all_state_metadata_and_exact_inputs_are_required(self):
        assembly = dict(registers=[dict(width=3)], outputs=[dict(width=1)])
        baseline = raw_report('core', 1)
        gate.check_component(baseline, 'core', 1, assembly)
        changes = dict(all_state=False, all_outputs=False, registers=2, state_bits=4,
            outputs=2, partitions=0, compiled_modules=['CoreD2Proof'],
            emitted_input_sha256_before={'core.mlir': 'sha'})
        for key, value in changes.items():
            report = deepcopy(baseline)
            report[key] = value
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                gate.check_component(report, 'core', 1, assembly)
        baseline['emitted_input_sha256_after']['core.mlir'] = 'changed'
        with self.assertRaises(RuntimeError): gate.check_component(baseline, 'core', 1, assembly)

    def test_raw_audit_is_mandatory_and_unambiguous(self):
        assembly = dict(registers=[dict(width=3)], outputs=[dict(width=1)])
        for audit in ('', 'Pinwheel audit: standard axioms only.',
                raw_report('core', 1)['axiom_audit'] * 2):
            report = raw_report('core', 1)
            report['axiom_audit'] = audit
            with self.subTest(audit=audit), self.assertRaisesRegex(RuntimeError, 'audit'):
                gate.check_component(report, 'core', 1, assembly)

    def test_raw_controls_cannot_be_reordered_omitted_or_self_asserted(self):
        baseline = raw_report('frontend', 1)
        names = ('unchanged', 'retained-export', 'ready-output')
        for mutate in (lambda r: r['mutations'].reverse(),
                lambda r: r['mutations'].pop(),
                lambda r: r['mutations'][1].update(expected_rejection=False),
                lambda r: r['mutations'][1].update(all_state_reimport=True),
                lambda r: r['mutations'][0].update(operation=''),
                lambda r: r.update(private_axiom_rejected=False)):
            report = deepcopy(baseline)
            mutate(report)
            with self.assertRaises(RuntimeError):
                gate.check_mutations(report, names, private_axiom=True)

    def test_wrapper_controls_require_concrete_isolated_proof_modules(self):
        report = wrapper_report()
        names = ('unchanged', 'package-wire', 'package-clock', 'tiny-output')
        gate.check_mutations(report, names, stateless=True)
        for key in ('module', 'proof_directory'):
            changed = deepcopy(report)
            changed['mutations'][2][key] = ''
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                gate.check_mutations(changed, names, stateless=True)

    def test_full_receipt_refuses_missing_initialization_join_before_finite_tests(self):
        report, config = component_receipt()
        config['stage'] = report['stage'] = 'full'
        report.update(full_qualification=True, required_targets=list(gate.TARGETS))
        for name in ('public-wire', 'matched-cost', 'composition-and-audit'):
            report['stages'][name] = dict(passed=True, result={})
        with self.assertRaisesRegex(RuntimeError, 'initialized-upload'):
            gate.validate_worker(report, config)

    def test_wire_scope_refuses_missing_or_wrong_depth_terminal_races(self):
        config = dict(stage='wire', source_commit='source', producer_commit='producer')
        for races in ({}, {'2': {}}, {'2': {}, '8': {}}):
            report = dict(schema=gate.SCHEMA, stage='wire', passed=True, full_qualification=False,
                source_commit='source', producer_commit='producer', required_targets=[],
                commands=[dict(exit_code=0, expected_failure=False)],
                stages={name: dict(passed=True) for name in ('library', 'emission', 'public-wire')})
            report['stages']['public-wire']['result'] = dict(raw_certified_inputs=False,
                adversarial={'2': {}, '4': {}}, staging_races=races)
            with self.subTest(races=races), self.assertRaisesRegex(RuntimeError, 'depth coverage'):
                gate.validate_worker(report, config)

    def test_factory_requires_both_nonempty_named_depth_roots(self):
        for values in ({}, {'Other': 'import Init'}, {'StreamingSessionD2': ''},
                {'StreamingSessionD2': 'import Init', '../escape': 'x'}):
            factory = types.SimpleNamespace(generate=lambda a, values=values: values)
            with self.subTest(values=values), self.assertRaisesRegex(RuntimeError, 'factory'):
                gate.composition_texts(factory, 1)
        factory = types.SimpleNamespace(generate=lambda a: {'StreamingSessionD2': 'import Init'})
        self.assertEqual(gate.composition_texts(factory, 1)[1], 'StreamingSessionD2')

    def test_required_target_checks_are_native_lean_and_include_initialized_api(self):
        source = gate.join_checks(['StreamingSessionD2', 'StreamingSessionD4'])
        self.assertEqual(source.count('#check '), 36)
        for depth in (2, 4):
            for theorem in gate.JOIN_THEOREMS:
                self.assertIn('#check Pinwheel.Artifact.StreamingSessionD' + str(depth) + '.' + theorem, source)
        with self.assertRaises(RuntimeError): gate.join_checks(['StreamingSessionD2'] * 2)

    def test_generated_negative_directories_are_never_ambiguously_merged(self):
        with tempfile.TemporaryDirectory() as temporary:
            directories = [Path(temporary) / name for name in ('one', 'two')]
            for directory in directories:
                directory.mkdir()
                (directory / 'Mutant.lean').write_text('import Init\n')
            fake = types.SimpleNamespace(digest=lambda p: 'hash', proof_closure=lambda *args: 'closure')
            self.assertEqual(gate.generated_closure(fake, ROOT, [directories[0]], ['Mutant'], {}), 'closure')
            with self.assertRaisesRegex(RuntimeError, 'Ambiguous generated'):
                gate.generated_closure(fake, ROOT, directories, ['Mutant'], {})

    def test_section_labels_are_namespaced_without_altering_command_options(self):
        called = []
        run = gate.SectionRun(lambda *args, **kwargs: called.append((args, kwargs)), 'raw-d2')
        run(['lean', 'Fixture.lean'], 'mutation', timeout=3, reject='proof mismatch')
        self.assertEqual(called, [((['lean', 'Fixture.lean'], 'raw-d2--mutation'),
            dict(timeout=3, reject='proof mismatch'))])

    def test_environment_refuses_solver_and_mapping_overrides(self):
        helper = types.SimpleNamespace(check_environment=lambda environment: None)
        gate.check_environment(helper, {'PATH': '/usr/bin'})
        for name in ('YOSYS_DATDIR', 'ABC_SCRIPT', 'Z3_TRACE', 'CIRCT_HOME', 'VVP_TEST'):
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, 'overrides'):
                gate.check_environment(helper, {name: 'override'})

    def test_identity_binds_abc_wrapper_payload_lean_cache_and_mapping_data(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            oss, lean, circt = (root / name for name in ('oss', 'lean', 'circt'))
            files = [oss / 'bin' / name for name in ('yosys', 'yosys-abc', 'z3')]
            files += [oss / 'libexec' / name for name in ('yosys', 'yosys-abc', 'z3', 'realpath')]
            files += [oss / 'share/yosys' / 'cells.lib', lean / 'lib/lean/Init.olean',
                lean / 'lib/lean/Init.olean.private', lean / 'lib/lean/Init.ir',
                lean / 'lib/lean/libLean.dylib', circt / 'lib/nested/libMLIR.so.1']
            for path in files:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b'fixture')
            tools = dict(circt=str(circt / 'bin/circt-opt'), iverilog=str(oss / 'bin/iverilog'),
                vvp=str(oss / 'bin/vvp'), lean=str(lean / 'bin/lean'), lake=str(lean / 'bin/lake'),
                python=sys.executable, yosys=str(oss / 'bin/yosys'),
                abc=str(oss / 'bin/yosys-abc'), solver=str(oss / 'bin/z3'))
            helper = types.SimpleNamespace(tool_identity=lambda *args: dict(files={}, scope='fixture'),
                digest=lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest())
            first = gate.tool_identity(helper, tools, {})
            self.assertEqual(set(first['files']), set(map(str, files)))
            (oss / 'libexec/yosys-abc').write_bytes(b'changed payload')
            self.assertNotEqual(first, gate.tool_identity(helper, tools, {}))
            (oss / 'libexec/z3').unlink()
            with self.assertRaisesRegex(RuntimeError, 'Missing or redirected'):
                gate.tool_identity(helper, tools, {})


if __name__ == '__main__': unittest.main()
