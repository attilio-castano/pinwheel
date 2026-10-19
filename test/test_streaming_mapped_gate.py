"""Refuse scope laundering, stale raw inputs and incomplete mapped devices."""
from copy import deepcopy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import struct
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('mapped_gate_fixture', ROOT / 'scripts/check-streaming-mapped.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def device():
    names = ['Pinwheel.Artifact.target' + str(n) for n in range(44)]
    result = dict(complete_device_checked=True, all_native_cases_checked=True,
        all_device_mutations_checked=True, all_complete_costs_checked=True,
        required_qnames=names, extra_qnames=gate.expected_extra_qnames(), full_state_bits={'2': 6039, '4': 6195}, depths={})
    for depth, bits in (('2', 6039), ('4', 6195)):
        result['depths'][depth] = dict(cost=dict(schema='pinwheel.streaming-mapped-cost.v1',
            scope='complete-tiny-tapeout', top='tt_um_pinwheel_streaming_ready_d' + depth,
            declared_state_bits=bits, physical_ff_bits=bits, inputs_unchanged=True,
            timing_qualified=False, mapped_equivalence_proved=False,
            liberty_sha256=gate.LIBRARY_SHA256, combinational_cells=100),
            uart=dict(depth=int(depth), genuine=True), i2c=dict(depth=int(depth), genuine=True),
            legacy=dict(depth=int(depth), genuine=True), controls=[dict(name=name, passed=True, expected_rejection=True)
                for name in ('changed-pad', 'status-wire', 'changed-clock')])
    return result, names


def checks():
    def check(result):
        if result.get('genuine') is not True: raise RuntimeError('Missing independent native evidence')
    return dict(uart_check=check, i2c_check=check, legacy_check=check,
        native_check=lambda *args: None, cost_check=lambda *args: None)


def native_fixture(root):
    root = Path(root)
    for name in ('complete.json', 'complete.sv', 'sampler-ff-pin.sv', 'complete.vvp', 'sampler-ff-pin.vvp', 'cells.sv'):
        (root / name).write_text('actual fixture bytes ' + name)
    tools = dict(vvp='/pinned/bin/vvp')
    intent = dict(schema='pinwheel.streaming-mapped-native-intent.v1', depth=2, vvp=tools['vvp'],
        scopes=['UART24', 'I2C10', 'SPI32768', 'JTAG4097'],
        executable_sha256={name: gate.digest(root / (name + '.vvp')) for name in ('complete', 'sampler-ff-pin')},
        source_sha256={name: gate.digest(root / (name + '.sv')) for name in ('complete', 'sampler-ff-pin')},
        model_sha256=gate.digest(root / 'cells.sv'))
    (root / 'native-intent.json').write_text(json.dumps(intent))
    runs, events = [], []
    for index, scope in enumerate(['uart'] * 2 + ['legacy'] * 2 + ['i2c'] * 10):
        name = 'sampler-ff-pin' if index == 1 else 'complete'
        argv = [tools['vvp'], str(root / (name + '.vvp'))]
        row = dict(index=index, scope=scope, argv=argv, actual_argv=argv,
            native_exit_code=0, physical_edges=index + 1, client_succeeded=True,
            executable_sha256_before=intent['executable_sha256'][name],
            executable_sha256_after=intent['executable_sha256'][name])
        runs.append(row)
        events.extend((dict(event='intent', **{key: row[key] for key in
            ('index', 'scope', 'argv', 'executable_sha256_before')}), dict(event='result', **row)))
    journal = root / 'native.jsonl'; journal.write_text('\n'.join(map(json.dumps, events)) + '\n')
    result = dict(complete_json=str(root / 'complete.json'), complete_sha256=gate.digest(root / 'complete.json'),
        native_intent=intent, native_runs=runs, native_journal=str(journal), native_journal_sha256=gate.digest(journal),
        physical_edges=sum(row['physical_edges'] for row in runs))
    for name, rows, key in (('uart', runs[:2], 'native_runs'), ('legacy', runs[2:4], 'cases'), ('i2c', runs[4:], 'cases')):
        result[name] = {key: [dict(physical_edges=row['physical_edges']) for row in rows],
            'physical_edges': sum(row['physical_edges'] for row in rows)}
        for index, case in enumerate(result[name][key]):
            if name == 'uart': path = root / 'uart' / ('unchanged.bin' if index == 0 else 'sampler-ff-pin.bin')
            elif name == 'legacy':
                case['protocol'] = ('spi', 'jtag')[index]
                path = root / 'legacy' / case['protocol'] / 'wire.bin'
            else:
                case['direction'] = 'read' if index < 5 else 'write'
                case['profile'] = ('clean', 'varying', 'lastpoll', 'timeout', 'address_nack')[index % 5]
                path = root / 'i2c' / (case['direction'] + '-' + case['profile']) / 'wire.bin'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b''.join(struct.pack('<I16B', n, *([0] * 16)) for n in range(1, case['physical_edges'] + 1)))
            case['trace'] = dict(edges=case['physical_edges'], bytes=case['physical_edges'] * 20,
                sha256=gate.digest(path), format=gate.TRACE_FORMAT)
    return result, tools


class MappedGateTests(unittest.TestCase):
    def test_real_generated_session_imports_are_in_the_built_library_closure(self):
        def closure(seeds):
            visited, pending = set(), list(seeds)
            while pending:
                module = pending.pop()
                if module in visited or module != 'Pinwheel' and not module.startswith('Pinwheel.'):
                    continue
                path = ROOT / (module.replace('.', '/') + '.lean')
                self.assertTrue(path.is_file(), 'Missing actual project module: ' + module)
                visited.add(module)
                pending.extend(name for line in re.findall(r'^import\s+([^\n]+)', path.read_text(), re.MULTILINE)
                    for name in line.split())
            return visited
        imports = gate.generated_session_library_imports()
        self.assertTrue(imports)
        required = closure(imports)
        self.assertFalse(required - closure(gate.BUILD_ROOTS),
            'Generated sessions depend on project modules outside the native build targets')
        # This is the dependency failure from the real partial UART-root build,
        # derived from source imports rather than an expected BUILD_ROOTS string.
        self.assertTrue(required - closure(('Pinwheel.Hardware.StreamingUART.All',
            'Pinwheel.Hardware.StreamingMapped.All')))

    def test_native_import_preflight_loads_transitive_oleans_and_refuses_a_missing_dependency(self):
        lean = shutil.which('lean')
        if lean is None:
            self.skipTest('Native Lean is unavailable for the transitive import control')
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            env = dict(os.environ, LEAN_PATH=str(root))
            for name, text in (('PreflightLeaf', 'def preflightMarker : Nat := 7\n'),
                    ('PreflightParent', 'import PreflightLeaf\nexample : preflightMarker = 7 := rfl\n')):
                source = root / (name + '.lean'); source.write_text(text)
                result = subprocess.run([lean, '--root=' + str(root), '-o', str(root / (name + '.olean')), str(source)],
                    cwd=ROOT, env=env, capture_output=True, text=True, timeout=60)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            calls = []
            def native(argv, label, **options):
                calls.append((argv, label))
                result = subprocess.run(argv[2:], cwd=ROOT, env=env, capture_output=True, text=True, timeout=60)
                if result.returncode:
                    raise RuntimeError(result.stdout + result.stderr)
                return result.stdout
            tools = dict(lake='fixture-lake-env', lean=lean)
            positive = root / 'positive'; positive.mkdir()
            receipt = gate.library_import_preflight(positive, tools, native, modules=['PreflightParent'])
            self.assertTrue(receipt['checked'])
            self.assertEqual(receipt['sha256'], gate.digest(receipt['source']))
            self.assertEqual(calls[0][0][:3], [tools['lake'], 'env', lean])
            (root / 'PreflightLeaf.olean').unlink()
            self.assertTrue((root / 'PreflightParent.olean').is_file())
            missing = root / 'missing'; missing.mkdir()
            with self.assertRaisesRegex(RuntimeError, "unknown module prefix 'PreflightLeaf'|PreflightLeaf.*does not exist"):
                gate.library_import_preflight(missing, tools, native, modules=['PreflightParent'])
            self.assertEqual(len(calls), 2)

    def test_preflight_source_cannot_change_during_native_loading(self):
        with tempfile.TemporaryDirectory() as temporary:
            def changed(argv, label, **options):
                Path(argv[-1]).write_text('import DifferentModule\n')
            with self.assertRaisesRegex(RuntimeError, 'changed during native execution'):
                gate.library_import_preflight(temporary, dict(lake='lake', lean='lean'), changed,
                    modules=['PreflightParent'])

    def test_preflight_receipt_binds_exact_factory_import_text_and_worker_location(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            modules = gate.generated_session_library_imports()
            text = ''.join('import ' + module + '\n' for module in modules)
            source = root / 'MappedSessionLibraryImports.lean'; source.write_text(text)
            receipt = dict(checked=True, modules=modules, source=str(source), sha256=gate.digest(source))
            gate.validate_library_import_preflight(receipt, root)
            alternate = root / 'unrelated.lean'; alternate.write_text(text)
            with self.assertRaisesRegex(RuntimeError, 'retained worker path'):
                gate.validate_library_import_preflight(dict(receipt, source=str(alternate)), root)
            source.write_text('import ' + modules[0] + '\n')
            with self.assertRaisesRegex(RuntimeError, 'actual generated session import set'):
                gate.validate_library_import_preflight(dict(receipt, sha256=gate.digest(source)), root)

    def test_all_new_mapped_helpers_tests_and_kernel_modules_are_required_committed(self):
        tree = {name: 'oid' for name in gate.required_inputs({})}
        tree['scripts/streaming_mapped_future.py'] = 'new'
        selected = gate.required_inputs(tree)
        self.assertIn('scripts/check-streaming-mapped.py', selected)
        self.assertIn('test/test_streaming_mapped_package.py', selected)
        self.assertIn('Pinwheel/Hardware/StreamingMapped/Clauses.lean', selected)
        self.assertIn('scripts/streaming_mapped_future.py', selected)
        self.assertNotIn('docs/research/status.md', selected)
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'scripts').mkdir()
            self.assertEqual(set(gate.producer_inputs(root, tree)), selected)
            (root / 'scripts/streaming_mapped_uncommitted.py').write_text('pass\n')
            with self.assertRaisesRegex(RuntimeError, 'Commit every mapped'):
                gate.producer_inputs(root, tree)

    def test_frozen_consumed_artifacts_reject_changed_missing_and_redirected_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / 'raw.json'; path.write_bytes(b'first')
            files = {str(path): gate.digest(path)}
            gate.verify_files(files)
            path.write_bytes(b'changed')
            with self.assertRaises(RuntimeError): gate.verify_files(files)
            path.unlink()
            with self.assertRaises(RuntimeError): gate.verify_files(files)
            target = root / 'target'; target.write_bytes(b'first'); path.symlink_to(target)
            with self.assertRaises(RuntimeError): gate.verify_files(files)

    def test_duplicate_receipt_keys_and_symlink_inventory_are_not_accepted(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / 'receipt.json'; path.write_text('{"passed":false,"passed":true}')
            with self.assertRaisesRegex(RuntimeError, 'Duplicate'): gate.read_json(path)
            (root / 'redirect').symlink_to(path)
            with self.assertRaisesRegex(RuntimeError, 'Symlink'): gate.regular_inventory(root)

    def test_commands_require_actual_zero_or_declared_nonzero_exits(self):
        gate.command_inventory([dict(exit_code=0, expected_failure=False), dict(exit_code=1, expected_failure=True)])
        for row in ({}, dict(exit_code=True), dict(exit_code=1), dict(exit_code=0, expected_failure=True),
                dict(exit_code=1, expected_failure=True, error='TimeoutError')):
            with self.subTest(row=row), self.assertRaises(RuntimeError): gate.command_inventory([row])

    def test_pre_use_journal_cannot_omit_or_change_native_commands(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            rows = [dict(label='native', argv=['lean', 'Proof.lean'], exit_code=0)]
            path = root / 'command-intents.jsonl'
            path.write_text(json.dumps(dict(index=0, label='native', argv=rows[0]['argv'])) + '\n')
            gate.verify_journal(root, rows)
            for change in (dict(index=1, label='native', argv=rows[0]['argv']),
                    dict(index=0, label='native', argv=['native_decide']), {}):
                path.write_text(json.dumps(change) + '\n')
                with self.assertRaisesRegex(RuntimeError, 'intents'): gate.verify_journal(root, rows)

    def test_exact_device_flags_depths_and44_names_are_mandatory(self):
        baseline, names = device()
        self.assertTrue(gate.validate_device(baseline, names, **checks()))
        for field in ('complete_device_checked', 'all_native_cases_checked',
                'all_device_mutations_checked', 'all_complete_costs_checked'):
            changed = deepcopy(baseline); changed[field] = False
            with self.subTest(field=field), self.assertRaises(RuntimeError): gate.validate_device(changed, names, **checks())
        for change in ('depth', 'names', 'state', 'extra'):
            changed = deepcopy(baseline)
            if change == 'depth': del changed['depths']['4']
            elif change == 'names': changed['required_qnames'] = list(reversed(names))
            elif change == 'state': changed['full_state_bits']['2'] = 5797
            else: changed['extra_qnames'] = changed['extra_qnames'][:-1]
            with self.subTest(change=change), self.assertRaises(RuntimeError): gate.validate_device(changed, names, **checks())

    def test_complete_cost_cannot_be_a_component_partial_state_or_timing_claim(self):
        baseline, names = device()
        for field, value in (('scope', 'component'), ('top', 'other'), ('physical_ff_bits', 5797),
                ('declared_state_bits', 6038), ('inputs_unchanged', False), ('timing_qualified', True),
                ('mapped_equivalence_proved', True), ('liberty_sha256', 'a' * 64)):
            changed = deepcopy(baseline); changed['depths']['2']['cost'][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(RuntimeError, 'cost'):
                gate.validate_device(changed, names, **checks())

    def test_native_validators_and_distinguishing_device_controls_are_not_boolean_flags(self):
        baseline, names = device()
        for kind in ('uart', 'i2c', 'legacy'):
            changed = deepcopy(baseline); changed['depths']['4'][kind]['genuine'] = False
            with self.subTest(kind=kind), self.assertRaisesRegex(RuntimeError, 'independent native'):
                gate.validate_device(changed, names, **checks())
        for mode in ('omit', 'order', 'self-assert'):
            changed = deepcopy(baseline); rows = changed['depths']['2']['controls']
            if mode == 'omit': rows.pop()
            elif mode == 'order': rows.reverse()
            else: rows[0]['expected_rejection'] = False
            with self.subTest(mode=mode), self.assertRaisesRegex(RuntimeError, 'distinguishing'):
                gate.validate_device(changed, names, **checks())

    def test_raw_stage_cannot_be_replaced_by_historical_full_or_different_source_receipt(self):
        raw = SimpleNamespace(SCHEMA='raw', validate_worker=lambda *args, **kwargs: None)
        report = dict(schema='raw', stage='components', source_commit='same', producer_commit='same', passed=True,
            full_qualification=False, committed_archive_membership_verified_before=True,
            committed_archive_membership_verified_after=True, tool_identity_unchanged=True,
            selected_git_objects={'file': 'oid'}, source_sha256={'file': 'sha'})
        config = dict(source_commit='same', producer_commit='same', source_tree={'file': 'oid'}, source_sha256={'file': 'sha'})
        for field, value in (('stage', 'full'), ('full_qualification', True), ('source_commit', 'historical'),
                ('producer_commit', 'other'), ('passed', False), ('committed_archive_membership_verified_after', False)):
            changed = deepcopy(report); changed[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(RuntimeError, 'same-commit'):
                gate.validate_raw(changed, config, raw, 'same', {'file': 'oid'}, {'file': 'sha'}, None)
        changed = deepcopy(config); changed['producer_commit'] = 'old'
        with self.assertRaisesRegex(RuntimeError, 'same-commit'):
            gate.validate_raw(report, changed, raw, 'same', {'file': 'oid'}, {'file': 'sha'}, None)

    def test_native_all14_actual_processes_bind_argv_exit_executable_and_case_edges(self):
        with tempfile.TemporaryDirectory() as temporary:
            baseline, tools = native_fixture(Path(temporary))
            gate.validate_native(baseline, 2, tools)
            for field, value in (('actual_argv', ['/other/vvp', 'other.vvp']), ('native_exit_code', 1),
                    ('executable_sha256_after', '0' * 64), ('client_succeeded', False), ('physical_edges', 999)):
                changed = deepcopy(baseline); changed['native_runs'][0][field] = value
                with self.subTest(field=field), self.assertRaises(RuntimeError):
                    gate.validate_native(changed, 2, tools)
            changed = deepcopy(baseline); changed['native_runs'].pop()
            with self.assertRaisesRegex(RuntimeError, 'All14'): gate.validate_native(changed, 2, tools)
            changed = deepcopy(baseline); changed['legacy']['cases'][0]['physical_edges'] += 1
            with self.assertRaisesRegex(RuntimeError, 'independent protocol'): gate.validate_native(changed, 2, tools)

    def test_native_intent_journal_and_executable_cannot_change_after_use(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); baseline, tools = native_fixture(root)
            path = root / 'native.jsonl'; original = path.read_text()
            path.write_text(original.replace('"event": "intent"', '"event": "after"', 1))
            changed = deepcopy(baseline); changed['native_journal_sha256'] = gate.digest(path)
            with self.assertRaisesRegex(RuntimeError, 'pre-use'): gate.validate_native(changed, 2, tools)
            path.write_text(original)
            (root / 'complete.vvp').write_text('different native program')
            with self.assertRaisesRegex(RuntimeError, 'binding changed'): gate.validate_native(baseline, 2, tools)

    def test_native_trace_metadata_must_match_the_actual_retained_trace_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            baseline, tools = native_fixture(Path(temporary))
            for group, rows in (('uart', 'native_runs'), ('legacy', 'cases'), ('i2c', 'cases')):
                changed = deepcopy(baseline); changed[group][rows][0]['trace']['sha256'] = '0' * 64
                with self.subTest(group=group), self.assertRaisesRegex(RuntimeError, 'trace bytes differ'):
                    gate.validate_native(changed, 2, tools)
            path = Path(temporary) / 'legacy/spi/wire.bin'
            path.write_bytes(path.read_bytes()[:-1])
            with self.assertRaisesRegex(RuntimeError, 'truncated'): gate.validate_native(baseline, 2, tools)

    def test_complete_trace_hash_does_not_make_reordered_or_missing_cycle_ids_valid(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); baseline, tools = native_fixture(root)
            path = root / 'uart/sampler-ff-pin.bin'
            rows = [struct.pack('<I16B', n, *([0] * 16)) for n in (2, 1)]
            path.write_bytes(b''.join(rows))
            baseline['uart']['native_runs'][1]['trace']['sha256'] = gate.digest(path)
            with self.assertRaisesRegex(RuntimeError, 'cycles'): gate.validate_native(baseline, 2, tools)

    def test_symlink_and_hardlink_cannot_redirect_a_physical_trace(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); baseline, tools = native_fixture(root)
            path = root / 'uart/unchanged.bin'; saved = root / 'saved.bin'
            path.rename(saved); path.symlink_to(saved)
            with self.assertRaisesRegex(RuntimeError, 'retained physical-edge'): gate.validate_native(baseline, 2, tools)
            path.unlink(); path.hardlink_to(saved)
            with self.assertRaisesRegex(RuntimeError, 'aliased'): gate.validate_native(baseline, 2, tools)

    def test_complete_cost_binds_retained_bill_actual_netlist_and_selected_library(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            full, library = root / 'complete.json', root / 'cells.lib'
            full.write_text('actual complete netlist'); library.write_text('fixture pinned library')
            lib_hash, full_hash = gate.digest(library), gate.digest(full)
            cost = dict(input_sha256={str(full): full_hash, str(library): lib_hash}, physical_ff_bits=6039)
            (root / 'cost.json').write_text(json.dumps(cost))
            result = dict(cost=cost, complete_json=str(full), complete_sha256=full_hash)
            called = []
            def recompute(*args, **options):
                called.append((args, options)); return deepcopy(cost)
            with patch.object(gate, 'LIBRARY_SHA256', lib_hash):
                gate.validate_cost(result, 2, library, recompute)
                self.assertEqual(called, [((full, 'tt_um_pinwheel_streaming_ready_d2', library, 6039), dict(complete=True))])
                changed = deepcopy(result); changed['cost']['input_sha256'][str(full)] = 'old'
                with self.assertRaisesRegex(RuntimeError, 'stale'): gate.validate_cost(changed, 2, library, recompute)
                with self.assertRaisesRegex(RuntimeError, 'recomputation'):
                    gate.validate_cost(result, 2, library, lambda *args, **kwargs: dict(physical_ff_bits=6038))
                (root / 'cost.json').write_text(json.dumps(dict(physical_ff_bits=6039)))
                with self.assertRaisesRegex(RuntimeError, 'stale'): gate.validate_cost(result, 2, library, recompute)

    def test_worker_config_bytes_are_verified_before_any_source_or_output_use(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'config.json'; path.write_text('{}')
            with self.assertRaisesRegex(RuntimeError, 'parent-frozen'):
                gate.worker(path, '0' * 64)
            self.assertEqual(list(Path(temporary).iterdir()), [path])

    def test_narrow_cad_receipt_cannot_broaden_historical_global_archive_claim(self):
        receipt = dict(schema='pinwheel.streaming-mapped-selected-cad-archive-membership.v1',
            cad_selected_archive_membership_verified=True, installed_payload_archive_membership_proved=False,
            packages={'circt': {'actual': 'archive1'}, 'oss-cad-suite': {'actual': 'archive2'}}, selected_cad_files=10)
        gate.validate_cad_membership(receipt, deepcopy(receipt))
        for field, value in (('cad_selected_archive_membership_verified', False),
                ('installed_payload_archive_membership_proved', True), ('selected_cad_files', 0)):
            changed = deepcopy(receipt); changed[field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError):
                gate.validate_cad_membership(changed, changed)
        changed = deepcopy(receipt); changed['packages']['circt']['actual'] = 'other-archive'
        with self.assertRaisesRegex(RuntimeError, 'independent audit'):
            gate.validate_cad_membership(changed, receipt)

    def test_all44_expected_targets_are_the_real_two_depth_session_APIs(self):
        raw = gate.load('_mapped_test_raw', ROOT / gate.RAW_DRIVER)
        names = gate.expected_qnames(raw)
        self.assertEqual(len(names), 44)
        self.assertEqual(len(set(names)), 44)
        for depth in (2, 4):
            self.assertIn('Pinwheel.Artifact.StreamingMappedSessionD' + str(depth) + '.initialized_runtime_correct', names)
            self.assertIn('Pinwheel.Artifact.StreamingMappedSessionD' + str(depth) + '.uart_frame_correct', names)

    def test_historical_report_option_is_not_a_supported_gate_input(self):
        result = subprocess.run([sys.executable, '-B', str(ROOT / gate.DRIVER), '--raw-report', '/tmp/old.json'],
            capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 2)
        self.assertIn('unrecognized arguments: --raw-report', result.stderr)


if __name__ == '__main__': unittest.main()
