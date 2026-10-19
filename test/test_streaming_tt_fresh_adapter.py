"""Strict import ownership, compiler bounds and scoped-hook refusal controls."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import types
import unittest
import shutil
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import streaming_tt_fresh_foundation as F

SPEC = importlib.util.spec_from_file_location('fresh_adapter_entry', ROOT / 'scripts/check-streaming-ready-fresh.py')
ENTRY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ENTRY)


def binding(root):
    root = root.resolve()
    return dict(candidate_root=str(root / 'snapshot'), lean=str(root / 'tool/bin/lean'),
                lake=str(root / 'tool/bin/lake'), python=str(root / 'python'), modules=['Pinwheel', 'Pinwheel.Core'])


def full_foundation_fixture(root):
    """649 tiny source/object rows; structural fixtures, never compiled evidence."""
    root = root.resolve(); candidate = root / 'candidate'; candidate.mkdir()
    names = [f'Pinwheel.M{index:03d}' for index in range(648)] + ['Pinwheel']
    (candidate / 'Pinwheel').mkdir()
    for name in names[:-1]:
        (candidate / (name.replace('.', '/') + '.lean')).write_text('import Std\n')
    (candidate / 'Pinwheel.lean').write_text(''.join('import ' + name + '\n' for name in names[:-1]))
    for name in F.FOUNDATION_INPUTS:
        path = candidate / name
        if not path.exists(): path.parent.mkdir(parents=True, exist_ok=True); path.write_text('input:' + name)
    for name in F.ADAPTERS:
        path = candidate / name; path.parent.mkdir(parents=True, exist_ok=True); path.write_text('adapter:' + name)
    projection = {name: F.sha(candidate / name) for name in F.FOUNDATION_INPUTS}
    projection.update({name.replace('.', '/') + '.lean': F.sha(candidate / (name.replace('.', '/') + '.lean')) for name in names})
    retained = root / 'retained'; shutil.copytree(candidate, retained)
    library = retained / '.lake/build/lib/lean'
    for module in names:
        for suffix in ('.olean', '.ilean'):
            path = library / (module.replace('.', '/') + suffix); path.parent.mkdir(parents=True, exist_ok=True); path.write_text(module + suffix)
    control = library / F.CONTROL; control.parent.mkdir(parents=True); control.write_text('unused negative control')
    out = root / 'foundation'; out.mkdir()
    commands = [dict(label='build-' + name, exit_code=0) for name in names]
    commands += [dict(label='axioms', exit_code=0), dict(label='reject-untrusted-axiom', exit_code=1),
                 dict(label='compile-unused-private-axiom', exit_code=0), dict(label='reject-unused-private-axiom', exit_code=1)]
    for row in commands:
        (out / (row['label'] + '.log')).write_text('native fixture log')
    (out / 'axioms.log').write_text('Pinwheel audit: 123 declarations, 45 theorems; standard axioms only.')
    (out / 'reject-unused-private-axiom.log').write_text('Unapproved axioms in _private.Pinwheel.CI.FoundationPrivateControl.x.forbiddenUnused')
    packet = dict(passed=True, modules=649, serial_build=True, committed_input_membership_verified=True,
        inherited_override_guard_checked=True, exit_code=0, lean_resource_limits=['-M4096', '-j1', '-DElab.async=false'],
        executable_suites=65, kernel_suites=8, untrusted_axiom_rejected=True, unused_private_axiom_rejected=True,
        audited_declarations=123, audited_theorems=45, source_commit='a' * 40, source_sha256=projection,
        commands=commands, retained_snapshot=str(retained), retained_library=str(library),
        retained_library_artifact_sha256=F.manifest(library), retained_private_control_module=F.CONTROL)
    report = out / 'report.json'; report.write_text(json.dumps(packet))
    runtime = root / 'runtime.json'; runtime.write_text('{}')
    tools = {}
    for name in ('lean', 'lake', 'python'):
        path = root / name; path.write_text('fixture:' + name); tools[name] = str(path)
    return candidate, report, runtime, tools, packet


class FreshAdapterTests(unittest.TestCase):
    def test_positive_library_partition_excludes_exact_unused_control(self):
        modules = ['Pinwheel', 'Pinwheel.Core']
        artifacts = {name.replace('.', '/') + suffix: 'a' * 64 for name in modules for suffix in ('.olean', '.ilean')}
        artifacts[F.CONTROL] = 'b' * 64
        positive, negative = F.partition_library(modules, artifacts, F.CONTROL)
        self.assertEqual(len(positive), 4)
        self.assertEqual(negative, {F.CONTROL: 'b' * 64})
        for mutation in ('missing', 'extra', 'control-sidecar', 'bad-control-name'):
            changed = dict(artifacts); control = F.CONTROL
            if mutation == 'missing': changed.pop('Pinwheel/Core.olean')
            elif mutation == 'extra': changed['OldProof.olean'] = 'c' * 64
            elif mutation == 'control-sidecar': changed[F.CONTROL + '.private'] = 'c' * 64
            else: control = 'Pinwheel/Core.olean'
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                F.partition_library(modules, changed, control)

    def test_manifest_rejects_alias_and_captures_added_old_objects(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name); (root / 'Good.olean').write_text('good')
            before = F.manifest(root)
            (root / 'Old.olean').write_text('old')
            self.assertNotEqual(before, F.manifest(root))
            (root / 'Alias.olean').symlink_to(root / 'Good.olean')
            with self.assertRaises(ValueError): F.manifest(root)

    def test_module_membership_rejects_unimported_and_cyclic_source(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name); (root / 'Pinwheel').mkdir()
            (root / 'Pinwheel.lean').write_text('import Pinwheel.Core\n')
            (root / 'Pinwheel/Core.lean').write_text('import Std\n')
            self.assertEqual(F.module_order(root), ['Pinwheel.Core', 'Pinwheel'])
            (root / 'Pinwheel/Old.lean').write_text('import Std\n')
            with self.assertRaises(ValueError): F.module_order(root)
            (root / 'Pinwheel/Old.lean').unlink()
            (root / 'Pinwheel/Core.lean').write_text('import Pinwheel\n')
            with self.assertRaises(ValueError): F.module_order(root)

    def test_staging_never_copies_negative_control_and_refuses_preexisting_cache(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name); b = binding(root)
            snapshot = Path(b['candidate_root']); snapshot.mkdir()
            library = root / 'retained'; (library / 'Pinwheel/CI').mkdir(parents=True)
            (library / 'Pinwheel.olean').write_text('positive')
            (library / F.CONTROL).write_text('private axiom')
            b.update(foundation_library=str(library), positive_library_artifact_sha256={'Pinwheel.olean': F.sha(library / 'Pinwheel.olean')})
            with patch.object(F, 'verify_binding', return_value=True):
                staged = F.stage_library(b, snapshot)
                self.assertFalse((staged / F.CONTROL).exists())
                with self.assertRaises(ValueError): F.stage_library(b, snapshot)
            (staged / 'Old.olean').write_text('old cache')
            with self.assertRaises(ValueError): F.verify_staged(b)

    def test_direct_lean_translation_preserves_source_and_binds_only_fresh_library(self):
        root = Path('/bounded-case'); b = binding(root); worker = root / 'worker'
        proof = worker / 'proof'; source = proof / 'FreshProof.lean'
        requested = ['env', 'LEAN_PATH=' + str(proof), b['lake'], 'env', 'lean', '--root=' + str(proof),
                     '-DwarningAsError=true', '-o', str(source.with_suffix('.olean')), str(source)]
        actual = F.bounded_command(requested, b, worker, root / 'entry.py', root / 'binding.json')
        self.assertEqual(actual[:3], ['env', 'LEAN_PATH=' + b['candidate_root'] +
            '/.lake/build/lib/lean:' + str(root / 'tool/lib/lean') + ':' + str(proof), 'LEAN_SYSROOT=' + str(root / 'tool')])
        self.assertEqual(actual[3:7], [b['lean'], '-M4096', '-j1', '-DElab.async=false'])
        self.assertEqual(actual[-1], str(source))
        self.assertNotIn(b['lake'], actual)

    def test_unowned_paths_outputs_and_resource_overrides_refused(self):
        root = Path('/bounded-case'); b = binding(root); worker = root / 'worker'
        variants = [
            ['env', 'LEAN_PATH=/old/workspace/.lake/build/lib/lean', b['lake'], 'env', 'lean', '/x.lean'],
            [b['lake'], 'env', 'lean', '-M6144', '/x.lean'],
            [b['lake'], 'env', 'lean', '-j8', '/x.lean'],
            [b['lake'], 'env', 'lean', '-DElab.async=true', '/x.lean'],
            [b['lake'], 'env', 'lean', '-o', '/foreign/Old.olean', '/x.lean'],
            [b['lake'], 'build', 'Old.Cached.Proof'],
            ['env', 'LD_PRELOAD=foreign', b['lake'], 'env', 'lean', '/x.lean']]
        for argv in variants:
            with self.subTest(argv=argv), self.assertRaises(ValueError):
                F.bounded_command(argv, b, worker, root / 'entry.py', root / 'binding.json')

    def test_library_build_and_queries_are_actual_hash_verifier_commands(self):
        root = Path('/bounded-case'); b = binding(root)
        for original, option in (([b['lake'], 'build', 'Pinwheel.Core'], '--verify-stage'),
                                 ([b['lake'], 'env', 'which', 'lean'], '--compiler-path'),
                                 ([b['lake'], 'env', 'printenv', 'LEAN_PATH'], '--compiler-search')):
            actual = F.bounded_command(original, b, root / 'worker', root / 'entry.py', root / 'binding.json')
            self.assertEqual(actual, [b['python'], '-B', str(root / 'entry.py'), option, str(root / 'binding.json')])

    def test_worker_helper_provider_restored_after_success_and_failure(self):
        def original(): return types.SimpleNamespace(load_helpers=lambda root: types.SimpleNamespace(Commands=object))
        gate = types.SimpleNamespace(helpers=original)
        root = Path('/bounded-case'); b = binding(root)
        with ENTRY.worker_hooks(gate, b, {'path': str(root / 'binding.json')}, {'worker_out': str(root / 'worker')}):
            self.assertIsNot(gate.helpers, original)
        self.assertIs(gate.helpers, original)
        with self.assertRaises(RuntimeError):
            with ENTRY.worker_hooks(gate, b, {'path': str(root / 'binding.json')}, {'worker_out': str(root / 'worker')}):
                raise RuntimeError('probe')
        self.assertIs(gate.helpers, original)

    def test_master_dispatch_uses_frozen_selected_adapter_and_original_producer(self):
        class FakeCommands:
            def __init__(self, *args, **kwargs): self.records = []
            def __call__(self, argv, label, **options):
                self.records.append(dict(argv=list(map(str, argv)), label=label))
                return 'no Native fixture'
        def original():
            return types.SimpleNamespace(write_json=ENTRY.dump,
                load_helpers=lambda root: types.SimpleNamespace(Commands=FakeCommands))
        gate = types.SimpleNamespace(helpers=original)
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve(); state = {}; config_path = root / 'worker-config.json'
            cfg = dict(stage='components', source_commit='a' * 40, producer_commit='a' * 40,
                       snapshot=str(root / 'selected'), tool_paths={'python': '/fixture/python'})
            fake_binding = dict(adapter_source_sha256={n: F.sha(ROOT / n) for n in F.ADAPTERS})
            with patch.object(F, 'create_binding', return_value=fake_binding):
                with ENTRY.master_hooks(gate, root / 'foundation.json', root / 'runtime.json', state):
                    helper = gate.helpers(); helper.write_json(config_path, cfg)
                    command = helper.load_helpers(ROOT).Commands()
                    result = command(['/fixture/python', '-B', str(root / 'producer/scripts/check-streaming-uart.py'),
                                      '--worker-config', str(config_path)], 'fresh-continuation-worker')
                    actual = command.records[-1]['argv']
                    self.assertEqual(result, 'no Native fixture')
                    self.assertEqual(actual[2], str(root / 'selected/scripts/check-streaming-ready-fresh.py'))
                    self.assertEqual(actual[-2:], ['--producer-root', str(root / 'producer')])
                    self.assertEqual(cfg['fresh_foundation'], state['marker'])
            self.assertIs(gate.helpers, original)

    def test_preuse_requested_and_actual_journals_must_close_exactly(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve(); b = binding(root); worker = root / 'worker'; proof = worker / 'proof'
            proof.mkdir(parents=True)
            source = proof / 'Fresh.lean'; source.write_text('theorem fixture : True := True.intro')
            requested = ['env', 'LEAN_PATH=' + str(proof), b['lake'], 'env', 'lean', '-o',
                         str(proof / 'Fresh.olean'), str(source)]
            marker = str(root / 'binding.json')
            actual = F.bounded_command(requested, b, worker, Path(b['candidate_root']) / 'scripts/check-streaming-ready-fresh.py', marker)
            command = dict(label='Fresh', argv=actual, expected_failure=False, exit_code=0)
            row = dict(label='Fresh', requested_argv=requested, actual_argv=actual, record=command, expected_failure=False)
            intent = dict(index=0, label='Fresh', argv=requested, options={})
            self.assertTrue(F.validate_command_intents([intent], [command], [row], b, worker, marker))
            for mutation in ('missing', 'wrong-request', 'wrong-actual', 'wrong-index', 'wrong-negative'):
                i, c, r = deepcopy(intent), deepcopy(command), deepcopy(row)
                if mutation == 'wrong-request': i['argv'] = ['/old/compiler']
                elif mutation == 'wrong-actual': c['argv'] = requested
                elif mutation == 'wrong-index': i['index'] = False
                elif mutation == 'wrong-negative': r['expected_failure'] = True
                with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                    F.validate_command_intents([i], [c], [] if mutation == 'missing' else [r], b, worker, marker)
    def test_duplicate_json_keys_refused(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / 'binding.json'; path.write_text('{"passed":true,"passed":false}')
            with self.assertRaises(ValueError): F.read(path)

    def test_incomplete_runtime_companion_cannot_be_promoted(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name); foundation = root / 'foundation.json'; foundation.write_text('{}')
            runtime = root / 'runtime.json'
            for changed in ({'passed': 1}, {'passed': True, 'status': 'running'}, {'passed': True, 'status': 'completed', 'timed_out': True}):
                runtime.write_text(json.dumps({'schema': 'pinwheel.streaming-tt-fresh-foundation-runtime.v1', **changed}))
                with self.subTest(changed=changed), self.assertRaises(ValueError):
                    F.verify_runtime(runtime, foundation, {})

    def test_complete649_binding_regenerates_and_stages_only_positive_objects(self):
        with tempfile.TemporaryDirectory() as name:
            candidate, report, runtime, tools, packet = full_foundation_fixture(Path(name))
            with patch.object(F, 'verify_runtime', return_value={'source_commit': 'a' * 40, 'committed_input_sha256': packet['source_sha256']}):
                actual = F.create_binding(report, runtime, candidate, 'b' * 40, tools)
                self.assertEqual(len(actual['modules']), 649)
                self.assertEqual(len(actual['positive_library_artifact_sha256']), 1298)
                self.assertEqual(set(actual['excluded_negative_control_artifact_sha256']), {F.CONTROL})
                self.assertTrue(F.verify_binding(actual))
                staged = F.stage_library(actual, candidate)
                self.assertEqual(len(F.manifest(staged)), 1298)
                self.assertFalse((staged / F.CONTROL).exists())

    def test_source_projection_native_outcomes_and_missing_logs_refused(self):
        with tempfile.TemporaryDirectory() as name:
            candidate, report, runtime, tools, original = full_foundation_fixture(Path(name))
            variants = []
            changed = deepcopy(original); changed['source_sha256'].pop('scripts/process_group.py'); variants.append(changed)
            changed = deepcopy(original); changed['passed'] = 1; variants.append(changed)
            changed = deepcopy(original); changed['commands'][7]['exit_code'] = 1; variants.append(changed)
            changed = deepcopy(original); changed['commands'][7]['exit_code'] = False; variants.append(changed)
            changed = deepcopy(original); changed['unused_private_axiom_rejected'] = False; variants.append(changed)
            changed = deepcopy(original); changed['commands'][3], changed['commands'][4] = changed['commands'][4], changed['commands'][3]; variants.append(changed)
            with patch.object(F, 'verify_runtime', return_value={'source_commit': 'a' * 40, 'committed_input_sha256': original['source_sha256']}):
                for changed in variants:
                    report.write_text(json.dumps(changed))
                    with self.subTest(change=len(variants)), self.assertRaises(ValueError):
                        F.create_binding(report, runtime, candidate, 'b' * 40, tools)
                report.write_text(json.dumps(original))
                (report.parent / 'build-Pinwheel.M000.log').unlink()
                with self.assertRaises(ValueError): F.create_binding(report, runtime, candidate, 'b' * 40, tools)

    def test_actual_changed_consumed_source_and_old_extra_object_refused(self):
        with tempfile.TemporaryDirectory() as name:
            candidate, report, runtime, tools, original = full_foundation_fixture(Path(name))
            source = candidate / 'Pinwheel/M000.lean'; old = source.read_text(); source.write_text('changed width')
            with patch.object(F, 'verify_runtime', return_value={'source_commit': 'a' * 40, 'committed_input_sha256': original['source_sha256']}):
                with self.assertRaises(ValueError): F.create_binding(report, runtime, candidate, 'b' * 40, tools)
                source.write_text(old)
                library = Path(original['retained_library']); (library / 'OldProof.olean').write_text('old')
                with self.assertRaises(ValueError): F.create_binding(report, runtime, candidate, 'b' * 40, tools)

    def test_pinned_namespace_shadow_and_duplicate_generated_modules_refused(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name).resolve(); worker = root / 'worker'; a = worker / 'a'; b = worker / 'b'
            a.mkdir(parents=True); b.mkdir()
            (a / 'Fresh.lean').write_text('fresh')
            self.assertTrue(F.generated_paths_owned([a, b], worker))
            (b / 'Fresh.olean').write_text('duplicate old object')
            with self.assertRaises(ValueError): F.generated_paths_owned([a, b], worker)
            (b / 'Fresh.olean').unlink()
            for module in ('Pinwheel/Core.olean', 'Std.olean', 'Init.lean', 'Lean.olean.private', 'Lake/Fake.olean'):
                path = a / module; path.parent.mkdir(parents=True, exist_ok=True); path.write_text('shadow')
                with self.subTest(module=module), self.assertRaises(ValueError): F.generated_paths_owned([a], worker)
                path.unlink()


if __name__ == '__main__': unittest.main()
