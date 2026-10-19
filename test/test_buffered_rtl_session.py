"""Isolated provenance refusal controls; no CAD, Lean build or qualified gate."""
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import types
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('buffered_rtl_session_driver',
    ROOT / 'scripts/check-buffered-rtl-session.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class GitFixture:
    def __init__(self, root, mode='frontend'):
        self.root = Path(root)
        for relative in gate.REQUIRED | (gate.FULL_REQUIRED if mode == 'full' else frozenset()):
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('import Init\n' if path.suffix == '.lean' else '# committed fixture\n')
        (self.root / 'Pinwheel').mkdir(exist_ok=True)
        (self.root / 'Pinwheel.lean').write_text('import Pinwheel.Dependency\n')
        (self.root / 'Pinwheel/Dependency.lean').write_text('import Init\n')
        self.git('init', '-q')
        self.git('add', '.')
        self.git('-c', 'user.name=Provenance Fixture', '-c', 'user.email=fixture@example.invalid',
                 '-c', 'commit.gpgsign=false', '-c', 'core.hooksPath=/dev/null', 'commit', '-qm', 'fixture')
        self.head = self.git('rev-parse', 'HEAD').strip()
        self.tree = gate.parse_tree(self.git('ls-tree', '-r', '-z', self.head))
        self.paths = gate.select_inputs(self.tree, mode)
        self.algorithm = self.git('rev-parse', '--show-object-format').strip()

    def git(self, *args):
        environment = dict(os.environ, GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL='/dev/null')
        return subprocess.check_output(['git', *args], cwd=self.root, env=environment,
                                       text=True, timeout=30)


class BufferedRtlProvenanceTests(unittest.TestCase):
    def test_rtl_inputs_are_frozen_before_command_and_parser(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-preuse-') as directory:
            root = Path(directory)
            sv = root / 'candidate.sv'
            sv.write_text('module candidate; endmodule\n')
            report, consumed = {}, []
            freeze = lambda paths: gate.freeze_inputs(report, root, paths)
            def run(command, label, **options):
                self.assertEqual(report['proof_input_sha256_before']['candidate.sv'], gate.digest(sv))
                self.assertIn('import.ys', report['proof_input_sha256_before'])
                (root / 'import.json').write_text('{}')
                consumed.append('command')
                return ''
            def parse(path):
                self.assertEqual(report['proof_input_sha256_before']['import.json'], gate.digest(path))
                consumed.append('parser')
                return 'graph'
            rb = types.SimpleNamespace(TOP='candidate', read_rtl=parse)
            result, _ = gate.import_rtl(run, rb, {'yosys': '/selected/yosys'}, root, sv,
                                        'import', freeze=freeze)
            self.assertEqual(result, 'graph')
            self.assertEqual(consumed, ['command', 'parser'])
            gate.assert_hashes(root, report['proof_input_sha256_before'])
            (root / 'import.json').write_text('{"changed":"after use"}')
            with self.assertRaisesRegex(RuntimeError, 'Frozen artifact changed'):
                gate.assert_hashes(root, report['proof_input_sha256_before'])

    def test_a_reused_generated_input_cannot_replace_its_first_hash(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-proof-reuse-') as directory:
            root = Path(directory)
            source = root / 'Emitter.lean'
            source.write_text('import Init\n')
            report = {}
            gate.full_module().register_inputs(report, gate, root, [source])
            first = dict(report['proof_input_sha256_before'])
            source.write_text('import Init\n-- altered after execution\n')
            with self.assertRaisesRegex(RuntimeError, 'Already frozen proof input changed'):
                gate.full_module().register_inputs(report, gate, root, [source])
            self.assertEqual(report['proof_input_sha256_before'], first)

    def test_component_receipt_cannot_qualify_full_session(self):
        schema, targets, full = gate.mode_contract('frontend')
        child = dict(schema=schema, source_commit='selected', source_sha256={'source': 'hash'},
                     required_targets=targets, full_session_proved=full, passed=True)
        gate.check_worker_contract(child, 'frontend', 'selected', {'source': 'hash'})
        with self.assertRaisesRegex(RuntimeError, 'selected full contract'):
            gate.check_worker_contract(child, 'full', 'selected', {'source': 'hash'})
        # Relabeling the schema/flag still cannot replace the missing theorem targets.
        relabeled = dict(child, schema=gate.mode_contract('full')[0], full_session_proved=True)
        with self.assertRaisesRegex(RuntimeError, 'selected full contract'):
            gate.check_worker_contract(relabeled, 'full', 'selected', {'source': 'hash'})
        complete = dict(relabeled, required_targets=gate.mode_contract('full')[1])
        gate.check_worker_contract(complete, 'full', 'selected', {'source': 'hash'})
        for key, wrong in [('source_commit', 'other'), ('source_sha256', {}), ('passed', False)]:
            with self.subTest(field=key), self.assertRaises(RuntimeError):
                gate.check_worker_contract(dict(complete, **{key: wrong}), 'full',
                                           'selected', {'source': 'hash'})

    def test_full_gate_requires_committed_physical_and_generator_inputs(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-full-membership-') as directory:
            fixture = GitFixture(directory, 'full')
            self.assertTrue(gate.FULL_REQUIRED <= set(fixture.paths))
            for relative in ('physical/buffered_sram_memory.sv', 'scripts/buffered_rtl_session_full.py'):
                tree = dict(fixture.tree)
                del tree[relative]
                with self.subTest(missing=relative), self.assertRaisesRegex(RuntimeError, 'not committed'):
                    gate.select_inputs(tree, 'full')
            path = Path(directory) / 'physical/buffered_sram_serial_wrapper.sv'
            path.write_text('uncommitted replacement wrapper\n')
            with self.assertRaisesRegex(RuntimeError, 'differs from selected committed source'):
                gate.source_identity(directory, fixture.tree, fixture.paths, fixture.algorithm)

    def test_selected_git_archive_and_changed_working_dependency(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-provenance-') as directory:
            root = Path(directory) / 'repo'
            root.mkdir()
            fixture = GitFixture(root)
            expected = gate.source_identity(root, fixture.tree, fixture.paths, fixture.algorithm)
            archive = subprocess.check_output(['git', 'archive', fixture.head, '--', *fixture.paths],
                                              cwd=root, timeout=30)
            snapshot = Path(directory) / 'snapshot'
            snapshot.mkdir()
            with tarfile.open(fileobj=io.BytesIO(archive)) as bundle:
                bundle.extractall(snapshot, filter='data')
            gate.assert_fresh_snapshot(snapshot)
            gate.check_source_hashes(snapshot, expected)
            # A changed unrelated document is outside this component's input set.
            (root / 'notes.md').write_text('unrelated working note\n')
            self.assertEqual(gate.source_identity(root, fixture.tree, fixture.paths, fixture.algorithm), expected)
            (root / 'Pinwheel/Dependency.lean').write_text('import Init\n-- changed after intake\n')
            with self.assertRaisesRegex(RuntimeError, 'differs from selected committed source'):
                gate.source_identity(root, fixture.tree, fixture.paths, fixture.algorithm)
            (snapshot / 'Pinwheel/Dependency.lean').write_text('changed archive source\n')
            with self.assertRaisesRegex(RuntimeError, 'Frozen source changed'):
                gate.check_source_hashes(snapshot, expected)

    def test_required_driver_and_new_helper_must_be_committed(self):
        with self.assertRaisesRegex(RuntimeError, 'not committed'):
            gate.select_inputs({})
        with tempfile.TemporaryDirectory(prefix='unqualified-provenance-') as directory:
            fixture = GitFixture(directory)
            driver = Path(directory) / gate.DRIVER
            driver.write_text('# uncommitted driver bytes\n')
            with self.assertRaisesRegex(RuntimeError, 'differs from selected committed source'):
                gate.source_identity(directory, fixture.tree, fixture.paths, fixture.algorithm)

    def test_generated_proof_closure_refuses_injected_and_changed_dependencies(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-proof-closure-') as directory:
            root = Path(directory)
            source, generated = root / 'snapshot', root / 'generated'
            (source / 'Pinwheel').mkdir(parents=True)
            generated.mkdir()
            committed = source / 'Pinwheel/Used.lean'
            committed.write_text('import Init\n')
            main = generated / 'Certificate.lean'
            main.write_text('import Pinwheel.Used\nimport Lean\n')
            inputs = {'Pinwheel/Used.lean': gate.digest(committed)}
            artifacts = {'Certificate.lean': gate.digest(main)}
            closure = gate.proof_closure(source, generated, ['Certificate'], inputs, artifacts)
            self.assertEqual(closure['Pinwheel.Used']['origin'], 'committed')
            self.assertEqual(closure['Certificate']['origin'], 'generated')
            rogue = source / 'Pinwheel/Rogue.lean'
            rogue.write_text('import Init\n')
            main.write_text('import Pinwheel.Rogue\n')
            artifacts['Certificate.lean'] = gate.digest(main)
            with self.assertRaisesRegex(RuntimeError, 'Uncommitted or changed proof dependency'):
                gate.proof_closure(source, generated, ['Certificate'], inputs, artifacts)
            main.write_text('import NotIndexed\n')
            artifacts['Certificate.lean'] = gate.digest(main)
            with self.assertRaisesRegex(RuntimeError, 'Missing indexed proof dependency'):
                gate.proof_closure(source, generated, ['Certificate'], inputs, artifacts)
            main.write_text('import Pinwheel.Used\n')
            with self.assertRaisesRegex(RuntimeError, 'Unfrozen generated proof dependency'):
                gate.proof_closure(source, generated, ['Certificate'], inputs, artifacts)

    def test_multiple_generated_directories_cannot_shadow_a_module(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-proof-closure-') as directory:
            root = Path(directory)
            source = root / 'snapshot'
            source.mkdir()
            one, two = root / 'one', root / 'two'
            one.mkdir()
            two.mkdir()
            for path in (one / 'Shared.lean', two / 'Shared.lean'):
                path.write_text('import Init\n')
            with self.assertRaisesRegex(RuntimeError, 'Ambiguous generated proof dependency'):
                gate.proof_closure(source, [one, two], ['Shared'], {},
                                   {'Shared.lean': gate.digest(one / 'Shared.lean')})

    def test_fresh_cache_and_frozen_artifact_guards(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-cache-') as directory:
            root = Path(directory)
            gate.assert_fresh_snapshot(root)
            (root / '.lake').mkdir()
            with self.assertRaisesRegex(RuntimeError, 'prior Git/build/cache'):
                gate.assert_fresh_snapshot(root)
            (root / '.lake').rmdir()
            artifact = root / 'Certificate.lean'
            artifact.write_text('import Init\n')
            frozen = gate.file_hashes(root)
            artifact.write_text('import Init\n-- altered after generation\n')
            with self.assertRaisesRegex(RuntimeError, 'Frozen artifact changed'):
                gate.assert_hashes(root, frozen)

    def test_payload_and_runtime_changes_are_observed_beyond_wrappers(self):
        with tempfile.TemporaryDirectory(prefix='unqualified-tool-identity-') as directory:
            root = Path(directory)
            circt, oss, lean = root / 'firtool-fixture', root / 'oss-fixture', root / 'lean-fixture'
            paths = {}
            for key, path in [('circt', circt / 'bin/circt-opt'), ('yosys', oss / 'bin/yosys'),
                              ('solver', oss / 'bin/z3'), ('lean', lean / 'bin/lean'),
                              ('lake', lean / 'bin/lake'), ('python', root / 'python')]:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b'\xcf\xfa\xed\xfe native fixture' if key == 'lean' else key.encode())
                paths[key] = str(path)
            for name in ('yosys', 'z3', 'realpath'):
                path = oss / 'libexec' / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('payload ' + name)
            library = oss / 'lib/libfixture.dylib'
            library.parent.mkdir(parents=True)
            library.write_text('runtime library')
            manifest = {'packages': {}}
            for key, package in [('circt', circt), ('oss-cad-suite', oss)]:
                archive = root / (key + '.archive')
                archive.write_text('pinned ' + key)
                manifest['packages'][key] = dict(directory=package.name, archive=archive.name,
                                                  sha256=gate.digest(archive))
            before = gate.tool_identity(paths, manifest)
            wrapper_hash = before['files'][str(oss / 'bin/yosys')]['sha256']
            (oss / 'libexec/yosys').write_text('altered real payload, unchanged wrapper')
            after = gate.tool_identity(paths, manifest)
            self.assertEqual(wrapper_hash, after['files'][str(oss / 'bin/yosys')]['sha256'])
            self.assertNotEqual(before, after)
            extra = oss / 'lib/new-runtime.dylib'
            extra.write_text('new runtime')
            self.assertNotEqual(set(after['files']), set(gate.tool_identity(paths, manifest)['files']))
            extra.unlink()
            outside = root / 'outside.dylib'
            outside.write_text('unindexed external runtime')
            extra.symlink_to(outside)
            with self.assertRaisesRegex(RuntimeError, 'escapes its selected package'):
                gate.tool_identity(paths, manifest)

    def test_versions_and_override_refusal(self):
        manifest = {'packages': {'circt': {'release': 'firtool-1.159.0'}}}
        versions = dict(lean='Lean (version 4.33.1, aarch64-apple-darwin, Release)',
                        circt='CIRCT firtool-1.159.0',
                        yosys='Yosys 0.69+24 (git sha1 d0e71cfb7-dirty, Release)',
                        solver='Z3 version 4.15.5 - 64 bit')
        gate.check_versions(versions, '4.33.1', manifest)
        for name, wrong in [('lean', 'Lean (version 4.33.0, Release)'),
                            ('circt', 'CIRCT firtool-1.158.0'), ('yosys', 'Yosys 0.69+25'),
                            ('solver', 'Z3 version 4.15.6 - 64 bit')]:
            with self.subTest(tool=name), self.assertRaises(RuntimeError):
                gate.check_versions(dict(versions, **{name: wrong}), '4.33.1', manifest)
        for name in ('LEAN_PATH', 'LAKE_PACKAGES_DIR', 'DYLD_LIBRARY_PATH', 'LD_PRELOAD'):
            with self.subTest(override=name), self.assertRaises(RuntimeError):
                gate.check_environment({name: '/borrowed/cache'})

    def test_bounded_failure_log_and_fresh_tag_are_preserved(self):
        module, _ = gate.load_commands(ROOT)
        with tempfile.TemporaryDirectory(prefix='unqualified-failure-') as directory:
            out = module.fresh_directory(directory, 'receipt')
            run = module.Commands(ROOT, out, default_timeout=10)
            with self.assertRaisesRegex(RuntimeError, 'smoke-failure:'):
                run([sys.executable, '-c', 'print("retained failure detail"); raise SystemExit(7)'],
                    'smoke-failure')
            self.assertEqual(run.records[0]['exit_code'], 7)
            self.assertIn('retained failure detail', (out / 'smoke-failure.log').read_text())
            with self.assertRaises(FileExistsError):
                module.fresh_directory(directory, 'receipt')
            self.assertTrue((out / 'smoke-failure.log').exists())


if __name__ == '__main__':
    unittest.main()
