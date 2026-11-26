"""Reject incomplete or cyclic source coverage before a serial kernel build."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
spec = importlib.util.spec_from_file_location('foundation_serial', ROOT/'scripts/check-foundation.py')
F = importlib.util.module_from_spec(spec); spec.loader.exec_module(F)
spec = importlib.util.spec_from_file_location('foundation_snapshot_serial', ROOT/'scripts/check-foundation-snapshot.py')
S = importlib.util.module_from_spec(spec); spec.loader.exec_module(S)
import lean_libraries as L


class SerialCoverage(unittest.TestCase):
    def test_resource_override_keeps_serial_execution_and_refuses_unbounded_memory(self):
        self.assertEqual(F.serial_limits(), ['-M4096', '-j1', '-DElab.async=false'])
        self.assertEqual(F.serial_limits(2048), ['-M2048', '-j1', '-DElab.async=false'])
        for memory in (0, -1, 255, 6145, True, 4096.0, '4096'):
            with self.subTest(memory=memory), self.assertRaisesRegex(RuntimeError, 'memory'):
                F.serial_limits(memory)

    def fixture(self, root):
        (root/'lakefile.toml').write_text('[[lean_lib]]\nname = "Pinwheel"\n\n'
                                          '[[lean_lib]]\nname = "PinwheelWitness"\n')
        (root/'PinwheelWitness.lean').write_text('import Pinwheel\n')
        (root/'Pinwheel').mkdir()
        (root/'Pinwheel.lean').write_text('import Pinwheel.Parent\n')
        (root/'Pinwheel/Parent.lean').write_text('public import Pinwheel.Child\nimport Lean\n')
        (root/'Pinwheel/Child.lean').write_text('import Lean\n')

    def test_real_default_library_is_complete_and_dependency_ordered(self):
        ordered = F.serial_modules()
        self.assertEqual(len(ordered), F.check_imports())
        self.assertEqual(len({name for name, _ in ordered}), len(ordered))
        names = [name for name, _ in ordered]
        self.assertLess(names.index('Pinwheel'), names.index('PinwheelHardwareLibrary'))
        self.assertIn('Pinwheel.Hardware.StreamingPhysical.Clock', names)
        self.assertIn('Pinwheel.Hardware.Processor.CoreCircuitOutputs', names)
        self.assertNotIn('PinwheelWitness', names)

    def test_public_imports_and_diamonds_are_compiled_once(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); self.fixture(root)
            (root/'Pinwheel.lean').write_text('import Pinwheel.Parent\nimport Pinwheel.Child\n')
            self.assertEqual([name for name, _ in F.serial_modules(root)],
                             ['Pinwheel.Child', 'Pinwheel.Parent', 'Pinwheel'])

    def test_unreachable_module_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); self.fixture(root)
            (root/'Pinwheel/Orphan.lean').write_text('import Lean\n')
            with self.assertRaisesRegex(RuntimeError, 'outside every declared library'):
                F.serial_modules(root)

    def test_second_library_covers_its_files_and_is_built_after_the_default(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); self.fixture(root)
            (root/'lakefile.toml').write_text((root/'lakefile.toml').read_text() +
                                              '\n[[lean_lib]]\nname = "PinwheelExtra"\n')
            (root/'Pinwheel/Extra.lean').write_text('import Pinwheel.Child\n')
            (root/'PinwheelExtra.lean').write_text('import Pinwheel.Extra\n')
            self.assertEqual([name for name, _ in F.serial_modules(root)],
                             ['Pinwheel.Child', 'Pinwheel.Parent', 'Pinwheel', 'Pinwheel.Extra', 'PinwheelExtra'])

    def test_separately_checked_library_counts_for_coverage_only(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); self.fixture(root)
            (root/'PinwheelWitness').mkdir()
            (root/'PinwheelWitness/Slow.lean').write_text('import Pinwheel\n')
            with self.assertRaisesRegex(RuntimeError, 'PinwheelWitness.Slow'):
                F.serial_modules(root)
            (root/'PinwheelWitness.lean').write_text('import PinwheelWitness.Slow\n')
            self.assertNotIn('PinwheelWitness.Slow', [name for name, _ in F.serial_modules(root)])

    def test_audit_imports_every_gated_library(self):
        libs = [('Pinwheel', ['Pinwheel']), ('PinwheelExtra', ['PinwheelExtra'])]
        text = (ROOT/'test/ProofAudit.lean').read_text()
        self.assertIn('import Pinwheel\nimport PinwheelExtra\n', L.audit_source(text, libs))

    def test_cycle_is_rejected_before_compiler_launch(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); self.fixture(root)
            (root/'Pinwheel/Child.lean').write_text('import Pinwheel.Parent\n')
            with self.assertRaisesRegex(RuntimeError, 'Cyclic local Lean imports'):
                F.serial_modules(root)

    def test_inherited_original_project_and_loader_paths_are_refused(self):
        S.check_environment({})
        for key in ('LEAN_PATH', 'LEAN_SYSROOT', 'LAKE_HOME', 'PYTHONPATH', 'DYLD_INSERT_LIBRARIES'):
            with self.subTest(key=key), self.assertRaisesRegex(RuntimeError, 'inherited compiler/cache/loader'):
                S.check_environment({key: '/old-build'})

    def test_retained_snapshot_starts_fresh_survives_failure_and_refuses_reuse(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with self.assertRaisesRegex(RuntimeError, 'controlled failure'):
                with S.snapshot_directory(root, True) as snapshot:
                    self.assertFalse((snapshot / '.lake').exists())
                    (snapshot / 'source.lean').write_text('source')
                    raise RuntimeError('controlled failure')
            self.assertEqual((root / 'snapshot/source.lean').read_text(), 'source')
            with self.assertRaises(FileExistsError):
                with S.snapshot_directory(root, True): pass

    def test_temporary_snapshot_is_removed_after_use(self):
        with S.snapshot_directory(Path('/unused'), False) as snapshot:
            self.assertTrue(snapshot.is_dir())
        self.assertFalse(snapshot.exists())

    def test_retained_library_inventory_includes_sidecars_and_refuses_aliases(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); library = root / '.lake/build/lib/lean'
            library.mkdir(parents=True)
            for name in ('Pinwheel.olean', 'Pinwheel.olean.private', 'Pinwheel.ilean'):
                (library / name).write_text(name)
            self.assertEqual(set(S.library_artifacts(root)),
                             {'Pinwheel.olean', 'Pinwheel.olean.private', 'Pinwheel.ilean'})
            (library / 'alias.olean').symlink_to(library / 'Pinwheel.olean')
            with self.assertRaisesRegex(RuntimeError, 'symbolic alias'): S.library_artifacts(root)


if __name__ == '__main__': unittest.main()
