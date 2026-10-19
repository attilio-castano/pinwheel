"""Runtime membership and binding controls; no Lean process is executed."""
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

PATH = Path(__file__).resolve().parents[1] / 'scripts/run-streaming-tt-foundation.py'
SPEC = importlib.util.spec_from_file_location('fresh_foundation_controller', PATH)
CONTROLLER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CONTROLLER)


class RuntimeObservationTests(unittest.TestCase):
    def fixture(self, root):
        prefix = root / 'toolchain'
        binaries = [prefix / 'bin' / name for name in ('lean', 'lake')]
        for binary in binaries:
            binary.parent.mkdir(parents=True, exist_ok=True)
            binary.write_text('binary:' + binary.name)
        library = prefix / 'lib/lean'
        library.mkdir(parents=True)
        (library / 'Init.olean').write_text('stdlib')
        seal = root / 'seal.json'
        seal.write_text(json.dumps({'binaries': {str(p): CONTROLLER.sha(p) for p in binaries}}))
        return prefix, seal, lambda name: str(prefix / 'bin' / name)

    def test_membership_and_resolution_capture_every_runtime_file(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            prefix, seal, which = self.fixture(root)
            with patch.object(CONTROLLER.shutil, 'which', side_effect=which):
                before = CONTROLLER.observe(seal)
                self.assertEqual(len(before), 3)
                extra = prefix / 'lib/lean/Init.olean.private'
                extra.write_text('new-private')
                after = CONTROLLER.observe(seal)
                self.assertNotEqual(before, after)
                self.assertIn(str(extra), after)
                self.assertEqual(after[str(extra)]['bytes'], len('new-private'))
                extra.unlink()
                self.assertEqual(before, CONTROLLER.observe(seal))

    def test_changed_actual_compiler_is_rejected(self):
        with tempfile.TemporaryDirectory() as name:
            prefix, seal, which = self.fixture(Path(name))
            (prefix / 'bin/lean').write_text('wrong binary')
            with patch.object(CONTROLLER.shutil, 'which', side_effect=which), self.assertRaises(ValueError):
                CONTROLLER.observe(seal)

    def test_runtime_directory_alias_is_rejected(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            prefix, seal, which = self.fixture(root)
            target = root / 'external'; target.mkdir()
            (prefix / 'lib/lean/redirected').symlink_to(target, target_is_directory=True)
            with patch.object(CONTROLLER.shutil, 'which', side_effect=which), self.assertRaises(ValueError):
                CONTROLLER.observe(seal)

    def test_file_alias_retains_exact_resolution_and_byte_identity(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            prefix, seal, which = self.fixture(root)
            target = prefix / 'lib/lean/Init.olean'
            alias = prefix / 'lib/lean/Alias.olean'; alias.symlink_to(target)
            with patch.object(CONTROLLER.shutil, 'which', side_effect=which):
                row = CONTROLLER.observe(seal)[str(alias)]
                self.assertEqual(row['resolved'], str(target.resolve()))
                self.assertEqual(row['sha256'], hashlib.sha256(b'stdlib').hexdigest())


if __name__ == '__main__':
    unittest.main()
