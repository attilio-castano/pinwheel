"""The witness check covers every witness file and audits with the witness loaded."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('check_witness', ROOT/'scripts/check-witness.py')
W = importlib.util.module_from_spec(spec); spec.loader.exec_module(W)


class WitnessCoverage(unittest.TestCase):
    def fixture(self, root):
        (root/'PinwheelWitness').mkdir()
        (root/'PinwheelWitness.lean').write_text('import PinwheelWitness.A\n')
        (root/'PinwheelWitness/A.lean').write_text('import Pinwheel\nimport PinwheelWitness.B\n')
        (root/'PinwheelWitness/B.lean').write_text('import Lean\n')

    def test_real_library_is_covered(self):
        modules = W.witness_modules()
        self.assertIn('PinwheelWitness', modules)
        self.assertIn('PinwheelWitness.I2CRead', modules)

    def test_reachable_files_are_listed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); self.fixture(root)
            self.assertEqual(W.witness_modules(root),
                             ['PinwheelWitness', 'PinwheelWitness.A', 'PinwheelWitness.B'])

    def test_unimported_file_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); self.fixture(root)
            (root/'PinwheelWitness/Orphan.lean').write_text('import Lean\n')
            with self.assertRaisesRegex(RuntimeError, 'not imported'):
                W.witness_modules(root)

    def test_audit_also_imports_the_witness_library(self):
        text = W.audit_source()
        self.assertIn('import Pinwheel\nimport PinwheelWitness\n', text)
        self.assertTrue(text.rstrip().endswith('#audit_pinwheel'))


if __name__ == '__main__': unittest.main()
