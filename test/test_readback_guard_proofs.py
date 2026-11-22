"""Regression tests for proof reconstruction and abstract counterexamples."""
from pathlib import Path
import shutil
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import backend_readback as rb
from readback_guard_proofs import BitGuardProblem, GuardProblem, resolution


class GuardTests(unittest.TestCase):
    def test_rup_requires_conflicting_premises(self):
        clauses = {1: [1], 2: [-1]}
        empty, steps = resolution(clauses, "3 0 1 2 0")
        self.assertEqual(empty, 3)
        self.assertEqual(steps[3][1], {1, 2})
        with self.assertRaisesRegex(ValueError, "did not close"):
            resolution({1: [1]}, "2 0 1 0")
        with self.assertRaisesRegex(ValueError, "Non-unit"):
            resolution({1: [1, 2]}, "2 0 1 0")

    @unittest.skipUnless(shutil.which("lean"), "Lean toolchain required for the SAT selector")
    def test_guard_and_data_faults(self):
        toolchain = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        solver = Path(toolchain) / "bin/cadical"
        guard = (1, "var", (), 0)
        a = (4, "var", (), 1)
        b = (4, "var", (), 2)
        selected = (4, "mux", (guard, a, b), None)
        swapped = (4, "mux", (guard, b, a), None)
        self.assertIsNone(GuardProblem(rb, dict(left=selected, right=swapped)).prove(solver, "bad"))
        # Replacing the lower half of a concatenation must invalidate its lower
        # bits while permitting an independent proof about an unaffected bit.
        original = (8, "concat", (selected, a), None)
        corrupt = (8, "concat", (selected, b), None)
        pair = dict(left=original, right=corrupt)
        self.assertIsNone(BitGuardProblem(rb, pair, 0).prove(solver, "low"))
        self.assertIsNotNone(BitGuardProblem(rb, pair, 7).prove(solver, "high"))


if __name__ == "__main__":
    unittest.main()
