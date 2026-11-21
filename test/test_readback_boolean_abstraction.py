"""Portable checks of sound abstraction/instantiation, not theorem acceptance."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import readback_boolean_abstraction as abstraction


def var(index, width=1): return width, "var", (), index
def literal(value, width=1): return width, "lit", (), value
def binary(op, left, right, width=1): return width, op, (left, right), None
def negate(value): return value[0], "not", (value,), None


def request(index):
    return binary("and", var(index * 2), binary("eq", var(index * 2 + 1, 17), literal(3, 17)))


class BooleanAbstractionTests(unittest.TestCase):
    def pair(self, left, right, variables=()):
        return {"left": left, "right": right, "variables": variables}

    def test_maximal_request_cut_and_consistent_occurrences(self):
        q = request(0)
        pair = self.pair(binary("and", q, q), q)
        # A whole-side cut is excluded; use a nontrivial outer Boolean control.
        pair = self.pair(binary("and", q, var(9)), binary("and", var(9), q))
        plan = abstraction.suggest(pair)
        self.assertIsNotNone(plan)
        self.assertEqual(plan.bits, 2)
        self.assertEqual(plan.cuts, (q,))
        self.assertEqual(abstraction.substitute_variables(plan.pair["left"], plan.arguments), pair["left"])
        self.assertEqual(abstraction.substitute_variables(plan.pair["right"], plan.arguments), pair["right"])

    def test_pure_boolean_correlations_are_not_abstracted(self):
        q, reset = request(0), var(8)
        pair = self.pair(binary("and", q, negate(reset)), binary("and", negate(reset), q))
        plan = abstraction.suggest(pair)
        self.assertEqual(plan.cuts, (q,))
        self.assertIn(reset, plan.arguments)
        self.assertNotIn(negate(reset), plan.arguments)

    def test_output_and_remaining_wide_variables_are_rejected(self):
        q = request(0)
        self.assertIsNone(abstraction.suggest(self.pair(binary("and", q, q, 8), literal(0, 8))))
        left = binary("and", q, binary("eq", var(9, 17), literal(0, 17)))
        right = binary("and", q, binary("eq", var(9, 17), literal(1, 17)))
        self.assertIsNone(abstraction.suggest(self.pair(left, right)))

    def test_bit_budget_bounds_kernel_enumeration(self):
        q = request(0)
        pair = self.pair(binary("and", q, var(8)), binary("and", var(8), q))
        self.assertIsNone(abstraction.suggest(pair, max_bits=1))
        self.assertEqual(abstraction.suggest(pair, max_bits=2).bits, 2)
        with self.assertRaises(ValueError): abstraction.suggest(pair, max_bits=0)

    def test_identical_or_no_shared_wide_predicate_returns_none(self):
        q = request(0)
        self.assertIsNone(abstraction.suggest(self.pair(q, q)))
        self.assertIsNone(abstraction.suggest(self.pair(var(0), negate(var(0)))))

    def test_emitter_preserves_original_signature_and_uses_kernel(self):
        q = request(0)
        pair = self.pair(binary("and", q, var(2)), binary("and", var(2), q),
                         ((1, "input", "v"), (17, "input", "data"), (1, "input", "r")))
        plan = abstraction.suggest(pair)
        text = abstraction.lean_lemmas(pair, plan, "local_7", repr)
        self.assertIn("theorem local_7 (x0 : BitVec 1) (x1 : BitVec 17) (x2 : BitVec 1)", text)
        self.assertIn("decide +kernel", text)
        self.assertIn("exact local_7_boolean", text)
        for unsafe in ("native_decide", "bv_decide", "sorry", "axiom "):
            self.assertNotIn(unsafe, text)
        wrong = self.pair(pair["right"], literal(0), pair["variables"])
        with self.assertRaises(ValueError): abstraction.lean_lemmas(wrong, plan, "bad", repr)


if __name__ == "__main__":
    unittest.main()
