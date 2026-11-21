import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("union_abstraction", ROOT / "scripts/readback_union_abstraction.py")
union = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(union)


def node(width, op, *children, value=None):
    return width, op, children, value


def example():
    a, b, c = node(8, "var", value=0), node(8, "var", value=1), node(1, "var", value=2)
    zero = node(8, "lit", value=0)
    left = node(8, "mux", c, node(8, "or", a, b), zero)
    right = node(8, "or", node(8, "mux", c, a, zero), node(8, "mux", c, b, zero))
    return {"left": left, "right": right,
            "variables": ((8, "input", "a"), (8, "input", "b"), (1, "input", "c"))}


class UnionAbstractionTests(unittest.TestCase):
    def test_union_uses_distinct_one_hot_labels_and_empty_zero(self):
        plan = union.suggest(example())
        self.assertEqual(plan.bits, 1)
        self.assertEqual(len(plan.leaves), 2)
        self.assertEqual(plan.left_shadow[0], 2)
        leaves = plan.left_shadow[2][1][2]
        self.assertEqual([leaf[3] for leaf in leaves], [1, 2])
        self.assertEqual(plan.left_shadow[2][2][3], 0)

    def test_demorgan_and_double_negation_are_structural(self):
        pair = example()
        a, b = pair["right"][2]
        dm = node(8, "not", node(8, "and", node(8, "not", a), node(8, "not", b)))
        plan = union.suggest({**pair, "right": dm})
        self.assertIsNotNone(plan)
        self.assertEqual(plan.right_shadow, union.suggest(pair).right_shadow)

    def test_arbitrary_and_xor_add_and_complement_are_rejected(self):
        pair = example()
        a, b = pair["right"][2]
        for op, args in (("and", (a, b)), ("xor", (a, b)), ("add", (a, b)), ("not", (a,))):
            self.assertIsNone(union.suggest({**pair, "right": node(8, op, *args)}))

    def test_label_interpretation_preserves_union_for_arbitrary_payloads(self):
        data = [0b1010, 0b1100, 0b0001]
        def interpret(mask):
            result = 0
            for k, value in enumerate(data):
                if mask & (1 << k):
                    result |= value
            return result
        for a in range(8):
            for b in range(8):
                self.assertEqual(interpret(a | b), interpret(a) | interpret(b))

    def test_budget_and_zero_only_network(self):
        pair = example()
        self.assertIsNone(union.suggest(pair, max_leaves=1))
        zero = node(8, "lit", value=0)
        self.assertIsNone(union.suggest({**pair, "left": zero, "right": node(8, "or", zero, zero)}))
        for kwargs in ({"max_bits": False}, {"max_leaves": 0}):
            with self.assertRaises(ValueError):
                union.suggest(pair, **kwargs)

    def test_altered_plan_rejected_before_emission(self):
        pair = example()
        plan = union.suggest(pair)
        with self.assertRaises(ValueError):
            union.lean_lemmas(pair, plan._replace(right_shadow=plan.left_shadow), "local_test", repr)

    def test_generated_proof_preserves_original_statement_and_proves_or_lift(self):
        pair = example()
        source = union.lean_lemmas(pair, union.suggest(pair), "local_test", repr)
        self.assertIn("theorem local_test (x0 : BitVec 8) (x1 : BitVec 8) (x2 : BitVec 1)", source)
        self.assertIn("theorem local_test_interpret_or", source)
        self.assertIn("BitVec.getLsbD_or", source)
        self.assertIn("decide +kernel", source)
        self.assertIn("hl.symm.trans ((congrArg lookup h).trans hr)", source)
        self.assertNotIn("native_decide", source)
        self.assertNotIn("sorry", source)


if __name__ == "__main__":
    unittest.main()
