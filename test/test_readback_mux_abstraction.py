import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("mux_abstraction", ROOT / "scripts/readback_mux_abstraction.py")
mux = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mux)


def var(width, index):
    return width, "var", (), index


def lit(width, value):
    return width, "lit", (), value


def choose(condition, yes, no):
    return yes[0], "mux", (condition, yes, no), None


def example():
    data, other = var(8, 0), var(8, 1)
    condition = 1, "eq", (data, lit(8, 0)), None
    left = choose(condition, data, other)
    right = choose(condition, data, choose(condition, data, other))
    return {"left": left, "right": right, "variables": ((8, "input", "data"), (8, "input", "other"))}


class MuxAbstractionTests(unittest.TestCase):
    def test_generalizes_predicate_and_keeps_exact_data_leaves(self):
        pair = example()
        plan = mux.suggest(pair)
        self.assertIsNotNone(plan)
        self.assertEqual(plan.bits, 1)
        self.assertEqual(plan.leaves, (var(8, 0), var(8, 1)))
        self.assertEqual(plan.tag_width, 1)
        self.assertEqual(mux._instantiate(plan.pair["left"], plan.arguments), plan.left_shadow)
        self.assertEqual(mux._instantiate(plan.pair["right"], plan.arguments), plan.right_shadow)

    def test_rejects_data_or_and_demorgan(self):
        pair = example()
        for op, children in (("or", (pair["left"], pair["right"])),
                             ("not", ((8, "and", (pair["left"], pair["right"]), None),))):
            changed = {**pair, "left": (8, op, children, None)}
            self.assertIsNone(mux.suggest(changed))

    def test_rejects_width_mismatch_and_large_leaf_set(self):
        pair = example()
        self.assertIsNone(mux.suggest({**pair, "right": lit(1, 0)}))
        self.assertIsNone(mux.suggest(pair, max_leaves=1))

    def test_bit_budget_is_hard_limit(self):
        pair = example()
        left = choose(var(1, 2), pair["left"], lit(8, 0))
        right = choose(var(1, 2), pair["right"], lit(8, 0))
        changed = {**pair, "left": left, "right": right,
                   "variables": pair["variables"] + ((1, "input", "enable"),)}
        self.assertIsNone(mux.suggest(changed, max_bits=1))
        self.assertEqual(mux.suggest(changed, max_bits=2).bits, 2)

    def test_requires_exact_instantiation_before_emission(self):
        pair = example()
        plan = mux.suggest(pair)
        altered = plan._replace(left_shadow=plan.right_shadow)
        with self.assertRaises(ValueError):
            mux.lean_lemmas(pair, altered, "local_test", repr)

    def test_emits_kernel_decision_and_structural_lifting(self):
        pair = example()
        source = mux.lean_lemmas(pair, mux.suggest(pair), "local_test", repr)
        self.assertIn("theorem local_test (x0 : BitVec 8) (x1 : BitVec 8)", source)
        self.assertIn("decide +kernel", source)
        self.assertIn("theorem local_test_map_mux", source)
        self.assertIn("hl.symm.trans ((congrArg lookup h).trans hr)", source)
        self.assertNotIn("native_decide", source)
        self.assertNotIn("sorry", source)

    def test_limits_must_be_positive_integers(self):
        for kwargs in ({"max_bits": 0}, {"max_bits": True}, {"max_leaves": -1}):
            with self.assertRaises(ValueError):
                mux.suggest(example(), **kwargs)


if __name__ == "__main__":
    unittest.main()
