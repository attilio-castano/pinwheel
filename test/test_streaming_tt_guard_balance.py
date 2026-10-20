"""Source contracts and refusal controls for fixed64 guard reassociation."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from streaming_tt_guard_balance import CORE, READY_CORE, FRONTEND, HELPER, HOST, INIT, inspect


def fixture():
    def guard(name, leaf, width):
        return f"def {name} : {width} := (List.finRange 64).foldl (fun acc k => both acc\n  {leaf}) (.lit 1)\n"

    def balanced(name, condition, leaf, width, register):
        return (f"def {condition} (k : Fin 64) : {width} :=\n  {leaf}\n"
                f"def {name} : {width} := BalancedConjunction.sixtyFour {condition}\n\n"
                f"theorem {name}_eval_fold (i : Values Input) (r : {register}) :\n"
                f"    {name}.eval i r = ((List.finRange 64).foldl (fun acc k => both acc\n"
                f"      {leaf}) (.lit 1)).eval i r := by\n"
                f"  exact BalancedConjunction.sixtyFour_eval i r {condition}\n")

    core_leaf = "(either (.inv (.ult (.lit (BitVec.ofNat 7 k.val)) (.input .count)))\n    (.slice k.val 1 (by omega) (.reg .written)))"
    tail_leaf = "(either (.inv (.ult wanted (.lit (BitVec.ofNat 7 (64-k.val)))))\n    (.zero (payload k.val 1 (by omega))))"
    prefix = "import Old\ninductive Register : Nat → Type where\n | written : Register 64\n"
    baseline = {CORE: prefix + guard("covered", core_leaf, "E a 1") + "def countValid := original\n",
                READY_CORE: prefix + guard("covered", core_leaf, "E a 1") + "def countValid := original\n",
                FRONTEND: prefix + guard("tailCanonical", tail_leaf, "E 1") + "def bulkOwner := original\n",
                HOST: "theorem host := by\n  unfold Frontend.tailCanonical\n  done\n",
                INIT: "theorem init := by\n  unfold Core.covered\n  done\n"}
    current = {HELPER: (Path(__file__).resolve().parents[1] / HELPER).read_text(),
               READY_CORE: prefix + "def covered : E a 1 := Streaming.Core.covered\ndef countValid := original\n",
               CORE: prefix.replace("import Old\n", "import Old\nimport Pinwheel.Hardware.BalancedConjunction\n") +
                     balanced("covered", "coveredCondition", core_leaf, "E a 1", "Values (Register a)") + "def countValid := original\n",
               FRONTEND: prefix + balanced("tailCanonical", "tailCondition", tail_leaf, "E 1", "Values Register") + "def bulkOwner := original\n",
               HOST: baseline[HOST].replace("unfold Frontend.tailCanonical", "rw [Frontend.tailCanonical_eval_fold]"),
               INIT: baseline[INIT].replace("unfold Core.covered", "rw [Core.covered_eval_fold]")}
    return current, baseline


class GuardBalanceTests(unittest.TestCase):
    def test_actual_source_tree_and_exact_leaf_preservation(self):
        current, baseline = fixture()
        result = inspect(current, baseline)
        self.assertEqual((result["and_nodes"], result["and_depth"], result["leaves"]), (63, 6, list(range(64))))
        self.assertFalse(result["kernel_proved"])
        self.assertFalse(result["timing_improvement_measured"])
        self.assertFalse(result["native_state_inventory_checked"])

    def test_duplicate_or_missing_tree_leaves_refused(self):
        for old, new in (("(f 7)", "(f 6)"), ("(.band (f 4) (f 5))", "(f 4)")):
            current, baseline = fixture()
            current[HELPER] = current[HELPER].replace(old, new)
            with self.subTest(new=new), self.assertRaises(ValueError):
                inspect(current, baseline)

    def test_serialized_eight_tree_refused_despite_same_leaf_set(self):
        current, baseline = fixture()
        a = current[HELPER].index("  .band")
        b = current[HELPER].index("\ndef sixtyFour")
        expr = "(f 0)"
        for index in range(1, 8):
            expr = f"(.band {expr} (f {index}))"
        current[HELPER] = current[HELPER][:a] + "  " + expr + "\n" + current[HELPER][b:]
        with self.assertRaises(ValueError):
            inspect(current, baseline)

    def test_index_alias_refused(self):
        current, baseline = fixture()
        current[HELPER] = current[HELPER].replace("block.val * 8 + position.val", "block.val * 7 + position.val")
        with self.assertRaises(ValueError):
            inspect(current, baseline)

    def test_actual_guard_operand_mutation_refused(self):
        for path, old, new in ((CORE, ".reg .written", ".reg .other"), (FRONTEND, "64-k.val", "63-k.val")):
            current, baseline = fixture()
            current[path] = current[path].replace(old, new)
            with self.subTest(path=path), self.assertRaises(ValueError):
                inspect(current, baseline)

    def test_state_and_unrelated_feature_mutations_refused(self):
        for old, new in (("Register 64", "Register 63"), ("def bulkOwner := original", "def bulkOwner := weakened")):
            current, baseline = fixture()
            current[FRONTEND] = current[FRONTEND].replace(old, new)
            with self.subTest(new=new), self.assertRaises(ValueError):
                inspect(current, baseline)

    def test_bridge_rhs_and_extra_proof_edits_refused(self):
        for path, old, new in ((CORE, "= ((List.finRange 64)", "= ((List.finRange 63)"),
                               (HOST, "  done", "  sorry"), (INIT, "  done", "  skip")):
            current, baseline = fixture()
            current[path] = current[path].replace(old, new)
            with self.subTest(path=path), self.assertRaises(ValueError):
                inspect(current, baseline)

    def test_actual_ready_core_alias_and_old_leaf_identity_required(self):
        current, baseline = fixture()
        current[READY_CORE] = current[READY_CORE].replace("Streaming.Core.covered", "Streaming.Core.countValid")
        with self.assertRaises(ValueError):
            inspect(current, baseline)
        current, baseline = fixture()
        baseline[READY_CORE] = baseline[READY_CORE].replace(".reg .written", ".reg .other")
        with self.assertRaises(ValueError):
            inspect(current, baseline)


if __name__ == "__main__":
    unittest.main()
