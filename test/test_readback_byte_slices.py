"""Statement-preserving proof search, real kernel proofs, and false-sign rejection."""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import readback_byte_slices as slices
import process_group

PREFIX = """import Lean.Elab.Command
import Pinwheel.Hardware.Readback.Boolean
open Pinwheel.Hardware
namespace Pinwheel.TypedArtifact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
"""
FALLBACK = """  all_goals first
  | rfl
  | (skip; done)
"""
END = "end Pinwheel.TypedArtifact\n"
APPEND = """theorem local_0 (x0 : BitVec 16) (x1 : BitVec 8) (x2 : BitVec 8) :
    (x0 ++ (x1 ++ x2)) = ((x0 ++ x1) ++ x2) := by
""" + FALLBACK


def mux(condition, yes, no):
    return f"(if ({condition}) = 1 then ({yes}) else ({no}))"


def eq(variable, value):
    return f"(BitVec.ofBool (decide ({variable} = ({value}#2))))"


def part(start, width):
    return f"((x4).extractLsb' {start} {width})"


def repeated(bit, payload, count):
    # CIRCT/Yosys emit the replicated sign prefix as a left-associated concat.
    # Keeping this association also avoids expensive dependent-width inference
    # on a right-nested copy of the entire byte-selector expression.
    result = bit
    for _ in range(count-1):
        result = f"({result} ++ {bit})"
    return f"({result} ++ {payload})"


def endpoint(wrong_sign=False, identical_guard=True):
    """The actual priority-to-pmux byte selection and scalar sign-bit expansion."""
    byte = mux(eq("x3", 0), part(0, 8), mux(eq("x3", 1), part(8, 8), mux(eq("x3", 2), part(16, 8), part(24, 8))))
    optimized = mux(f"{eq('x3', 1)} ||| {eq('x3', 2)}",
                    mux(eq("x3", 2), part(16, 8), part(8, 8)), mux(eq("x3", 0), part(0, 8), part(24, 8)))
    half = mux(eq("x3", 0), part(0, 16), part(16, 16))
    old_byte_bit = f"(x1 &&& ({byte}).extractLsb' 7 1)"
    new_byte_bit = f"(x1 &&& ({optimized}).extractLsb' 7 1)"
    half_bit = f"(x1 &&& ({half}).extractLsb' 15 1)"
    high_byte = "8388607#24" if wrong_sign else "16777215#24"
    left_byte = f"({mux(old_byte_bit, high_byte, '0#24')} ++ {byte})"
    left_half = f"({mux(half_bit, '65535#16', '0#16')} ++ {half})"
    right_byte, right_half = repeated(new_byte_bit, optimized, 24), repeated(half_bit, half, 16)
    # Test both the equal-guard rfl bottleneck and the algebraically equivalent
    # but syntactically different guards present in the retained real endpoint.
    guard = "x0" if identical_guard else "~~~(~~~x0)"
    lhs = mux(guard, mux(eq("x2", 0), left_byte, mux(eq("x2", 1), left_half, "x4")), "0#32")
    rhs = mux("x0", mux(eq("x2", 0), right_byte, mux(eq("x2", 1), right_half, "x4")), "0#32")
    return lhs, rhs


def endpoint_theorem(wrong_sign=False, identical_guard=True, later_two_bit_binder=False):
    lhs, rhs = endpoint(wrong_sign, identical_guard)
    extra = " (x5 : BitVec 2)" if later_two_bit_binder else ""
    return "theorem local_1 (x0 : BitVec 1) (x1 : BitVec 1) (x2 : BitVec 2) (x3 : BitVec 2) (x4 : BitVec 32)"+extra+" :\n" + \
        f"    {lhs} = {rhs} := by\n" + FALLBACK


def byte_only_theorem():
    lhs = mux("x0", f"({mux('x1', '16777215#24', '0#24')} ++ x2)", "0#32")
    rhs = mux("x0", repeated("x1", "x2", 24), "0#32")
    return "theorem local_2 (x0 : BitVec 1) (x1 : BitVec 1) (x2 : BitVec 8) :\n" + \
        f"    {lhs} = {rhs} := by\n"+FALLBACK


def compile_module(directory, module, *, extra_path=()):
    lean_path = os.pathsep.join(map(str, (directory, *extra_path, ROOT / ".lake/build/lib/lean")))
    command = ["lake", "env", "env", "LEAN_PATH="+lean_path, "lean", "-DwarningAsError=true",
               "-o", directory / (module+".olean"), directory / (module+".lean")]
    return process_group.run_captured(list(map(str, command)), cwd=ROOT, timeout=30,
                                      log_path=directory / (module+".log"))


class ParserTests(unittest.TestCase):
    def test_exact_statements_and_last_two_bit_branch(self):
        original = PREFIX+APPEND+"\n"+endpoint_theorem()+"\n"+END
        updated, evidence = slices._rewrite(original)
        self.assertEqual(evidence, {"append_prepasses": 2, "finite_offset_branches": 2,
                                   "direct_normalization_branches": 1, "preserved_propositions": 2})
        before = [entry[3] for entry in slices._declarations(original)]
        self.assertEqual(before, [entry[3] for entry in slices._declarations(updated)])
        self.assertIn("byte_offset_cases : x3 = (0#2)", updated)
        self.assertLess(updated.index("byte_offset_cases : x3"), updated.index("byte_offset_cases : x2"))
        self.assertEqual(updated.count("  | (skip; done)\n"), 2)
        self.assertIn("      done)\n  | rfl\n  | (skip; done)", updated)

    def test_auxiliary_and_custom_proofs_remain_unchanged(self):
        helper = "theorem local_1_labels (x : BitVec 1) :\n    x = x := by\n  rfl\n\n"
        custom = "theorem local_2 (x0 : BitVec 32) :\n    x0 = x0 := by\n  rfl\n\n"
        original = PREFIX+helper+custom+END
        updated, evidence = slices._rewrite(original)
        self.assertEqual(updated, original)
        self.assertEqual(evidence, {"append_prepasses": 0, "finite_offset_branches": 0,
                                   "direct_normalization_branches": 0, "preserved_propositions": 1})

    def test_malformed_declarations_and_boundaries_fail_closed(self):
        candidates = [
            PREFIX+APPEND.replace(" :\n", "\n :\n")+END,
            PREFIX+APPEND.replace(" := by\n", "\n := by\n")+END,
            PREFIX+APPEND+"axiom unexpected : False\n"+END,
            PREFIX+APPEND+"def unexpected := 0\n"+END,
            PREFIX+APPEND,
            PREFIX+APPEND+APPEND+END,
            PREFIX+APPEND.replace(FALLBACK, FALLBACK+FALLBACK)+END,
        ]
        for candidate in candidates:
            with self.subTest(source=candidate), self.assertRaises(ValueError):
                slices._rewrite(candidate)

    def test_one_helper_and_no_write_on_parse_failure(self):
        with tempfile.TemporaryDirectory(prefix="byte-slices-") as temporary:
            directory = Path(temporary)
            modules = ["Design", "LocalProofs000", "LocalProofs001", "LocalProofs", "Links"]
            for name, text in (("LocalProofs000", PREFIX+APPEND+END),
                               ("LocalProofs001", PREFIX+endpoint_theorem()+END),
                               ("LocalProofs", "import LocalProofs000\nimport LocalProofs001\n")):
                (directory / (name+".lean")).write_text(text)
            evidence = slices.prepare_byte_slices(directory, modules)
            self.assertEqual(modules, ["Design", "ByteSliceLemmas", "LocalProofs000", "LocalProofs001", "LocalProofs", "Links"])
            self.assertEqual(evidence["modified_modules"], ["LocalProofs000", "LocalProofs001"])
            self.assertEqual(evidence["preserved_propositions"], 2)
            self.assertEqual((directory / "LocalProofs.lean").read_text(), "import LocalProofs000\nimport LocalProofs001\n")
            with self.assertRaises(ValueError):
                slices.prepare_byte_slices(directory, modules)
        with tempfile.TemporaryDirectory(prefix="byte-slices-") as temporary:
            directory = Path(temporary)
            good, bad = PREFIX+APPEND+END, PREFIX+"theorem local_1\n"
            (directory / "LocalProofs000.lean").write_text(good)
            (directory / "LocalProofs001.lean").write_text(bad)
            modules = ["LocalProofs000", "LocalProofs001"]
            with self.assertRaises(ValueError):
                slices.prepare_byte_slices(directory, modules)
            self.assertEqual((directory / "LocalProofs000.lean").read_text(), good)
            self.assertEqual((directory / "LocalProofs001.lean").read_text(), bad)
            self.assertEqual(modules, ["LocalProofs000", "LocalProofs001"])
            self.assertFalse((directory / "ByteSliceLemmas.lean").exists())

    def test_helper_is_audited_and_uses_no_native_proof_shortcut(self):
        source = slices.helper_source()
        self.assertIn("namespace Pinwheel.TypedArtifact.ByteSlices", source)
        self.assertEqual(len(re.findall(r"^theorem ", source, re.M)), 5)
        self.assertIn("decide +kernel", source)
        for forbidden in ("native_decide", "bv_decide", "sorry", "axiom "):
            self.assertNotIn(forbidden, source)


class KernelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = subprocess.run(["lake", "build", "Pinwheel.Hardware.Readback.Boolean"],
                                cwd=ROOT, text=True, capture_output=True, timeout=90)
        if result.returncode:
            raise AssertionError(result.stdout+result.stderr)

    def test_positive_slice_sign_endpoint_and_standard_axiom_audit(self):
        with tempfile.TemporaryDirectory(prefix="byte-slice-kernel-", dir=ROOT / "build") as temporary:
            directory = Path(temporary)
            (directory / "LocalProofs000.lean").write_text(PREFIX+APPEND+END)
            (directory / "LocalProofs001.lean").write_text(PREFIX+
                endpoint_theorem(later_two_bit_binder=True)+"\n"+byte_only_theorem()+END)
            (directory / "LocalProofs.lean").write_text("import LocalProofs000\nimport LocalProofs001\n")
            modules = ["LocalProofs000", "LocalProofs001", "LocalProofs"]
            slices.prepare_byte_slices(directory, modules)
            (directory / "Audit.lean").write_text("""import Lean
import LocalProofs
open Lean Elab Command
elab "#audit_byte_slices" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.TypedArtifact." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axiom in {name}: {bad}"
  if count < 7 then throwError "Incomplete helper/endpoint audit"
  logInfo m!"Byte slice audit: {count} declarations, standard axioms only."
#audit_byte_slices
""")
            for module in modules+["Audit"]:
                result = compile_module(directory, module)
                self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            self.assertIn("standard axioms only", result.stdout)

    def test_wrong_sign_has_kernel_counterexample_and_proof_rejection(self):
        with tempfile.TemporaryDirectory(prefix="byte-slice-negative-", dir=ROOT / "build") as temporary:
            directory = Path(temporary)
            (directory / "LocalProofs.lean").write_text(PREFIX+endpoint_theorem(wrong_sign=True, identical_guard=False)+END)
            modules = ["LocalProofs"]
            slices.prepare_byte_slices(directory, modules)
            result = compile_module(directory, "ByteSliceLemmas")
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
            lhs, rhs = endpoint(wrong_sign=True, identical_guard=False)
            values = {"x0": "(1#1)", "x1": "(1#1)", "x2": "(0#2)", "x3": "(0#2)", "x4": "(128#32)"}
            instantiate = lambda text: re.sub(r"\bx[0-9]+\b", lambda match: values[match[0]], text)
            left, right = instantiate(lhs), instantiate(rhs)
            (directory / "Counterexample.lean").write_text("import Lean\nimport ByteSliceLemmas\n"+
                f"example : {left} = (2147483520#32) := by decide +kernel\n"+
                f"example : {right} = (4294967168#32) := by decide +kernel\n"+
                f"theorem Pinwheel.TypedArtifact.wrongSignWitness : ¬({left} = {right}) := by decide +kernel\n"+
                """open Lean Elab Command
elab "#audit_witness" : command => do
  let axioms ← collectAxioms ``Pinwheel.TypedArtifact.wrongSignWitness
  let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
  unless bad.isEmpty do throwError "Unapproved witness axioms: {bad}"
  logInfo "Concrete wrong-sign witness: standard axioms only."
#audit_witness
""")
            witness = compile_module(directory, "Counterexample")
            self.assertEqual(witness.returncode, 0, witness.stdout+witness.stderr)
            self.assertIn("Concrete wrong-sign witness: standard axioms only.", witness.stdout)
            rejected = compile_module(directory, "LocalProofs")
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn("unsolved goals", rejected.stdout)
            for unexpected in ("unknown identifier", "unexpected token", "file not found", "application type mismatch"):
                self.assertNotIn(unexpected, rejected.stdout+rejected.stderr)


if __name__ == "__main__":
    unittest.main()
