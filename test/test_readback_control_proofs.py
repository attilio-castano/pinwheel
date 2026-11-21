"""Check finite-control proof search against exact propositions and Lean's kernel."""
from contextlib import redirect_stdout
import io
from pathlib import Path
import re
import shutil
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from readback_control_proofs import split_two_bit_controls
from typed_artifact_runner import compile_modules


LEFT = "(if x7 = 0 then x0 else if x7 = 1 then x1 else if x7 = 2 then x2 else x3)"
RIGHT = "(if x7 = 3 then x3 else if x7 = 2 then x2 else if x7 = 1 then x1 else x0)"
PARAMETERS = "(w : Nat) (x0 x1 x2 x3 : BitVec w) (x7 : BitVec 2)"
HEADER = "import Lean\nnamespace ControlFixture\n"


def theorem(name="local_0", right=RIGHT, parameters=PARAMETERS):
    # With only rfl/skip the non-definitional mux reordering is deliberately
    # unproved. Successful compilation must use the inserted exhaustive split.
    return (f"theorem {name} {parameters} :\n    {LEFT} = {right} := by\n"
            "  all_goals first\n  | rfl\n  | skip\n\n")


def statement(source):
    return source.split(" := by\n", 1)[0]


class RewriteBoundaryTests(unittest.TestCase):
    def test_only_ordinary_local_theorem_changes_and_keeps_exact_proposition(self):
        ordinary = theorem()
        abstract = theorem("local_0_abstract")
        no_control = "theorem local_1 (x0 : BitVec 17) :\n    x0 = x0 := by\n  all_goals first\n  | rfl\n\n"
        source = HEADER + ordinary + abstract + no_control + "end ControlFixture\n"
        with tempfile.TemporaryDirectory(prefix="pinwheel-control-rewrite-") as temporary:
            directory = Path(temporary)
            selected = directory / "LocalProofs003.lean"
            selected.write_text(source)
            for module in ("Proof", "Graphs", "LocalProofsHelper"):
                (directory / (module + ".lean")).write_text(source)
            changed = split_two_bit_controls(directory, ["LocalProofs003", "Proof", "Graphs", "LocalProofsHelper"])
            result = selected.read_text()
            self.assertEqual(changed, 1)
            self.assertEqual(statement(result), statement(source))
            self.assertIn(abstract + no_control, result)
            self.assertIn("x7 = 0 ∨ x7 = 1 ∨ x7 = 2 ∨ x7 = 3", result)
            self.assertNotIn("native_decide", result)
            for module in ("Proof", "Graphs", "LocalProofsHelper"):
                self.assertEqual((directory / (module + ".lean")).read_text(), source)

    def test_malformed_headers_and_nonmatching_search_fragments_stay_unchanged(self):
        cases = [
            # A missing proof opener must not absorb a later abstract helper.
            "theorem local_8 (x7 : BitVec 2) :\n    x7 = x7\n\n" + theorem("local_8_abstract"),
            theorem().replace(" :\n", "\n", 1),
            theorem().replace(" := by\n", " := rfl\n", 1),
            theorem().replace("  all_goals first\n  | rfl\n", "  first | rfl\n"),
            theorem(parameters=PARAMETERS.replace("BitVec 2)", "BitVec 3)")),
        ]
        with tempfile.TemporaryDirectory(prefix="pinwheel-control-rejection-") as temporary:
            directory = Path(temporary)
            for number, fragment in enumerate(cases):
                with self.subTest(case=number):
                    path = directory / "LocalProofs.lean"
                    source = HEADER + fragment + "end ControlFixture\n"
                    path.write_text(source)
                    self.assertEqual(split_two_bit_controls(directory, ["LocalProofs"]), 0)
                    self.assertEqual(path.read_text(), source)


@unittest.skipUnless(shutil.which("lake"), "Lean integration test requires the pinned Lake toolchain")
class KernelControlTests(unittest.TestCase):
    def compile(self, directory, modules):
        records = SimpleNamespace(records=[])
        with patch("typed_artifact_runner.ROOT", directory.parent), redirect_stdout(io.StringIO()):
            compile_modules(records, directory, modules, timeout=60)
        for record in records.records:
            self.assertEqual(record["argv"][:3], ["lake", "env", "env"])
            self.assertTrue(record["argv"][3].startswith("LEAN_PATH=" + str(directory) + ":"))
            self.assertEqual(record["exit_code"], 0)
        return records

    def assert_semantic_failure(self, directory, module):
        with self.assertRaisesRegex(RuntimeError, module + " certificate failed:"):
            self.compile(directory, [module])
        self.assertFalse((directory / (module + ".olean")).exists())
        log = (directory / (module + ".log")).read_text()
        errors = re.findall(r"^.*?\.lean:\d+:\d+: error(?:\([^)]*\))?: (.*)$", log, re.M)
        self.assertTrue(errors, log)
        self.assertTrue(all("unsolved goals" in error for error in errors), errors)
        self.assertNotIn("sorryAx", log)

    def test_universal_payload_equivalence_and_phase_three_discrepancy(self):
        with tempfile.TemporaryDirectory(prefix="pinwheel-control-kernel-") as temporary:
            workspace = Path(temporary).resolve()
            (workspace / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            (workspace / "lakefile.toml").write_text('name = "control_fixture"\nversion = "0.1.0"\n')
            directory = workspace / "generated"
            directory.mkdir()
            original = HEADER + theorem() + "end ControlFixture\n"
            path = directory / "LocalProofs000.lean"
            path.write_text(original)
            self.assert_semantic_failure(directory, "LocalProofs000")
            self.assertEqual(split_two_bit_controls(directory, ["LocalProofs000"]), 1)
            self.assertEqual(statement(path.read_text()), statement(original))
            self.compile(directory, ["LocalProofs000"])

            # This module imports the freshly compiled private theorem and
            # instantiates it at each raw phase with unconstrained payloads.
            witness = "import LocalProofs000\nnamespace ControlFixture\n"
            for phase in range(4):
                left, right = LEFT.replace("x7", str(phase) + "#2"), RIGHT.replace("x7", str(phase) + "#2")
                witness += (f"theorem raw_phase_{phase} (w : Nat) (x0 x1 x2 x3 : BitVec w) :\n"
                            f"    {left} = {right} := local_0 w x0 x1 x2 x3 {phase}\n")
            witness += "end ControlFixture\n"
            (directory / "RawPhases.lean").write_text(witness)
            self.compile(directory, ["RawPhases"])

            # The mutant differs only on the reserved raw phase. It must fail
            # even though every normal phase agrees, at arbitrary word width.
            mutant_right = RIGHT.replace("x7 = 3 then x3", "x7 = 3 then x0")
            negative = HEADER + theorem("local_9", mutant_right) + "end ControlFixture\n"
            mutant = directory / "LocalProofs001.lean"
            mutant.write_text(negative)
            self.assertEqual(split_two_bit_controls(directory, ["LocalProofs001"]), 1)
            self.assertEqual(statement(mutant.read_text()), statement(negative))
            self.assert_semantic_failure(directory, "LocalProofs001")

            witness = "import RawPhases\nnamespace ControlFixture\nset_option linter.unusedVariables false\n"
            witness += f"def source {PARAMETERS} : BitVec w := {LEFT}\n"
            witness += f"def mutant {PARAMETERS} : BitVec w := {mutant_right}\n"
            for phase in range(3):
                witness += (f"theorem unchanged_phase_{phase} (w : Nat) (x0 x1 x2 x3 : BitVec w) :\n"
                            f"    source w x0 x1 x2 x3 {phase} = mutant w x0 x1 x2 x3 {phase} := by rfl\n")
            witness += """theorem phase_three_mismatch :
    source 257 0 7 11 (BitVec.ofNat 257 (2^200 + 165)) 3 ≠
      mutant 257 0 7 11 (BitVec.ofNat 257 (2^200 + 165)) 3 := by decide +kernel
end ControlFixture
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "ControlFixture." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved control proof axioms: {bad}"
  if count < 11 then throwError "Incomplete control proof audit"
  logInfo m!"Control proof audit: {count} declarations, standard axioms only."
"""
            (directory / "ControlWitness.lean").write_text(witness)
            self.compile(directory, ["ControlWitness"])
            self.assertIn("standard axioms only", (directory / "ControlWitness.log").read_text())


if __name__ == "__main__":
    unittest.main()
