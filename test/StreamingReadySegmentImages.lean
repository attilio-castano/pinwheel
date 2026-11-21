import Lean.Data.Json
import Pinwheel.Program.StreamingReadyRegisterReadVariants

open Lean
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingReadySegments
open Pinwheel.Program.StreamingReadyRegisterReadVariants

private def rows := registerReadRows I2cProfile.standard

example : check (rows.set 0 (.branch 20 true)) 36 = none := by decide +kernel
example : check (rows.set 2 (.count 0)) 36 = none := by decide +kernel
example : check (rows.set 4 (.branch 1 true)) 36 = none := by decide +kernel
example : check (rows.set 4 (.branch 24 true)) 36 = none := by decide +kernel

private def exitKind : Exit → String
  | .complete => "complete"
  | .discard => "discard"
  | .fault => "fault"

private def exitJson (path : PathEnd) : Json :=
  Json.mkObj [("kind", toJson (exitKind path.exit)), ("tx", toJson path.tx), ("rx", toJson path.rx),
    ("core_clocks", toJson path.coreClocks)]

private def manifest {program : List Row} (image : Image program 36) : Json :=
  let profile := I2cProfile.standard
  let request : Pinwheel.I2C.RegisterRead.Request := ⟨0x53, 0xA6⟩
  let tx := registerReadTX request
  Json.mkObj [
    ("schema", toJson "pinwheel.ready-register-read.v1"),
    ("address", toJson request.address.val),
    ("register", toJson request.register.toNat),
    ("words", toJson (image.words.map BitVec.toNat)),
    ("tx_budget", toJson image.txBudget),
    ("tx_bits", toJson tx),
    ("exits", toJson (image.outcomes.map exitJson)),
    ("wait_budget", toJson (profile.budgetMinusOne.val + 1)),
    ("idle_levels", toJson (0 : Nat)),
    ("idle_enabled", toJson (0 : Nat))]

def main (args : List String) : IO Unit := do
  let image ← match args with
    | [] => pure (manifest registerReadImage)
    | ["split"] => pure (manifest splitImage)
    | ["inverted-ack"] => pure (manifest invertedAckImage)
    | _ => throw (IO.userError "Expected no argument, split, or inverted-ack")
  IO.println image.compress
