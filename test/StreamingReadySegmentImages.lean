import Lean.Data.Json
import Pinwheel.Program.StreamingReadySegments

open Lean
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingReadySegments

private def rows := registerReadRows I2cProfile.standard

example : check (rows.set 0 (.branch 20 true)) 36 = none := by decide +kernel
example : check (rows.set 2 (.count 0)) 36 = none := by decide +kernel
example : check (rows.set 4 (.branch 1 true)) 36 = none := by decide +kernel
example : check (rows.set 4 (.branch 24 true)) 36 = none := by decide +kernel

def main : IO Unit := do
  let profile := I2cProfile.standard
  let image := registerReadImage
  let tx := registerReadTX ⟨0x53, 0xA6⟩
  IO.println (Json.mkObj [
    ("words", toJson (image.words.map BitVec.toNat)),
    ("tx_budget", toJson image.txBudget),
    ("tx_bits", toJson tx),
    ("wait_budget", toJson (profile.budgetMinusOne.val + 1)),
    ("idle_levels", toJson (0 : Nat)),
    ("idle_enabled", toJson (0 : Nat))]).compress
