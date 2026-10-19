import Pinwheel.Hardware.Buffered.I2cTimingUpload
import Lean

/-! Finite constructor exports for independent Python byte comparison. The
symbolic certificate covers all field values; this grid covers the supported
Python public constructor domain and does not extend that API's timing bounds. -/
open Pinwheel.Hardware.Buffered

private def exported (duration budget : Fin 256) : Lean.Json :=
  Lean.Json.mkObj
    [("phase_cycles", Lean.toJson (duration.val + 1)),
     ("wait_cycles", Lean.toJson (budget.val + 1)),
     ("words", Lean.toJson ((List.range 50).map fun k =>
       (I2cTiming.word duration budget (BitVec.ofNat 6 k)).toNat)),
     ("controls", Lean.toJson ((List.range 50).map fun k => (I2cSource.control (BitVec.ofNat 6 k)).toNat)),
     ("branch_indices", Lean.toJson ((List.range 50).map fun k => (I2cSource.branchIndex (BitVec.ofNat 6 k)).toNat)),
     ("branch_table", Lean.toJson ((List.range 16).map fun k => (I2cSource.dictionary (BitVec.ofNat 4 k)).toNat)),
     ("virtual_span", Lean.toJson (270 : Nat)),
     ("idle_levels", Lean.toJson (0 : Nat)),
     ("idle_enabled", Lean.toJson (0 : Nat)),
     ("tx_bits", Lean.toJson (24 : Nat)),
     ("rx_reservation_bits", Lean.toJson (32 : Nat))]

def main : IO Unit := do
  let phases : List (Fin 256) := [2, 3, 4, 127, 255]
  let waits : List (Fin 256) := [3, 4, 31, 127, 255]
  let cases := phases.flatMap fun duration => waits.map fun budget =>
    Lean.Json.mkObj
      [("phase_cycles", Lean.toJson (duration.val + 1)),
       ("wait_cycles", Lean.toJson (budget.val + 1)),
       ("image", exported duration budget)]
  IO.println (Lean.Json.mkObj
    [("schema", Lean.toJson "pinwheel-buffered-i2c-timing-source-v1"),
     ("cases", Lean.toJson cases)]).compress
