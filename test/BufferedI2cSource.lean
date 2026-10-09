import Pinwheel.Hardware.Buffered.I2cSource
import Lean

/-! Exact bounded typed constructor export for independent comparison with
lower_sram(compact_i2c_read(4, 4, 32)). This executable does not prove the Python
compiler universally; the importing module proves source/decoded execution. -/
open Pinwheel.Hardware.Buffered.I2cSource

def main (args : List String) : IO Unit := do
  unless args.isEmpty do
    throw (IO.userError "Usage: BufferedI2cSource.lean (fixed 4-byte, phase-4, wait-32 source)")
  let j := Lean.Json.mkObj
    [("schema", Lean.toJson "pinwheel-buffered-i2c-source-v1"),
     ("words", Lean.toJson ((List.range 50).map fun k => (word (BitVec.ofNat 6 k)).toNat)),
     ("controls", Lean.toJson ((List.range 50).map fun k => (control (BitVec.ofNat 6 k)).toNat)),
     ("branch_indices", Lean.toJson ((List.range 50).map fun k => (branchIndex (BitVec.ofNat 6 k)).toNat)),
     ("branch_table", Lean.toJson ((List.range 16).map fun k => (dictionary (BitVec.ofNat 4 k)).toNat)),
     ("virtual_span", Lean.toJson (270 : Nat)),
     ("idle_levels", Lean.toJson (0 : Nat)),
     ("idle_enabled", Lean.toJson (0 : Nat)),
     ("tx_bits", Lean.toJson (24 : Nat)),
     ("rx_reservation_bits", Lean.toJson (32 : Nat))]
  IO.println j.compress
