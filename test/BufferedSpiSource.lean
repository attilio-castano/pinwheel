import Pinwheel.Hardware.Buffered.SpiSource
import Lean

/-! Export the typed Lean SPI constructor for exact comparison with the
existing Python canonical lowering. The theorem module uses no native proof
oracle; this exporter is a separate executable fixture. -/
open Pinwheel.Hardware.Buffered.SpiSource

private def naturalArg (args : List String) (index fallback : Nat) : IO Nat :=
  match args[index]? with
  | none => pure fallback
  | some value => match value.toNat? with
    | some n => pure n
    | none => throw (IO.userError s!"SPI argument {index + 1} must be a natural number")

def main (args : List String) : IO Unit := do
  if args.length > 2 then throw (IO.userError "Usage: BufferedSpiSource.lean [bytes] [half_cycles]")
  let bytes ← naturalArg args 0 4
  let half ← naturalArg args 1 4
  if hb : 1 ≤ bytes ∧ bytes ≤ 4 then
    if hh : 3 ≤ half ∧ half ≤ 256 then
      let c : Config := ⟨⟨bytes - 1, by omega⟩, ⟨half - 1, by omega⟩,
        by change 2 ≤ half - 1; omega⟩
      let j := Lean.Json.mkObj
        [("schema", Lean.toJson "pinwheel-buffered-spi-source-v1"),
         ("words", Lean.toJson ((List.range 4).map fun k => (word c (BitVec.ofNat 6 k)).toNat)),
         ("controls", Lean.toJson ((List.range 4).map fun k => (control c (BitVec.ofNat 6 k)).toNat)),
         ("branch_indices", Lean.toJson ([0, 0, 0, 0] : List Nat)),
         ("branch_table", Lean.toJson (List.replicate 16 (0 : Nat))),
         ("virtual_span", Lean.toJson (16 * bytes + 2)),
         ("idle_levels", Lean.toJson (4 : Nat)),
         ("idle_enabled", Lean.toJson (7 : Nat)),
         ("tx_bits", Lean.toJson (8 * bytes)),
         ("rx_reservation_bits", Lean.toJson (8 * bytes))]
      IO.println j.compress
    else throw (IO.userError "SPI half period must be in 3..256")
  else throw (IO.userError "SPI byte count must be in 1..4")
