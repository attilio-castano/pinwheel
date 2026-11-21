import Lean.Data.Json
import Pinwheel.Program.StreamingSWDBranching

open Lean
open Pinwheel.Program.StreamingReadySegments Pinwheel.Program.StreamingSWDBranching

private def exitKind : Exit → String
  | .complete => "complete"
  | .discard => "discard"
  | .fault => "fault"

private def exitJson (path : PathEnd) : Json :=
  Json.mkObj [("kind", toJson (exitKind path.exit)), ("tx", toJson path.tx), ("rx", toJson path.rx),
    ("core_clocks", toJson path.coreClocks)]

private def manifest (variant : Variant) : Json :=
  let checked := image variant
  Json.mkObj [
    ("schema", toJson "pinwheel.ready-swd-read.v1"),
    ("words", toJson (checked.words.map BitVec.toNat)),
    ("tx_budget", toJson checked.txBudget),
    ("tx_bits", toJson ([] : List Bool)),
    ("exits", toJson (checked.outcomes.map exitJson)),
    ("start_count", toJson (0 : Nat)),
    ("idle_levels", toJson idlePins.levels.toNat),
    ("idle_enabled", toJson idlePins.enabled.toNat),
    ("half_cycles", toJson (4 : Nat)),
    ("request_bits", toJson requestBits)]

def main (args : List String) : IO Unit := do
  let variant ← match args with
    | [] | ["standard"] => pure Variant.standard
    | ["inverted-ack"] => pure Variant.invertedAck
    | ["short-turnaround"] => pure Variant.shortTurnaround
    | _ => throw (IO.userError "Expected standard, inverted-ack, or short-turnaround")
  IO.println (manifest variant).compress
