import Pinwheel.Hardware.Stream.BufferedMerge.Circuit
import Pinwheel.Hardware.Emit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Stream.BufferedMerge

namespace BufferedMergeEmit

private def number (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"Expected natural number: {s}")

private def portsJson (d : Interface P) : Json :=
  toJson (d.ports.map fun ⟨w, p⟩ => Json.mkObj [("name", toJson (d.label p)), ("width", toJson w)])

def emit (n w : Nat) (out : String) : IO Unit := do
  let ii := Physical.inputInterface n w
  let oi := Physical.outputInterface n w
  let ri := Structural.registers n w
  let c := Structural.circuit n w
  let initial : Values (Structural.Register n w) := Structural.encode Pinwheel.Hardware.Stream.BufferedMerge.initial
  let name := fun {b : Nat} (r : Structural.Register n w b) => "r_" ++ ri.label r
  let moduleName := s!"buffered_merge_{n+1}_w{w}"
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/merge.mlir") (← IO.ofExcept
    (Emit.moduleText moduleName c ii.ports ri.ports oi.ports ii.label ri.label oi.label))
  let regs := toJson (ri.ports.map fun ⟨b, r⟩ => Json.mkObj
    [("name", toJson (name r)), ("reference", toJson (name r)), ("width", toJson b),
     ("initial", toJson ((initial r).toNat)), ("reset", toJson ((initial r).toNat))])
  let roles := Json.mkObj
    [("reset", toJson (ii.label Physical.reset)), ("out_ready", toJson (ii.label Physical.outReady)),
     ("in_valid", toJson (Array.ofFn (fun k : Fin (n+1) => ii.label (Physical.inValid k)))),
     ("in_payload", toJson (Array.ofFn (fun k : Fin (n+1) => ii.label (Physical.inPayload k)))),
     ("in_ready", toJson (Array.ofFn (fun k : Fin (n+1) => oi.label (Physical.inReady k)))),
     ("out_valid", toJson (oi.label Physical.outValid)), ("out_payload", toJson (oi.label Physical.outPayload))]
  let registerRoles := Json.mkObj
    [("slot_valid", toJson (name (Structural.slotReg (.valid 0)))),
     ("slot_payload", toJson (name (Structural.slotReg (.data 0)))),
     ("cursor", toJson (Array.ofFn (fun k : Fin (n+1) => name (Structural.cursorReg k))))]
  let descriptor := Json.mkObj
    [("schema", toJson (1 : Nat)), ("module", toJson moduleName),
     ("input_count", toJson (n+1)), ("output_count", toJson (1 : Nat)), ("payload_width", toJson w),
     ("cursor_encoding", toJson "one_hot"), ("clock", toJson "clk"), ("reset_synchronous", toJson true),
     ("inputs", portsJson ii), ("outputs", portsJson oi), ("registers", regs),
     ("roles", roles), ("register_roles", registerRoles),
     ("startup", toJson "encoded_initial; hardware requires a reset edge before use")]
  IO.FS.writeFile (out ++ "/interface.json") (descriptor.pretty ++ "\n")
  IO.println s!"Buffered merge {n+1}/{w}: {ii.size} inputs, {oi.size} outputs, {ri.size} registers emitted to {out}."

end BufferedMergeEmit

def main (args : List String) : IO Unit := do
  let [ni, width, out] := args
    | throw (IO.userError "Usage: BufferedMergeEmit INPUTS WIDTH outdir")
  let count ← BufferedMergeEmit.number ni
  let w ← BufferedMergeEmit.number width
  unless count > 0 && w > 0 do throw (IO.userError "Input count and payload width must be positive")
  BufferedMergeEmit.emit (count-1) w out
