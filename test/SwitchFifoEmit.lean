import Pinwheel.Hardware.Switch.Backend
import Pinwheel.Hardware.Stream.CircularFifo3
import Pinwheel.Hardware.Emit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Switch

namespace SwitchFifoEmit

abbrev encoding : Physical.DestinationEncoding 2 := ⟨1, by decide, by decide⟩

private def ports (d : Interface P) (prefixName : String := "") : Json :=
  toJson (d.ports.map fun ⟨w, p⟩ =>
    let name := prefixName ++ d.label p
    Json.mkObj ([("index", toJson (d.position p).val), ("width", toJson w), ("name", toJson name)] ++
      (if prefixName.isEmpty then [] else [("reference", toJson name)])))

def emit (f : Stream.BackendAPI.Fifo 5 3) (kind dir : String) : IO Unit := do
  let ii := Physical.inputInterface 1 1 1 4
  let oi := Physical.outputInterface 1 1 4
  let ri := WithFifo.registers f 1 1 4
  let name := "switch_2x2_d3_w4_" ++ kind
  let mlir ← IO.ofExcept (Emit.moduleText name (WithFifo.circuit encoding f 1)
    ii.ports ri.ports oi.ports ii.label ri.label oi.label)
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/switch.mlir") mlir
  let descriptor := Json.mkObj [("module", toJson name), ("clock", toJson "clk"),
    ("inputs", ports ii), ("outputs", ports oi), ("registers", ports ri "r_")]
  IO.FS.writeFile (dir ++ "/interface.json") (descriptor.pretty ++ "\n")

end SwitchFifoEmit

def main (args : List String) : IO Unit := do
  match args with
  | ["shift", dir] => SwitchFifoEmit.emit (Stream.BackendAPI.shift 5 3 (by decide)) "shift" dir
  | ["circular", dir] => SwitchFifoEmit.emit (Stream.CircularFifo3.backend 5) "circular" dir
  | _ => throw (IO.userError "Usage: SwitchFifoEmit (shift|circular) outdir")
