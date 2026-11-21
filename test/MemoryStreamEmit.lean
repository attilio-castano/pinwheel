import Pinwheel.Hardware.Memory.StreamFlops
import Pinwheel.Hardware.Emit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryStreamEmit

private def portsJson (d : Interface P) : Json :=
  toJson (d.ports.map fun ⟨w, p⟩ => Json.mkObj
    [("name", toJson (d.label p)), ("width", toJson w)])

def emit (a w : Nat) (out : String) : IO Unit := do
  let ii := StreamInterface.inputs a w
  let oi := StreamInterface.outputs w
  let ri := StreamFlops.registers a w
  let moduleName := s!"stream_ram_a{a}_w{w}"
  let registerName := fun {b} (r : StreamFlops.Register a w b) => "r_" ++ ri.label r
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/memory.mlir") (← IO.ofExcept
    (Emit.moduleText moduleName (StreamFlops.circuit a w)
      ii.ports ri.ports oi.ports ii.label ri.label oi.label))
  let regs := toJson (ri.ports.map fun ⟨b, r⟩ => Json.mkObj
    [("name", toJson (registerName r)), ("reference", toJson (registerName r)), ("width", toJson b)])
  let roles := Json.mkObj
    [("reset", toJson (ii.label StreamInterface.reset)),
     ("valid", toJson (ii.label StreamInterface.valid)),
     ("write", toJson (ii.label StreamInterface.write)),
     ("address", toJson (ii.label StreamInterface.address)),
     ("data", toJson (ii.label StreamInterface.data)),
     ("ready", toJson (ii.label StreamInterface.ready)),
     ("in_ready", toJson (oi.label StreamInterface.inReady)),
     ("out_valid", toJson (oi.label StreamInterface.outValid)),
     ("out_data", toJson (oi.label StreamInterface.outData))]
  let registerRoles := Json.mkObj
    [("words", toJson (Array.ofFn (fun k : Fin (2^a) =>
        registerName (.left (CommandFlops.word (BitVec.ofFin k)))))),
     ("q", toJson (registerName (.left CommandFlops.q))),
     ("pending", toJson (registerName StreamFlops.pending))]
  let descriptor := Json.mkObj
    [("schema", toJson (1 : Nat)), ("module", toJson moduleName),
     ("address_width", toJson a), ("data_width", toJson w), ("depth", toJson (2^a)),
     ("clock", toJson "clk"), ("inputs", portsJson ii), ("outputs", portsJson oi),
     ("registers", regs), ("roles", roles), ("register_roles", registerRoles),
     ("startup", toJson "arbitrary array, Q and pending; no power-up initialization"),
     ("reset_behavior", toJson "suppresses both handshakes; edge clears pending only and preserves all array words and Q")]
  IO.FS.writeFile (out ++ "/interface.json") (descriptor.pretty ++ "\n")
  IO.println s!"Stream RAM {2^a}x{w}: {ri.size} registers emitted to {out}."

end MemoryStreamEmit

def main (args : List String) : IO Unit := do
  let [a, w, out] := args | throw (IO.userError "Usage: memory_stream_emit ADDRESS_WIDTH DATA_WIDTH outdir")
  let some a := a.toNat? | throw (IO.userError "Invalid address width")
  let some w := w.toNat? | throw (IO.userError "Invalid data width")
  unless a > 0 && w > 0 do throw (IO.userError "HDL export requires positive widths")
  MemoryStreamEmit.emit a w out
