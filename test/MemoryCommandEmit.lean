import Pinwheel.Hardware.Memory.CommandFlops
import Pinwheel.Hardware.Emit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryCommandEmit

private def portsJson (d : Interface P) : Json :=
  toJson (d.ports.map fun ⟨w, p⟩ => Json.mkObj
    [("name", toJson (d.label p)), ("width", toJson w)])

def emit (a w : Nat) (out : String) : IO Unit := do
  let ii := CommandInterface.inputs a w
  let oi := CommandInterface.outputs w
  let ri := CommandFlops.registers a w
  let moduleName := s!"command_ram_a{a}_w{w}"
  let registerName := fun {b} (r : CommandFlops.Register a w b) => "r_" ++ ri.label r
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/memory.mlir") (← IO.ofExcept
    (Emit.moduleText moduleName (CommandFlops.circuit a w)
      ii.ports ri.ports oi.ports ii.label ri.label oi.label))
  let regs := toJson (ri.ports.map fun ⟨b, r⟩ => Json.mkObj
    [("name", toJson (registerName r)), ("reference", toJson (registerName r)), ("width", toJson b)])
  let roles := Json.mkObj
    [("enable", toJson (ii.label .enable)), ("write", toJson (ii.label .write)),
     ("address", toJson (ii.label .address)), ("data", toJson (ii.label .data)),
     ("q", toJson (oi.label .q))]
  let registerRoles := Json.mkObj
    [("words", toJson (Array.ofFn (fun k : Fin (2^a) => registerName (CommandFlops.word (BitVec.ofFin k))))),
     ("q", toJson (registerName CommandFlops.q))]
  let descriptor := Json.mkObj
    [("schema", toJson (1 : Nat)), ("module", toJson moduleName),
     ("address_width", toJson a), ("data_width", toJson w), ("depth", toJson (2^a)),
     ("clock", toJson "clk"), ("inputs", portsJson ii), ("outputs", portsJson oi),
     ("registers", regs), ("roles", roles), ("register_roles", registerRoles),
     ("startup", toJson "arbitrary array and Q; no reset or power-up initialization")]
  IO.FS.writeFile (out ++ "/interface.json") (descriptor.pretty ++ "\n")
  IO.println s!"Command RAM {2^a}x{w}: {ri.size} registers emitted to {out}."

end MemoryCommandEmit

def main (args : List String) : IO Unit := do
  let [a, w, out] := args | throw (IO.userError "Usage: memory_command_emit ADDRESS_WIDTH DATA_WIDTH outdir")
  let some a := a.toNat? | throw (IO.userError "Invalid address width")
  let some w := w.toNat? | throw (IO.userError "Invalid data width")
  unless a > 0 && w > 0 do throw (IO.userError "HDL export requires positive widths")
  MemoryCommandEmit.emit a w out
