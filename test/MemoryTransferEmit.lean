import Pinwheel.Hardware.Memory.TransferCircuit
import Pinwheel.Hardware.Emit
import MemoryTransferSupport
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryTransferEmit

private def portsJson (d : Interface P) : Json :=
  toJson (d.ports.map fun ⟨w, p⟩ => Json.mkObj [("name", toJson (d.label p)), ("width", toJson w)])

def emit (a wi wo : Nat) (out : String) : IO Unit := do
  let ii := TransferInterface.inputs a wi
  let oi := TransferInterface.outputs a wo
  let ri := TransferCircuit.registers a
  let moduleName := s!"transfer_a{a}_i{wi}_o{wo}"
  let registerName := fun {b} (r : TransferCircuit.Register a b) => "r_" ++ ri.label r
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/transfer.mlir") (← IO.ofExcept
    (Emit.moduleText moduleName (TransferCircuit.circuit (a := a) (MemoryTransferSupport.transform wi wo))
      ii.ports ri.ports oi.ports ii.label ri.label oi.label))
  let regs := toJson (ri.ports.map fun ⟨b, r⟩ => Json.mkObj
    [("name", toJson (registerName r)), ("reference", toJson (registerName r)), ("width", toJson b)])
  let inputRoles := #["reset", "start_valid", "source_base", "destination_base", "length",
    "source_ready", "response_valid", "response_data", "destination_ready"]
  let outputRoles := #["start_ready", "busy", "done", "error", "source_valid", "source_address",
    "response_ready", "destination_valid", "destination_address", "destination_data", "memory_reset"]
  let registerRoles := #["phase", "source_base", "destination_base", "length", "index", "done", "error"]
  let roles := Json.mkObj (((inputRoles.zip ii.ports).map fun (name, ⟨_, p⟩) =>
    (name, toJson (ii.label p))).toList ++ ((outputRoles.zip oi.ports).map fun (name, ⟨_, p⟩) =>
    (name, toJson (oi.label p))).toList)
  let registerRoles := Json.mkObj ((registerRoles.zip ri.ports).map fun (name, ⟨_, p⟩) =>
    (name, toJson (registerName p))).toList
  let descriptor := Json.mkObj
    [("schema", toJson (1 : Nat)), ("module", toJson moduleName), ("clock", toJson "clk"),
     ("address_width", toJson a), ("input_width", toJson wi), ("output_width", toJson wo),
     ("transform", toJson "invert_resize"), ("inputs", portsJson ii), ("outputs", portsJson oi),
     ("registers", regs), ("roles", roles), ("register_roles", registerRoles),
     ("startup", toJson "arbitrary register bits; external reset establishes empty control"),
     ("reserved_phase", toJson "phase3 suppresses transactions, asserts memory_reset, and recovers empty control with error"),
     ("memory_boundary", toJson "open memory ports; attached adapters must honor memory_reset and hold stalled responses")]
  IO.FS.writeFile (out ++ "/interface.json") (descriptor.pretty ++ "\n")
  IO.println s!"Transfer controller a={a} {wi}->{wo}: {ri.size} registers emitted to {out}."

end MemoryTransferEmit

def main (args : List String) : IO Unit := do
  let [a, wi, wo, out] := args | throw (IO.userError "Usage: memory_transfer_emit ADDRESS_WIDTH INPUT_WIDTH OUTPUT_WIDTH outdir")
  let some a := a.toNat? | throw (IO.userError "Invalid address width")
  let some wi := wi.toNat? | throw (IO.userError "Invalid input width")
  let some wo := wo.toNat? | throw (IO.userError "Invalid output width")
  unless a > 0 && wi > 0 && wo > 0 do throw (IO.userError "HDL export requires positive widths")
  MemoryTransferEmit.emit a wi wo out
