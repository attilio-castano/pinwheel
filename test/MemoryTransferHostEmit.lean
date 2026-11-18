import Pinwheel.Hardware.Memory.TransferHostExport
import Pinwheel.Hardware.Emit
import MemoryTransferSupport
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryTransferHostEmit

private def metadata (a wi wo : Nat) : List (String × Json) :=
  let ii := TransferHostInterface.inputs a wi wo
  let oi := TransferHostInterface.outputs wi wo
  let ri := TransferHostCircuit.registers a wi wo
  let registerName := fun {b} (r : TransferHostCircuit.Register a wi wo b) => Emit.registerSymbol (ri.label r)
  let inputRoles := #["reset", "start_valid", "source_base", "destination_base", "length",
    "source_req_valid", "source_req_write", "source_req_address", "source_req_data", "source_resp_ready",
    "destination_req_valid", "destination_req_write", "destination_req_address", "destination_req_data",
    "destination_resp_ready"]
  let outputRoles := #["start_ready", "busy", "done", "error", "source_req_ready", "source_resp_valid",
    "source_resp_data", "destination_req_ready", "destination_resp_valid", "destination_resp_data"]
  let roles := Json.mkObj (((inputRoles.zip ii.ports).map fun (name, ⟨_, p⟩) =>
    (name, toJson (ii.label p))).toList ++ ((outputRoles.zip oi.ports).map fun (name, ⟨_, p⟩) =>
    (name, toJson (oi.label p))).toList)
  let control := #["phase", "source_base", "destination_base", "length", "index", "done", "error"]
  let controlRoles := ((control.zip (TransferCircuit.registers a).ports).map fun (name, ⟨_, p⟩) =>
    (name, toJson (registerName (.left p)))).toList
  let sourceWords := (Array.range (2^a)).map fun k =>
    registerName (.right (.left (.left (CommandFlops.word (BitVec.ofNat a k)))))
  let destinationWords := (Array.range (2^a)).map fun k =>
    registerName (.right (.right (.left (CommandFlops.word (BitVec.ofNat a k)))))
  let registerRoles := Json.mkObj (controlRoles ++ [
    ("source_words", toJson sourceWords),
    ("source_q", toJson (registerName (.right (.left (.left CommandFlops.q))))),
    ("source_pending", toJson (registerName (.right (.left StreamFlops.pending)))),
    ("destination_words", toJson destinationWords),
    ("destination_q", toJson (registerName (.right (.right (.left CommandFlops.q))))),
    ("destination_pending", toJson (registerName (.right (.right StreamFlops.pending))))])
  [("schema", toJson (1 : Nat)), ("address_width", toJson a),
   ("input_width", toJson wi), ("output_width", toJson wo),
   ("transform", toJson "invert_resize"), ("roles", roles), ("register_roles", registerRoles),
   ("startup", toJson "arbitrary words/Q/control/pending; reset preserves words/Q and clears control/pending"),
   ("ownership", toJson "offered start blocks host requests; both pending host responses drain before acceptance; busy transfer owns both memories")]

def emit (a wi wo : Nat) (out : System.FilePath) (hierarchical : Bool) : IO Unit := do
  let name := s!"transfer_host_a{a}_i{wi}_o{wo}"
  let design := TransferHostExport.hierarchy (MemoryTransferSupport.transform wi wo) a name
  if hierarchical then
    let emitted ← IO.ofExcept design.emit
    emitted.write out (metadata a wi wo)
  else
    let flat := { design.flat with name := name }
    let emitted ← IO.ofExcept flat.emit
    IO.FS.createDirAll out
    IO.FS.writeFile (out / "transfer-host.mlir") emitted.mlir
    let descriptor := (Json.mkObj (metadata a wi wo)).mergeObj emitted.descriptor
    IO.FS.writeFile (out / "interface.json") (descriptor.pretty ++ "\n")
  IO.println s!"Host transfer a={a} {wi}->{wo}: {design.flat.registers.size} registers emitted to {out}."

end MemoryTransferHostEmit

def main (args : List String) : IO Unit := do
  let (hierarchical, rest) := match args with
    | "--hierarchy" :: rest => (true, rest)
    | _ => (false, args)
  let [a, wi, wo, out] := rest
    | throw (IO.userError "Usage: memory_transfer_host_emit [--hierarchy] ADDRESS_WIDTH INPUT_WIDTH OUTPUT_WIDTH outdir")
  let some a := a.toNat? | throw (IO.userError "Invalid address width")
  let some wi := wi.toNat? | throw (IO.userError "Invalid input width")
  let some wo := wo.toNat? | throw (IO.userError "Invalid output width")
  unless a > 0 && wi > 0 && wo > 0 do throw (IO.userError "HDL export requires positive widths")
  MemoryTransferHostEmit.emit a wi wo out hierarchical
