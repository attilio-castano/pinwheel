import Pinwheel.Hardware.Memory.TransferHostOwnershipCandidate
import Pinwheel.Hardware.Emit
import MemoryTransferSupport

open Pinwheel.Hardware Pinwheel.Hardware.Memory

def main (args : List String) : IO Unit := do
  let [a, wi, wo, out] := args
    | throw (IO.userError "Usage: memory_transfer_host_ownership_emit ADDRESS_WIDTH INPUT_WIDTH OUTPUT_WIDTH outdir")
  let some a := a.toNat? | throw (IO.userError "Invalid address width")
  let some wi := wi.toNat? | throw (IO.userError "Invalid input width")
  let some wo := wo.toNat? | throw (IO.userError "Invalid output width")
  unless a > 0 && wi > 0 && wo > 0 do throw (IO.userError "HDL export requires positive widths")
  let ii := TransferHostInterface.inputs a wi wo
  let oi := TransferHostInterface.outputs wi wo
  let ri := TransferHostOwnershipCandidate.registers a wi wo
  let moduleName := s!"transfer_host_a{a}_i{wi}_o{wo}"
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/transfer-host.mlir") (← IO.ofExcept
    (Emit.moduleText moduleName (TransferHostOwnershipCandidate.circuit (a := a) (MemoryTransferSupport.transform wi wo))
      ii.ports ri.ports oi.ports ii.label ri.label oi.label))
  IO.println s!"Host ownership a={a} {wi}->{wo}: {ri.size} registers emitted to {out}."
