import Pinwheel.Hardware.Memory.TransferHostCircuit
import MemoryTransferSupport
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryTransferHostReplay

private def snapshot (d : Interface P) (values : Values P) : Array Nat :=
  d.ports.map (fun ⟨_, p⟩ => (values p).toNat)

private def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!

private def input (a wi wo : Nat) (j : Json) : Except String (Values (TransferHostInterface.Input a wi wo)) := do
  let descriptor := TransferHostInterface.inputs a wi wo
  let mut bank : Array Nat := #[]
  for ⟨w, p⟩ in descriptor.ports do
    let key := descriptor.label p
    let value ← j.getObjValAs? Nat key
    unless value < 2^w do throw s!"Input {key} exceeds its {w}-bit wire width"
    bank := bank.push value
  return values descriptor bank

def replay (a wi wo : Nat) (stimulus startup result : String) : IO Unit := do
  let ri := TransferHostCircuit.registers a wi wo
  let oi := TransferHostInterface.outputs wi wo
  let c := TransferHostCircuit.circuit (a := a) (MemoryTransferSupport.transform wi wo)
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile startup))
  let mut bank ← IO.ofExcept (fromJson? raw : Except String (Array Nat))
  unless bank.size == ri.size do throw (IO.userError "Wrong startup register count")
  for (port, value) in ri.ports.zip bank do
    unless value < 2^port.1 do throw (IO.userError s!"Startup register exceeds its {port.1}-bit wire width")
  let mut rows : Array String := #[]
  let mut cycle := 0
  for line in (← IO.FS.readFile stimulus).splitOn "\n" do
    if line.isEmpty then continue
    let raw ← IO.ofExcept (Json.parse line)
    let i ← IO.ofExcept (input a wi wo raw)
    let before := snapshot oi (c.observe i (values ri bank))
    bank := snapshot ri (c.step i (values ri bank))
    let after := snapshot oi (c.observe i (values ri bank))
    rows := rows.push (Json.mkObj [("cycle", toJson cycle), ("input", raw),
      ("pre", toJson before), ("post", toJson after), ("registers", toJson bank)]).compress
    cycle := cycle+1
  if cycle == 0 then throw (IO.userError "Stimulus must contain at least one edge")
  IO.FS.writeFile result (String.intercalate "\n" rows.toList ++ "\n")
  IO.println s!"Host transfer a={a} {wi}->{wo}: {cycle} physical transitions replayed."

end MemoryTransferHostReplay

def main (args : List String) : IO Unit := do
  let [a, wi, wo, stimulus, startup, result] := args
    | throw (IO.userError "Usage: memory_transfer_host_replay ADDRESS_WIDTH INPUT_WIDTH OUTPUT_WIDTH stimulus.jsonl startup.json trace.jsonl")
  let some a := a.toNat? | throw (IO.userError "Invalid address width")
  let some wi := wi.toNat? | throw (IO.userError "Invalid input width")
  let some wo := wo.toNat? | throw (IO.userError "Invalid output width")
  MemoryTransferHostReplay.replay a wi wo stimulus startup result
