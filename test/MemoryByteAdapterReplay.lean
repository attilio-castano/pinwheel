import Pinwheel.Hardware.Memory.ByteAdapterCircuit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryByteAdapterReplay

private def snapshot (d : Interface P) (bank : Values P) : Array Nat :=
  d.ports.map (fun ⟨_, p⟩ => (bank p).toNat)

private def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!

private def input (a : Nat) (j : Json) : Except String (Values (ByteAdapterInterface.Input a)) := do
  let reset ← j.getObjValAs? Bool "reset"
  let valid ← j.getObjValAs? Bool "request_valid"
  let write ← j.getObjValAs? Bool "write"
  let signed ← j.getObjValAs? Bool "signed"
  let size ← j.getObjValAs? Nat "size"
  let address ← j.getObjValAs? Nat "address"
  let offset ← j.getObjValAs? Nat "offset"
  let data ← j.getObjValAs? Nat "data"
  let ready ← j.getObjValAs? Bool "response_ready"
  unless size < 4 && address < 2^a && offset < 4 && data < 2^32 do throw "Input exceeds wire width"
  return values (ByteAdapterInterface.inputs a)
    #[reset.toNat, valid.toNat, write.toNat, signed.toNat, size, address, offset, data, ready.toNat]

/-- Complete physical words/Q/retained metadata/pending are checked, including
bits erased by the logical view. Address width zero is allowed for semantics. -/
def replay (a : Nat) (stimulus startup result : String) : IO Unit := do
  let ri := ByteAdapterCircuit.registers a
  let oi := ByteAdapterInterface.outputs
  let c := ByteAdapterCircuit.circuit a
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
    let i ← IO.ofExcept (input a raw)
    let before := snapshot oi (c.observe i (values ri bank))
    bank := snapshot ri (c.step i (values ri bank))
    let after := snapshot oi (c.observe i (values ri bank))
    rows := rows.push (Json.mkObj [("cycle", toJson cycle), ("input", raw),
      ("pre", toJson before), ("post", toJson after), ("registers", toJson bank)]).compress
    cycle := cycle+1
  if cycle == 0 then throw (IO.userError "Stimulus must contain at least one edge")
  IO.FS.writeFile result (String.intercalate "\n" rows.toList ++ "\n")
  IO.println s!"Byte adapter {2^a}x32: {cycle} physical transitions replayed."

end MemoryByteAdapterReplay

def main (args : List String) : IO Unit := do
  let [a, stimulus, startup, result] := args
    | throw (IO.userError "Usage: memory_byte_adapter_replay ADDRESS_WIDTH stimulus.jsonl startup.json trace.jsonl")
  let some a := a.toNat? | throw (IO.userError "Invalid address width")
  MemoryByteAdapterReplay.replay a stimulus startup result
