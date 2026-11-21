import Pinwheel.Hardware.Memory.StreamFlops
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryStreamReplay

private def snapshot (d : Interface P) (values : Values P) : Array Nat :=
  d.ports.map (fun ⟨_, p⟩ => (values p).toNat)

private def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!

private def input (a w : Nat) (j : Json) : Except String (Values (StreamInterface.Input a w)) := do
  let reset ← j.getObjValAs? Bool "reset"
  let valid ← j.getObjValAs? Bool "valid"
  let write ← j.getObjValAs? Bool "write"
  let address ← j.getObjValAs? Nat "address"
  let data ← j.getObjValAs? Nat "data"
  let ready ← j.getObjValAs? Bool "ready"
  unless address < 2^a && data < 2^w do throw "Input exceeds wire width"
  return StreamInterface.Pins.values ⟨BitVec.ofBool reset, BitVec.ofBool valid,
    BitVec.ofBool write, BitVec.ofNat a address, BitVec.ofNat w data, BitVec.ofBool ready⟩

/-- Startup and post-edge registers use the complete descriptor order: every
word, then Q, then pending. Pre/post outputs use ready, valid, data order. -/
def replay (a w : Nat) (stimulus startup result : String) : IO Unit := do
  let ri := StreamFlops.registers a w
  let oi := StreamInterface.outputs w
  let c := StreamFlops.circuit a w
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
    let i ← IO.ofExcept (input a w raw)
    let before := snapshot oi (c.observe i (values ri bank))
    bank := snapshot ri (c.step i (values ri bank))
    let after := snapshot oi (c.observe i (values ri bank))
    rows := rows.push (Json.mkObj [("cycle", toJson cycle), ("input", raw),
      ("pre", toJson before), ("post", toJson after), ("registers", toJson bank)]).compress
    cycle := cycle + 1
  if cycle == 0 then throw (IO.userError "Stimulus must contain at least one edge")
  IO.FS.writeFile result (String.intercalate "\n" rows.toList ++ "\n")
  IO.println s!"Stream RAM {2^a}x{w}: {cycle} physical transitions replayed."

end MemoryStreamReplay

def main (args : List String) : IO Unit := do
  let [a, w, stimulus, startup, result] := args
    | throw (IO.userError "Usage: memory_stream_replay ADDRESS_WIDTH DATA_WIDTH stimulus.jsonl startup.json trace.jsonl")
  let some a := a.toNat? | throw (IO.userError "Invalid address width")
  let some w := w.toNat? | throw (IO.userError "Invalid data width")
  MemoryStreamReplay.replay a w stimulus startup result
