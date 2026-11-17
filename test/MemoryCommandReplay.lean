import Pinwheel.Hardware.Memory.CommandFlops
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Memory

namespace MemoryCommandReplay

private def snapshot (d : Interface P) (values : Values P) : Array Nat :=
  d.ports.map (fun ⟨_, p⟩ => (values p).toNat)

private def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!

private def input (a w : Nat) (j : Json) : Except String (Values (CommandInterface.Input a w)) := do
  let enable ← j.getObjValAs? Bool "enable"
  let write ← j.getObjValAs? Bool "write"
  let address ← j.getObjValAs? Nat "address"
  let data ← j.getObjValAs? Nat "data"
  unless address < 2^a && data < 2^w do throw "Input exceeds wire width"
  return fun p => match p with
    | .enable => BitVec.ofBool enable
    | .write => BitVec.ofBool write
    | .address => BitVec.ofNat a address
    | .data => BitVec.ofNat w data

def replay (a w : Nat) (stimulus startup result : String) : IO Unit := do
  let ri := CommandFlops.registers a w
  let c := CommandFlops.circuit a w
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile startup))
  let mut bank ← IO.ofExcept (fromJson? raw : Except String (Array Nat))
  unless bank.size == ri.size do throw (IO.userError "Wrong startup register count")
  for value in bank do
    unless value < 2^w do throw (IO.userError "Startup word exceeds wire width")
  let mut rows : Array String := #[]
  let mut cycle := 0
  for line in (← IO.FS.readFile stimulus).splitOn "\n" do
    if line.isEmpty then continue
    let raw ← IO.ofExcept (Json.parse line)
    let i ← IO.ofExcept (input a w raw)
    let before := (c.observe i (values ri bank) .q).toNat
    bank := snapshot ri (c.step i (values ri bank))
    let after := (c.observe i (values ri bank) .q).toNat
    rows := rows.push (Json.mkObj [("cycle", toJson cycle), ("input", raw),
      ("pre", toJson before), ("post", toJson after), ("registers", toJson bank)]).compress
    cycle := cycle + 1
  if cycle == 0 then throw (IO.userError "Stimulus must contain at least one edge")
  IO.FS.writeFile result (String.intercalate "\n" rows.toList ++ "\n")
  IO.println s!"Command RAM {2^a}x{w}: {cycle} physical transitions replayed."

end MemoryCommandReplay

def main (args : List String) : IO Unit := do
  let [a, w, stimulus, startup, result] := args
    | throw (IO.userError "Usage: memory_command_replay ADDRESS_WIDTH DATA_WIDTH stimulus.jsonl startup.json trace.jsonl")
  let some a := a.toNat? | throw (IO.userError "Invalid address width")
  let some w := w.toNat? | throw (IO.userError "Invalid data width")
  MemoryCommandReplay.replay a w stimulus startup result
