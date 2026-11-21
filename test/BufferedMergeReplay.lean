import Pinwheel.Hardware.Stream.BufferedMerge.Circuit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Stream.BufferedMerge

namespace BufferedMergeReplay

private def number (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"Expected natural number: {s}")

private def pins (n w : Nat) (j : Json) : Except String (Physical.Pins n w) := do
  let reset ← j.getObjValAs? Bool "reset"
  let ready ← j.getObjValAs? Bool "ready"
  let valid ← j.getObjValAs? (Array Bool) "valid"
  let payload ← j.getObjValAs? (Array Nat) "payload"
  unless valid.size = n+1 && payload.size = n+1 do throw "Wrong input port count"
  for value in payload do
    unless value < 2^w do throw "Payload exceeds physical wire width"
  return ⟨BitVec.ofBool reset, BitVec.ofBool ready, fun k => BitVec.ofBool valid[k.val]!,
    fun k => BitVec.ofNat w payload[k.val]!⟩

private def snapshot (d : Interface P) (s : Values P) : Array Nat :=
  d.ports.map (fun ⟨_, p⟩ => (s p).toNat)

private def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!

private def check (d : Interface P) (cycle : Nat) (phase : String) (actual expected : Array Nat) : IO Unit := do
  unless actual.size == d.size && expected.size == d.size do throw (IO.userError "Wrong snapshot size")
  for ⟨_, p⟩ in d.ports do
    let k := (d.position p).val
    unless actual[k]! == expected[k]! do
      throw (IO.userError s!"Cycle {cycle} {phase}: {d.label p}, expected {expected[k]!}, got {actual[k]!}")

private def physicalJson (o : Values (Physical.Out n w)) : Json :=
  Json.mkObj
    [("in_ready", toJson (Array.ofFn (fun k : Fin (n+1) => o (Physical.inReady k) == 1))),
     ("out_valid", toJson (o Physical.outValid == 1)), ("out_payload", toJson ((o Physical.outPayload).toNat))]

private def optionalJson (f : α → Json) : Option α → Json
  | none => Json.null
  | some x => f x

private def deliveryJson (d : Delivery n (BitVec w)) : Json :=
  Json.mkObj [("source", toJson d.source.val), ("payload", toJson d.payload.toNat)]

private def logicalJson (o : Output n (BitVec w)) : Json :=
  Json.mkObj [("ready", toJson (Array.ofFn o.ready)), ("offered", optionalJson deliveryJson (o.offered 0))]

private def stateJson (s : State n (BitVec w)) : Json :=
  Json.mkObj [("slot", optionalJson deliveryJson s.slot), ("cursor", toJson s.cursor.val)]

private def startup (d : Interface P) (file : String) : IO (Array Nat) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let bank ← IO.ofExcept (fromJson? j : Except String (Array Nat))
  unless bank.size == d.size do throw (IO.userError "Wrong startup register count")
  for ⟨w, p⟩ in d.ports do
    unless bank[(d.position p).val]! < 2^w do throw (IO.userError "Startup register exceeds its width")
  return bank

def replay (n w : Nat) (stimulus result : String) (startupFile : Option String) : IO Unit := do
  let oi := Physical.outputInterface n w
  let ri := Structural.registers n w
  let c := Structural.circuit n w
  let mut model : State n (BitVec w) := initial
  let mut bank := snapshot ri (Structural.encode model)
  if let some file := startupFile then bank ← startup ri file
  let mut cycle := 0
  let mut rows : Array String := #[]
  for line in (← IO.FS.readFile stimulus).splitOn "\n" do
    if line.isEmpty then continue
    let raw ← IO.ofExcept (Json.parse line)
    let p ← IO.ofExcept (pins n w raw)
    if cycle == 0 && startupFile.isSome && p.reset != 1 then
      throw (IO.userError "Arbitrary startup registers require a first reset edge")
    let i := Physical.decode p
    let before := snapshot oi (c.observe p.values (values ri bank))
    check oi cycle "pre-output" before (snapshot oi ((Physical.component n w).observe p.values model))
    let logicalBefore := logicalJson (observe i model)
    let granted := optionalJson (fun k => toJson k.val) (grant i model)
    let next := snapshot ri (c.step p.values (values ri bank))
    model := step i model
    check ri cycle "post-state" next (snapshot ri (Structural.encode model))
    bank := next
    let after := snapshot oi (c.observe p.values (values ri bank))
    check oi cycle "post-output" after (snapshot oi ((Physical.component n w).observe p.values model))
    rows := rows.push (Json.mkObj [("cycle", toJson cycle), ("input", raw),
      ("pre", physicalJson (values oi before)), ("post", physicalJson (values oi after)),
      ("pre_values", toJson before), ("post_values", toJson after), ("post_registers", toJson bank),
      ("logical", Json.mkObj [("pre", logicalBefore), ("post", logicalJson (observe i model)),
        ("grant", granted), ("state", stateJson model)])]).compress
    cycle := cycle+1
  if cycle == 0 then throw (IO.userError "Stimulus must contain at least one edge")
  IO.FS.writeFile result (String.intercalate "\n" rows.toList ++ "\n")
  IO.println s!"Buffered merge {n+1}/{w}: {cycle} edges, all {oi.size} outputs pre/post and {ri.size} registers matched."

end BufferedMergeReplay

def main (args : List String) : IO Unit := do
  unless args.length == 4 || args.length == 5 do
    throw (IO.userError "Usage: BufferedMergeReplay INPUTS WIDTH stimulus.jsonl trace.jsonl [startup-registers.json]")
  let count ← BufferedMergeReplay.number args[0]!
  let w ← BufferedMergeReplay.number args[1]!
  unless count > 0 && w > 0 do throw (IO.userError "Input count and payload width must be positive")
  BufferedMergeReplay.replay (count-1) w args[2]! args[3]! args[4]?
