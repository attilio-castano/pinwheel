import Pinwheel.Hardware.Switch.Circuit
import Lean.Data.Json

open Lean Pinwheel.Hardware Pinwheel.Hardware.Switch

namespace SwitchCircuitReplay

set_option backward.isDefEq.respectTransparency false

private def number (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"Expected natural number: {s}")

private def encoding (extraOutputs : Nat) : Physical.DestinationEncoding (extraOutputs + 1) :=
  ⟨extraOutputs.log2 + 1, by omega, Nat.succ_le_of_lt Nat.lt_log2_self⟩

private def pins (n m dw w : Nat) (j : Json) : Except String (Physical.Pins n m dw w) := do
  let reset ← j.getObjValAs? Bool "reset"
  let valid ← j.getObjValAs? (Array Bool) "valid"
  let destination ← j.getObjValAs? (Array Nat) "destination"
  let payload ← j.getObjValAs? (Array Nat) "payload"
  let ready ← j.getObjValAs? (Array Bool) "ready"
  unless valid.size = n+1 && destination.size = n+1 && payload.size = n+1 && ready.size = m+1 do
    throw "Wrong input/output port count"
  for d in destination do
    unless d < 2^dw do throw "Destination exceeds physical wire width"
  for p in payload do
    unless p < 2^w do throw "Payload exceeds physical wire width"
  return ⟨BitVec.ofBool reset, fun k => BitVec.ofBool valid[k.val]!,
    fun k => BitVec.ofNat dw destination[k.val]!, fun k => BitVec.ofNat w payload[k.val]!,
    fun o => BitVec.ofBool ready[o.val]!⟩

/-- Snapshot the complete typed enumeration at every edge. Later evaluation
reads only this array, never a chain of previous transition closures. -/
private def snapshot (d : Interface P) (values : Values P) : Array Nat :=
  d.ports.map (fun ⟨_, p⟩ => (values p).toNat)

private def values (d : Interface P) (bank : Array Nat) : Values P :=
  fun {w} p => BitVec.ofNat w bank[(d.position p).val]!

private def check (d : Interface P) (cycle : Nat) (phase : String) (actual expected : Array Nat) : IO Unit := do
  unless actual.size == d.size && expected.size == d.size do
    throw (IO.userError s!"Wrong snapshot size at {phase}")
  for ⟨w, p⟩ in d.ports do
    let index := (d.position p).val
    unless actual[index]! == expected[index]! do
      throw (IO.userError s!"Cycle {cycle} {phase}: {d.label p} ({w} bits) expected {expected[index]!}, got {actual[index]!}")

private def physicalJson (outputs : Values (Physical.Out n m w)) : Json :=
  Json.mkObj
    [("in_ready", toJson (Array.ofFn (fun k : Fin (n+1) => outputs (Physical.inReady k) == 1))),
     ("out_valid", toJson (Array.ofFn (fun o : Fin (m+1) => outputs (Physical.outValid o) == 1))),
     ("out_payload", toJson (Array.ofFn (fun o : Fin (m+1) => (outputs (Physical.outPayload o)).toNat)))]

private def optionalJson (f : α → Json) : Option α → Json
  | none => Json.null
  | some x => f x

private def packetJson (p : Packet outputs (BitVec w)) : Json :=
  Json.mkObj [("destination", toJson p.destination.val), ("payload", toJson p.payload.toNat)]

private def deliveryJson (d : Delivery n outputs (BitVec w)) : Json :=
  Json.mkObj [("source", toJson d.source.val), ("destination", toJson d.packet.destination.val),
    ("payload", toJson d.packet.payload.toNat)]

private def logicalJson (o : Switch.Output n outputs (BitVec w)) : Json :=
  Json.mkObj [("ready", toJson (Array.ofFn o.ready)),
    ("offered", Json.arr (Array.ofFn (fun k => optionalJson deliveryJson (o.offered k))))]

private def stateJson (s : Switch.State n outputs (BitVec w)) : Json :=
  Json.mkObj [("queues", Json.arr (Array.ofFn (fun k => Json.arr ((s.queues k).map packetJson).toArray))),
    ("slots", Json.arr (Array.ofFn (fun o => optionalJson deliveryJson (s.slots o)))),
    ("cursor", toJson (Array.ofFn (fun o => (s.cursor o).val)))]

private def snapshotState (s : Switch.State n outputs (BitVec w)) : Switch.State n outputs (BitVec w) :=
  let queues := Array.ofFn s.queues
  let slots := Array.ofFn s.slots
  let cursors := Array.ofFn s.cursor
  ⟨fun k => queues[k.val]!, fun o => slots[o.val]!, fun o => cursors[o.val]!⟩

private def startup (d : Interface P) (file : String) : IO (Array Nat) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let bank ← IO.ofExcept (fromJson? j : Except String (Array Nat))
  unless bank.size == d.size do throw (IO.userError "Wrong startup register count")
  for ⟨w, p⟩ in d.ports do
    unless bank[(d.position p).val]! < 2^w do
      throw (IO.userError s!"Startup register {d.label p} exceeds its width")
  return bank

def replay (n m depth w : Nat) (stimulus result : String) (startupFile : Option String) : IO Unit := do
  let e := encoding m
  let oi := Physical.outputInterface n m w
  let ri := Structural.registers n m e.width w depth
  let c := Structural.circuit e n w depth
  let mut model : Switch.State n (m+1) (BitVec w) := Switch.initial
  let mut bank := snapshot ri (Structural.encode e model)
  if let some file := startupFile then bank ← startup ri file
  let mut cycle := 0
  let mut rows : Array String := #[]
  for line in (← IO.FS.readFile stimulus).splitOn "\n" do
    if line.isEmpty then continue
    let raw ← IO.ofExcept (Json.parse line)
    let p ← IO.ofExcept (pins n m e.width w raw)
    if cycle == 0 && startupFile.isSome && p.reset != 1 then
      throw (IO.userError "Arbitrary startup registers require a first reset edge")
    let i := Physical.decode p
    let before := snapshot oi (c.observe p.values (values ri bank))
    let expectedBefore := snapshot oi (Physical.observe depth p model)
    check oi cycle "pre-output" before expectedBefore
    let logicalBefore := logicalJson (Switch.observe depth i model)
    let grants := Json.arr (Array.ofFn (fun o => optionalJson (fun k => toJson k.val) (Switch.grant i model o)))
    let nextBank := snapshot ri (c.step p.values (values ri bank))
    model := snapshotState (Switch.step depth i model)
    check ri cycle "post-state" nextBank (snapshot ri (Structural.encode e model))
    bank := nextBank
    let after := snapshot oi (c.observe p.values (values ri bank))
    check oi cycle "post-output" after (snapshot oi (Physical.observe depth p model))
    let logical := Json.mkObj [("pre", logicalBefore),
      ("post", logicalJson (Switch.observe depth i model)), ("grants", grants), ("state", stateJson model)]
    let row := Json.mkObj [("cycle", toJson cycle), ("input", raw),
      ("pre", physicalJson (values oi before)), ("post", physicalJson (values oi after)),
      ("pre_values", toJson before), ("post_values", toJson after),
      ("post_registers", toJson bank), ("logical", logical)]
    rows := rows.push row.compress
    cycle := cycle + 1
  if cycle == 0 then throw (IO.userError "Stimulus must contain at least one edge")
  IO.FS.writeFile result (String.intercalate "\n" rows.toList ++ "\n")
  IO.println s!"Switch circuit {n+1}/{m+1}/{depth}/{w}: {cycle} edges, all {oi.size} outputs pre/post and {ri.size} registers per edge matched."

end SwitchCircuitReplay

def main (args : List String) : IO Unit := do
  unless args.length == 6 || args.length == 7 do
    throw (IO.userError "Usage: switch_circuit_replay INPUTS OUTPUTS DEPTH WIDTH stimulus.jsonl trace.jsonl [startup-registers.json]")
  let count ← SwitchCircuitReplay.number args[0]!
  let outputs ← SwitchCircuitReplay.number args[1]!
  let depth ← SwitchCircuitReplay.number args[2]!
  let width ← SwitchCircuitReplay.number args[3]!
  unless count > 0 && outputs > 0 && depth > 0 && width > 0 do
    throw (IO.userError "All parameters must be positive")
  SwitchCircuitReplay.replay (count - 1) (outputs - 1) depth width args[4]! args[5]! args[6]?
