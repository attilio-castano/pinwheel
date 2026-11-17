import Pinwheel.Hardware.Switch.Contract
import Lean.Data.Json

open Lean Pinwheel.Hardware.Switch

private def number (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"Expected natural number: {s}")

private def packet (outputs width : Nat) (j : Json) : Except String (Option (Packet outputs Nat)) := do
  if j == Json.null then return none
  let destination ← j.getObjValAs? Nat "destination"
  let payload ← j.getObjValAs? Nat "payload"
  if payload ≥ 2^width then throw "Payload exceeds width"
  if h : destination < outputs then return some ⟨⟨destination, h⟩, payload⟩
  else throw "Invalid logical destination"

private def input (extra outputs width : Nat) (j : Json) : Except String (Input extra outputs Nat) := do
  let reset ← j.getObjValAs? Bool "reset"
  let offered ← (← j.getObjVal? "offered").getArr?
  let ready ← j.getObjValAs? (Array Bool) "ready"
  unless offered.size = extra + 1 && ready.size = outputs do throw "Wrong input/output port count"
  let packets ← offered.mapM (packet outputs width)
  return ⟨reset, fun k => packets[k.val]!, fun o => ready[o.val]!⟩

private def packetJson (p : Packet outputs Nat) : Json :=
  Json.mkObj [("destination", toJson p.destination.val), ("payload", toJson p.payload)]

private def deliveryJson (d : Delivery extra outputs Nat) : Json :=
  Json.mkObj [("source", toJson d.source.val), ("destination", toJson d.packet.destination.val),
    ("payload", toJson d.packet.payload)]

private def optionalJson (f : α → Json) : Option α → Json
  | none => Json.null
  | some x => f x

private def observationJson (o : Output extra outputs Nat) : Json :=
  Json.mkObj [("ready", toJson (Array.ofFn o.ready)),
    ("offered", Json.arr (Array.ofFn (fun k => optionalJson deliveryJson (o.offered k))))]

private def stateJson (s : State extra outputs Nat) : Json :=
  Json.mkObj [("queues", Json.arr (Array.ofFn (fun k => Json.arr ((s.queues k).map packetJson).toArray))),
    ("slots", Json.arr (Array.ofFn (fun o => optionalJson deliveryJson (s.slots o)))),
    ("cursor", toJson (Array.ofFn (fun o => (s.cursor o).val)))]

/-- Freeze the functions at each edge; never retain a lazy transition history. -/
private def snapshot (s : State extra outputs Nat) : State extra outputs Nat :=
  let queues := Array.ofFn s.queues
  let slots := Array.ofFn s.slots
  let cursors := Array.ofFn s.cursor
  ⟨fun k => queues[k.val]!, fun o => slots[o.val]!, fun o => cursors[o.val]!⟩

def main (args : List String) : IO Unit := do
  let [ni, no, d, w, stimulus, result] := args
    | throw (IO.userError "Usage: switch_replay INPUTS OUTPUTS DEPTH WIDTH stimulus.jsonl trace.jsonl")
  let count ← number ni
  let outputs ← number no
  let depth ← number d
  let width ← number w
  unless count > 0 && outputs > 0 && depth > 0 && width > 0 do throw (IO.userError "All parameters must be positive")
  let extra := count - 1
  let mut s : State extra outputs Nat := initial
  let mut cycle := 0
  let mut rows : Array String := #[]
  for line in (← IO.FS.readFile stimulus).splitOn "\n" do
    if line.isEmpty then continue
    let i ← IO.ofExcept (input extra outputs width (← IO.ofExcept (Json.parse line)))
    let before := observationJson (observe depth i s)
    let grants := Json.arr (Array.ofFn (fun o => optionalJson (fun k => toJson k.val) (grant i s o)))
    s := snapshot (step depth i s)
    let row := Json.mkObj [("cycle", toJson cycle), ("pre", before),
      ("post", observationJson (observe depth i s)), ("grants", grants), ("state", stateJson s)]
    rows := rows.push row.compress
    cycle := cycle + 1
  IO.FS.writeFile result (String.intercalate "\n" rows.toList ++ "\n")
  IO.println s!"Switch model {count}/{outputs}/{depth}/{width}: {cycle} edges."
