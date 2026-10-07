import Pinwheel.Program.Transfer
import Lean.Data.Json

/-! Deterministic finite command/transition vectors evaluated by the actual
Lean ownership model. A cross-language consumer may compare these observations;
such a comparison is finite differential evidence, not universal refinement.
The model is one slot on one device. Wrapper instance identity is outside these
nonwrapping epoch/sequence observations. Stdout contains only one JSON object. -/
open Lean (Json toJson)
open Pinwheel.Program.Transfer

private def outcomeName : Outcome → String
  | .complete => "complete"
  | .timeout => "timeout"
  | .fault => "fault"

private def rejectionName : Rejection → String
  | .wrongIdentity => "wrong_identity"
  | .wrongPhase => "wrong_phase"
  | .capacity => "capacity"
  | .programGeneration => "program_generation"
  | .txExhausted => "tx_exhausted"
  | .rxFull => "rx_full"

private def replyJson (reply : Reply) : Json :=
  let accepted := match reply with | .rejected _ => false | _ => true
  let reason := match reply with | .rejected reason => toJson (rejectionName reason) | _ => Json.null
  let bit := match reply with | .txBit bit => toJson bit | _ => Json.null
  Json.mkObj [("accepted", toJson accepted), ("reason", reason), ("tx_bit", bit)]

private def dataFields (request : Option Request) (consumed : Nat) (rx : List Bool)
    (outcome : Option Outcome) : List (String × Json) :=
  [("identity", match request with | some r => toJson [r.identity.epoch, r.identity.sequence] | none => Json.null),
    ("program_generation", match request with | some r => toJson r.programGeneration | none => Json.null),
    ("tx_bits", toJson (request.map Request.tx |>.getD [])),
    ("tx_consumed_bits", toJson consumed),
    ("rx_limit", toJson (request.map Request.rxLimit |>.getD 0)),
    ("rx_bits", toJson rx),
    ("outcome", match outcome with | some o => toJson (outcomeName o) | none => Json.null)]

private def stateJson (edge : Transition) : Json :=
  let (phase, fields) := match edge.state.slot with
    | .free => ("free", dataFields none 0 [] none)
    | .preparing r => ("preparing", dataFields (some r) 0 [] none)
    | .running e => ("running", dataFields (some e.request) e.txConsumed e.rx none)
    | .completed c => ("completed", dataFields (some c.execution.request) c.execution.txConsumed c.execution.rx (some c.outcome))
  Json.mkObj ([("phase", toJson phase), ("epoch", toJson edge.state.epoch),
    ("next_sequence", toJson edge.state.nextSequence), ("reply", replyJson edge.reply)] ++ fields)

private def idFields (id : Identity) : List (String × Json) :=
  [("epoch", toJson id.epoch), ("sequence", toJson id.sequence)]

private def commandJson : Command → Json
  | .prepare generation tx rxLimit => Json.mkObj [("kind", toJson "prepare"),
      ("program_generation", toJson generation), ("tx_bits", toJson tx), ("rx_limit", toJson rxLimit)]
  | .start id generation => Json.mkObj ([("kind", toJson "start"),
      ("program_generation", toJson generation)] ++ idFields id)
  | .consumeTx id => Json.mkObj ([("kind", toJson "consume")] ++ idFields id)
  | .appendRx id bit => Json.mkObj ([("kind", toJson "append"), ("bit", toJson bit)] ++ idFields id)
  | .finish id outcome => Json.mkObj ([("kind", toJson "finish"),
      ("outcome", toJson (outcomeName outcome))] ++ idFields id)
  | .read id => Json.mkObj ([("kind", toJson "read")] ++ idFields id)
  | .release id => Json.mkObj ([("kind", toJson "release")] ++ idFields id)
  | .reset => Json.mkObj [("kind", toJson "reset")]

private def commands (capacity : Capacity) (outcome : Outcome) : List Command := Id.run do
  let id : Identity := ⟨0, 1⟩
  let next : Identity := ⟨0, 2⟩
  let reset : Identity := ⟨1, 1⟩
  let tx := (List.range capacity.txBits).map fun n => n % 3 == 1
  let txCount := if outcome == .complete then capacity.txBits else capacity.txBits / 2
  let rxCount := if outcome == .complete then capacity.rxBits else capacity.rxBits / 2
  let mut result : List Command := [
    .release id,
    .prepare 7 (List.replicate (capacity.txBits + 1) false) 0,
    .prepare 7 [] (capacity.rxBits + 1),
    .prepare 7 tx capacity.rxBits,
    .start id 8,
    .appendRx next true,
    .release id,
    .start id 7,
    .prepare 7 [] 0,
    .start id 7,
    .read id,
    .release id]
  result := result ++ List.replicate txCount (.consumeTx id)
  if outcome == .complete then result := result ++ [.consumeTx id]
  result := result ++ ((List.range rxCount).map fun n => .appendRx id (n % 2 == 0))
  if outcome == .complete then result := result ++ [.appendRx id false]
  result := result ++ [
    .finish id outcome,
    .read id, .read id,
    .consumeTx id,
    .appendRx id true,
    .finish id .fault,
    .prepare 8 tx capacity.rxBits,
    .release next,
    .release id,
    .prepare 8 tx capacity.rxBits,
    .read id,
    .release id,
    .reset,
    .prepare 8 tx capacity.rxBits,
    .start next 8,
    .release id,
    .start reset 8,
    .finish reset .complete,
    .read reset,
    .release reset]
  return result

private def caseJson (capacity : Capacity) (outcome : Outcome) : Json := Id.run do
  let cs := commands capacity outcome
  let mut s : State := {}
  let mut states : Array Json := #[]
  for command in cs do
    let edge := step capacity s command
    states := states.push (stateJson edge)
    s := edge.state
  return Json.mkObj [("tx_capacity_bits", toJson capacity.txBits),
    ("rx_capacity_bits", toJson capacity.rxBits),
    ("commands", toJson (cs.map commandJson)), ("states", Json.arr states)]

def main : IO Unit := do
  let mut cases : Array Json := #[]
  for txCapacity in [:5] do
    for rxCapacity in [:5] do
      for outcome in [Outcome.complete, .timeout, .fault] do
        cases := cases.push (caseJson ⟨txCapacity, rxCapacity⟩ outcome)
  IO.println (Json.mkObj [("schema", toJson "pinwheel-transfer-vectors-v1"),
    ("cases", Json.arr cases)]).compress
