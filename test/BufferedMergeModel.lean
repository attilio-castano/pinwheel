import Lean
import Pinwheel.Hardware.Stream.BufferedMerge.Model

open Lean Elab Command
open Pinwheel.Hardware
open Pinwheel.Hardware.Stream
open Pinwheel.Hardware.Stream.BufferedMerge

namespace BufferedMergeModelTests

structure Frame where
  reset : Bool
  offers : Array (Option Nat)
  ready : Bool
  deriving Repr

/-- Occurrence serial numbers belong only to the independent oracle. Repeated
payloads from one or several sources are still separate accepted transactions. -/
structure Occurrence where
  source : Nat
  serial : Nat
  payload : Nat
  deriving BEq, Repr

structure Oracle where
  cursor : Nat
  slot : Option Occurrence
  nextSerial : Array Nat
  accepted : Array (Array Occurrence)
  delivered : Array (Array Occurrence)
  deriving Repr

structure Observation where
  ready : Array Bool
  offered : Option (Nat × Nat)
  deriving BEq, Repr

def emptyOracle (inputs : Nat) : Oracle :=
  ⟨0, none, Array.replicate inputs 0, Array.replicate inputs #[], Array.replicate inputs #[]⟩

/-- Integer modulo scan, with no calls to RoundRobin or BufferedMerge. -/
def choose (i : Frame) (s : Oracle) : Option Nat := Id.run do
  if i.reset || (s.slot.isSome && !i.ready) then return none
  let inputs := i.offers.size
  for offset in [0:inputs] do
    let candidate := (s.cursor+offset) % inputs
    if (i.offers[candidate]?.getD none).isSome then return some candidate
  return none

def oracleObserve (i : Frame) (s : Oracle) : Observation :=
  ⟨(Array.range i.offers.size).map (fun source => choose i s == some source),
    if i.reset then none else s.slot.map (fun value => (value.source, value.payload))⟩

def oracleStep (i : Frame) (s : Oracle) : Oracle := Id.run do
  if i.reset then return emptyOracle i.offers.size
  let mut next := s
  if i.ready then
    if let some value := s.slot then
      next := { next with delivered := next.delivered.modify value.source (·.push value) }
  if s.slot.isNone || i.ready then
    match choose i s with
    | none => next := { next with slot := none }
    | some source =>
      let payload := (i.offers[source]?.getD none).getD 0
      let serial := s.nextSerial[source]?.getD 0
      let value : Occurrence := ⟨source, serial, payload⟩
      next := { next with
        cursor := (source+1) % i.offers.size
        slot := some value
        nextSerial := next.nextSerial.set! source (serial+1)
        accepted := next.accepted.modify source (·.push value) }
  return next

def input (n : Nat) (f : Frame) : Input n Nat :=
  ⟨f.reset, fun k => f.offers[k.val]?.getD none, fun _ => f.ready⟩

def capture (n : Nat) (o : Output n Nat) : Observation :=
  ⟨(List.finRange (n+1)).toArray.map o.ready,
    (o.offered 0).map (fun value => (value.source.val, value.payload))⟩

def seedOracle (n : Nat) (s : State n Nat) : Oracle := Id.run do
  let mut oracle := { emptyOracle (n+1) with cursor := s.cursor.val }
  if let some value := s.slot then
    let occurrence : Occurrence := ⟨value.source.val, 0, value.payload⟩
    oracle := { oracle with
      slot := some occurrence
      nextSerial := oracle.nextSerial.set! value.source.val 1
      accepted := oracle.accepted.set! value.source.val #[occurrence] }
  return oracle

def seedHistory (s : State n Nat) : Multiport.History (n+1) 1 Nat (Delivery n Nat) :=
  ⟨fun source => (s.slot.toList.filter (fun value => value.source == source)).map Delivery.payload,
    fun _ => []⟩

def checkLedger (n : Nat) (s : State n Nat) (oracle : Oracle)
    (history : Multiport.History (n+1) 1 Nat (Delivery n Nat)) : IO Unit := do
  unless s.cursor.val == oracle.cursor &&
      s.slot.map (fun value => (value.source.val, value.payload)) ==
        oracle.slot.map (fun value => (value.source, value.payload)) do
    throw (IO.userError "merge state differs from integer/origin oracle")
  for source in List.finRange (n+1) do
    let accepted := oracle.accepted[source.val]?.getD #[]
    let delivered := oracle.delivered[source.val]?.getD #[]
    let pending := if let some value := oracle.slot then
      if value.source == source.val then #[value] else #[] else #[]
    unless accepted == delivered ++ pending do
      throw (IO.userError "occurrence ledger lost, duplicated, or reordered a transaction")
    unless (history.inputs source).toArray == accepted.map Occurrence.payload &&
        ((history.outputs 0).filter (fun value => value.source == source)).toArray.map Delivery.payload ==
          delivered.map Occurrence.payload do
      throw (IO.userError "logical source ledger differs from independent occurrence ledger")

def runFrom (n : Nat) (initial : State n Nat) (frames : Array Frame) : IO Nat := do
  let mut logical := initial
  let mut oracle := seedOracle n initial
  let mut history := seedHistory initial
  let mut edges := 0
  for f in frames do
    unless f.offers.size == n+1 do throw (IO.userError "incorrect oracle frame width")
    let i := input n f
    let actual := observe i logical
    unless capture n actual == oracleObserve f oracle do
      throw (IO.userError s!"edge {edges}: pre-edge handshake/provenance mismatch")
    history := history.advance i actual
    logical := step i logical
    oracle := oracleStep f oracle
    checkLedger n logical oracle history
    unless capture n (observe i logical) == oracleObserve f oracle do
      throw (IO.userError s!"edge {edges}: post-edge handshake/provenance mismatch")
    edges := edges+1
  return edges

def exhaustiveEdges (n : Nat) : IO Nat := do
  let sources := List.finRange (n+1)
  let slots : List (Option (Delivery n Nat)) := none :: sources.flatMap
    (fun source => [some ⟨source, 0⟩, some ⟨source, 1⟩])
  let mut edges := 0
  for cursor in sources do
    for slot in slots do
      for code in [0:3^(n+1)] do
        let offers := (Array.range (n+1)).map (fun k =>
          match code / 3^k % 3 with | 0 => none | 1 => some 0 | _ => some 1)
        for reset in [false, true] do
          for ready in [false, true] do
            edges := edges + (← runFrom n ⟨cursor, slot⟩ #[⟨reset, offers, ready⟩])
  return edges

def randomStep (seed : Nat) : Nat := (seed*1664525+1013904223) % 4294967296

/-- Offered data remain asserted until their source is accepted or reset.
Only three payload values are used, deliberately repeating across origins. -/
def traffic (inputs cycles : Nat) : Array Frame := Id.run do
  let mut frames := #[]
  let mut oracle := emptyOracle inputs
  let mut offers : Array (Option Nat) := Array.replicate inputs none
  let mut seed := 151+inputs
  for cycle in [0:cycles] do
    for source in [0:inputs] do
      seed := randomStep seed
      if (offers[source]?.getD none).isNone && seed % 4 != 0 then
        offers := offers.set! source (some (seed % 3))
    seed := randomStep seed
    let reset := cycle % 113 == 112
    let ready := cycle % 97 ≥ 31 && seed % 5 < 3
    let f : Frame := ⟨reset, offers, ready⟩
    frames := frames.push f
    let accepted := choose f oracle
    oracle := oracleStep f oracle
    if reset then offers := Array.replicate inputs none
    else if let some source := accepted then offers := offers.set! source none
  return frames

def fairnessChecks (n : Nat) : IO Nat := do
  let mut checked := 0
  for cursor in List.finRange (n+1) do
    for target in List.finRange (n+1) do
      let mut logical : State n Nat := ⟨cursor, some ⟨0, 1⟩⟩
      let mut opportunities := 0
      let mut served := false
      for cycle in [0:5*(n+1)+5] do
        let offers := (Array.range (n+1)).map (fun k =>
          if k == target.val || (cycle+k) % 3 != 0 then some 1 else none)
        let i := input n ⟨false, offers, cycle % 5 == 4⟩
        if logical.slot.isNone || i.ready 0 then opportunities := opportunities+1
        if (observe i logical).ready target then
          served := true
          unless opportunities ≤ n+1 do throw (IO.userError "persistent requester exceeded N refill opportunities")
          break
        logical := step i logical
      unless served do throw (IO.userError "persistent requester starved under repeated output service")
      checked := checked+1
  return checked

def negativeControls : IO Unit := do
  let start := emptyOracle 2
  let samePayload : Frame := ⟨false, #[some 7, some 7], false⟩
  let held := oracleStep samePayload start
  let observed := oracleObserve samePayload held
  unless observed.ready == #[false, false] && observed.offered == some (0, 7) do
    throw (IO.userError "full stalled output accepted another source or lost its origin")
  -- Distinct origin tags must remain visible even when all payload bits agree.
  let wrongOrigin := { observed with offered := some (1, 7) }
  if observed == wrongOrigin then throw (IO.userError "negative control: wrong origin was invisible")
  let wrongReady := { observed with ready := #[true, false] }
  if observed == wrongReady then throw (IO.userError "negative control: blocked acceptance was invisible")
  let reset : Frame := ⟨true, #[some 7, some 7], true⟩
  let afterReset := oracleStep reset held
  unless afterReset.slot.isNone && afterReset.cursor == 0 &&
      oracleObserve reset held == ⟨#[false, false], none⟩ do
    throw (IO.userError "reset retained an item or reported a canceled handshake")

end BufferedMergeModelTests

elab "#audit_buffered_merge" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Stream.BufferedMerge." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Stream.BufferedMerge." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty buffered-merge audit"
  logInfo m!"Buffered merge audit: {count} declarations, standard axioms only."

#audit_buffered_merge

def main : IO Unit := do
  let mut exhaustive := 0
  for n in [0, 1, 2] do
    exhaustive := exhaustive + (← BufferedMergeModelTests.exhaustiveEdges n)
  let mut traffic := 0
  let mut fairness := 0
  for n in [0, 1, 2, 4, 7] do
    traffic := traffic + (← BufferedMergeModelTests.runFrom n initial
      (BufferedMergeModelTests.traffic (n+1) 2000))
    fairness := fairness + (← BufferedMergeModelTests.fairnessChecks n)
  BufferedMergeModelTests.negativeControls
  IO.println s!"Buffered merge model: {exhaustive} exhaustive edges, {traffic} protocol-respecting stress edges, {fairness} cursor/target fairness cases; pre/post ports, complete state, and per-source occurrence ledgers agree with the independent integer oracle."
