import Pinwheel.Hardware.Memory.StreamModel

open Pinwheel.Hardware.Memory
open Pinwheel.Hardware.Memory.StreamModel

namespace MemoryStreamModelTests

structure Oracle where
  words : Array Nat
  q : Nat
  pending : Bool
  deriving BEq, Repr

def model (a w : Nat) (s : Oracle) : State a w :=
  ⟨⟨fun address => BitVec.ofNat w (s.words[address.toNat]?.getD 0), BitVec.ofNat w s.q⟩,
    s.pending⟩

def capture (a : Nat) (s : State a w) : Oracle :=
  ⟨(Array.range (2^a)).map (fun address => (s.memory.contents (BitVec.ofNat a address)).toNat),
    s.memory.q.toNat, s.pending⟩

/-- Independent array update and handshake oracle: no logical memory, decoder,
or adapter transition functions are used to calculate expected results. -/
def advance (i : Input a w) (s : Oracle) : Oracle :=
  if i.reset then { s with pending := false }
  else if s.pending && !i.ready then s
  else match i.offered with
    | none => { s with pending := false }
    | some (.read address) => { s with q := s.words[address.toNat]?.getD 0, pending := true }
    | some (.write address data) =>
      { s with words := s.words.set! address.toNat data.toNat, pending := false }

def expectedReads (i : Input a w) (s : Oracle) : List Nat :=
  if i.reset || (s.pending && !i.ready) then []
  else match i.offered with
    | some (.read address) => [s.words[address.toNat]?.getD 0]
    | _ => []

def checkEdge (a w : Nat) (label : String) (cycle : Nat) (i : Input a w) (s : Oracle) : IO Oracle := do
  let logical := model a w s
  let observation := (component a w).observe i logical
  let expectedReady := !i.reset && (!s.pending || i.ready)
  let expectedOffer := if !i.reset && s.pending then some s.q else none
  unless observation.ready == expectedReady && observation.offered.map BitVec.toNat == expectedOffer do
    throw (IO.userError s!"{label} edge {cycle}: wrong pre-edge observation")
  let expectedRequests := if expectedReady then i.offered.toList else []
  unless decide (acceptedRequests i logical = expectedRequests) do
    throw (IO.userError s!"{label} edge {cycle}: wrong accepted request")
  let expectedResponses := if !i.reset && i.ready && s.pending then [s.q] else []
  unless (emittedResponses i logical).map BitVec.toNat == expectedResponses do
    throw (IO.userError s!"{label} edge {cycle}: wrong response transfer")
  unless (acceptedReadValues i logical).map BitVec.toNat == expectedReads i s do
    throw (IO.userError s!"{label} edge {cycle}: wrong acceptance snapshot")
  let actual := capture a (step i logical)
  let expected := advance i s
  unless actual == expected do
    throw (IO.userError s!"{label} edge {cycle}: expected {repr expected}, got {repr actual}")
  let after := (component a w).observe i (model a w actual)
  let expectedAfter := if !i.reset && expected.pending then some expected.q else none
  unless after.offered.map BitVec.toNat == expectedAfter do
    throw (IO.userError s!"{label} edge {cycle}: wrong post-edge response")
  return actual

def offers (a w : Nat) : Array (Option (Request a w)) := Id.run do
  let mut result := #[none]
  for address in [0:2^a] do
    result := result.push (some (.read (BitVec.ofNat a address)))
    for data in [0:2^w] do
      result := result.push (some (.write (BitVec.ofNat a address) (BitVec.ofNat w data)))
  return result

def exhaustive (a w : Nat) : IO Nat := do
  let words := 2^a
  let values := 2^w
  let mut edges := 0
  for seed in [0:values^(words+1)] do
    for pending in [false, true] do
      let s : Oracle := ⟨(Array.range words).map (fun k => seed / values^k % values),
        seed / values^words % values, pending⟩
      for reset in [false, true] do
        for ready in [false, true] do
          for request in offers a w do
            let _ ← checkEdge a w s!"exhaustive a{a} w{w}" edges ⟨reset, request, ready⟩ s
            edges := edges + 1
  return edges

def directed : IO Nat := do
  let initial : Oracle := ⟨#[17, 88, 33, 44], 123, true⟩
  -- A reset cancels an arbitrary preexisting response and refuses an offered
  -- write. Next, blocked reads/writes cannot overwrite Q. Retire/refill uses the
  -- old Q for delivery and the addressed word for the new pending response.
  let inputs : Array (Input 2 8) := #[
    ⟨true, some (.write 1 255), true⟩,
    ⟨false, some (.read 1), false⟩,
    ⟨false, some (.read 2), false⟩,
    ⟨false, some (.write 1 7), false⟩,
    ⟨false, some (.read 2), true⟩,
    ⟨false, some (.write 2 157), true⟩,
    ⟨false, some (.read 2), false⟩,
    ⟨true, some (.read 0), true⟩,
    ⟨false, none, true⟩,
    ⟨false, some (.read 2), true⟩,
    ⟨false, none, true⟩]
  let expectedResponses : Array (List Nat) := #[[], [], [], [], [88], [33], [], [], [], [], [157]]
  let mut s := initial
  let mut history : History 2 8 := {}
  for cycle in [0:inputs.size] do
    let i := inputs[cycle]?.getD ⟨false, none, false⟩
    let logical := model 2 8 s
    let actualResponses := (emittedResponses i logical).map BitVec.toNat
    unless actualResponses == expectedResponses[cycle]! do
      throw (IO.userError s!"directed edge {cycle}: explicit delivery sequence failed")
    history := history.advance i logical
    s ← checkEdge 2 8 "directed" cycle i s
    unless decide (history.reads = history.responses ++ pendingValues (model 2 8 s)) do
      throw (IO.userError s!"directed edge {cycle}: epoch ledger failed")
  unless s == ⟨#[17, 88, 157, 44], 157, false⟩ do
    throw (IO.userError "directed final memory differs; reset must preserve committed writes")
  unless history.requests.length == 1 && history.reads.map BitVec.toNat == [157] &&
      history.responses.map BitVec.toNat == [157] do
    throw (IO.userError "reset did not cancel the previous transaction epoch")
  return inputs.size

def longTrace : IO Nat := do
  let mut s : Oracle := ⟨#[5, 47, 169, 63, 213, 8, 71, 254], 137, false⟩
  let mut history : History 3 8 := {}
  for cycle in [0:240] do
    let request : Option (Request 3 8) :=
      if cycle % 9 == 0 then none
      else if cycle % 5 < 2 then some (.write (BitVec.ofNat 3 (cycle * 13)) (BitVec.ofNat 8 (cycle * 41)))
      else some (.read (BitVec.ofNat 3 (cycle * 13 + 7)))
    let i : Input 3 8 := ⟨cycle % 43 == 0, request, cycle % 17 > 6⟩
    history := history.advance i (model 3 8 s)
    s ← checkEdge 3 8 "long trace" cycle i s
    unless decide (history.reads = history.responses ++ pendingValues (model 3 8 s)) do
      throw (IO.userError s!"long trace edge {cycle}: epoch ledger failed")
  return 240

example (i : Input a w) (s : State a w) (hr : i.reset = true) :
    (step i s).memory = s.memory := by
  simpa using congrArg (fun t : State a w => t.memory) (reset_state i s hr)

example (i : Input a w) (s : State a w) (hr : i.reset = true) (inputs : List (Input a w)) :
    let result := runHistory (step i s) {} inputs
    result.2.reads = result.2.responses ++ pendingValues result.1 :=
  history_after_reset i s hr inputs

end MemoryStreamModelTests

def main : IO Unit := do
  let mut exhaustive := 0
  exhaustive := exhaustive + (← MemoryStreamModelTests.exhaustive 1 2)
  exhaustive := exhaustive + (← MemoryStreamModelTests.exhaustive 0 2)
  exhaustive := exhaustive + (← MemoryStreamModelTests.exhaustive 0 0)
  let directed ← MemoryStreamModelTests.directed
  let trace ← MemoryStreamModelTests.longTrace
  IO.println s!"Memory stream model: {exhaustive} exhaustive state/input edges, {directed} directed edges, {trace} trace edges; observations, transfers, snapshots, state and epoch ledgers agree."
