import Pinwheel.Hardware.Reactive.FetchChoice

open Pinwheel.Hardware

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  -- Two zero-duration checked instructions: high pin 1 switches addresses,
  -- low pin 1 stays at the same address. Entry capture then replaces slot 15
  -- with pin 0, forcing the next terminal capture to take precedence again.
  let word0 := Execution.pack
    {kind := 2, levels := 1, enabled := 3,
     terminal := 63, entry := 61, finish := 2, sample := 15, yes := 1, no := 0}
  let word1 := Execution.pack
    {kind := 2, levels := 2, enabled := 3,
     terminal := 63, entry := 61, finish := 2, sample := 15, yes := 0, no := 1}
  let index : BitVec 8 → BitVec 6 := fun a => if a == 0 then 2 else 1
  let dictionary : BitVec 6 → BitVec 64 := fun k => if k == 2 then word0 else word1
  let read : Reactive.Fetch.Reader := fun a => dictionary (index a)
  let readExpr (address : Reactive.E 8) : Reactive.E 64 :=
    Execution.readTree 8 (fun a => .lit (read a)) address
  let indexExpr (address : Reactive.E 8) : Reactive.E 6 :=
    Execution.readTree 8 (fun a => .lit (index a)) address
  let recordChoice := Reactive.Fetch.selectionExpr Reactive.Fetch.branchExpr Reactive.Fetch.candidateExpr readExpr
  let indexChoice := Execution.readTree 6 (fun k => .lit (dictionary k))
    (Reactive.Fetch.selectionExpr Reactive.Fetch.branchExpr Reactive.Fetch.candidateExpr indexExpr)
  let mut state : Reactive.State := ⟨3, 0, 0, 0, {}, Vector.replicate 16 false⟩
  let mut staleDifferences := 0
  for n in [:128] do
    let incoming := BitVec.ofNat 2 (n % 4)
    let context : Reactive.Inputs := {incoming, current := read state.pc, last := 1}
    let r : Reactive.Fetch.Request := ⟨context, state⟩
    let expectedPC := if incoming[1] then state.pc ^^^ 1 else state.pc
    let reference := Reactive.stepValue (Reactive.Fetch.resolve context state read) state
    let records := Reactive.stepValue (Reactive.Fetch.resolveCandidates r read) state
    let indices := Reactive.stepValue (Reactive.Fetch.resolveIndexedCandidates r index dictionary) state
    ensure (recordChoice.eval context.values state.values == read expectedPC &&
      indexChoice.eval context.values state.values == read expectedPC)
      s!"structural candidate lookup at edge {n}"
    ensure (decide (records = reference ∧ indices = reference)) s!"candidate state mismatch at edge {n}"
    ensure (reference.pc == expectedPC && reference.mode == 3 && reference.remaining == 0 &&
      reference.pins.levels == (if expectedPC == 0 then 1 else 2) &&
      reference.samples[15] == incoming[0]) s!"one-cycle branch/capture schedule at edge {n}"
    let staleWord := read (Reactive.Fetch.candidateAddress r state.samples[15])
    let stale := Reactive.stepValue {context with successor := staleWord} state
    if stale != reference then staleDifferences := staleDifferences + 1
    state := reference
  ensure (staleDifferences > 0) "stale branch-selection mutation escaped"
  IO.println s!"Fetch choices: 128 consecutive one-cycle branches; stale-selection mutant differs on {staleDifferences} edges."
