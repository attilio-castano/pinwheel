import Pinwheel.Hardware.Storage.FetchContract

open Pinwheel.Hardware

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- Enter each valid program from rest, then distinguish two images differing
only in terminal-capture enable bit 35. A stale-sample branch gives the wrong
PC in the enabled image. The next-address requirement is checked on that edge. -/
def main : IO Unit := do
  let branch (capture : Bool) := Execution.pack
    {kind := 2, terminal := if capture then 1 else 0, finish := 2, yes := 1, no := 0}
  let action := Execution.pack {}
  ensure (branch true ^^^ branch false == (1 <<< 35)) "witness must change only capture enable"
  for capture in [false, true] do
    let word := branch capture
    let read : Reactive.Fetch.Reader := fun pc => if pc == 0 then word else action
    ensure (Execution.validValue word && Execution.validValue action) "witness words must be valid"
    let initial : Reactive.State := ⟨0, 0, 0, 0, {}, Vector.replicate 16 false⟩
    let started := Reactive.stepValue
      (Reactive.Fetch.resolve {start := true, last := 2} initial read) initial
    ensure (started.mode == 3 && started.pc == 0 && started.remaining == 0 && !started.samples[0])
      "start must enter a one-cycle checked record with a clear sample"
    let context : Reactive.Inputs := {incoming := 1, current := word, last := 2}
    let resolved := Reactive.Fetch.resolve context started read
    let next := Reactive.stepValue resolved started
    let selected := Reactive.Fetch.forwardedBranchExpr.eval context.values started.values
    ensure (selected == BitVec.ofBool capture && next.pc == (if capture then 1 else 0))
      "capture on the dispatch edge must determine the entered PC"
    ensure (Storage.Dispatch.candidate resolved started false == (if capture then 2 else 0))
      "the same edge must request the entered instruction's next candidate"
    ensure (next.mode == (if capture then 1 else 3) && next.remaining == 0)
      "forwarding must not add an execution cycle"
  IO.println "Fetch contract: valid programs entered from rest distinguish capture bit 35, same-edge branch selection, and the next candidate address."
