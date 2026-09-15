import Pinwheel.Hardware.Storage.CacheContract

open Pinwheel.Hardware

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  -- A latency change must be visible even if the eventual values agree.
  let register : Timed.Component Bool Bool Bool := ⟨fun i _ => i, fun _ s => s⟩
  let delayed : Timed.Component Bool (Bool × Bool) Bool :=
    ⟨fun i s => (i, s.1), fun _ s => s.2⟩
  ensure (register.trace false [true, false] == [(false, true), (true, false)])
    "pre/post-edge observation convention"
  ensure (register.trace false [true, false] != delayed.trace (false, false) [true, false])
    "extra-cycle mutation escaped the timed trace"
  -- Old slot 15 is false. The terminal capture must select the yes address on
  -- this edge; a second capture at successor entry then overwrites the slot.
  let word := Execution.pack {kind := 2, terminal := 63, finish := 2, sample := 15, yes := 1, no := 2}
  let core : Reactive.State := ⟨3, 0, 0, 0, {}, Vector.replicate 16 false⟩
  let context : Reactive.Inputs := ⟨false, false, 2, {}, 2, word, 4⟩
  let read : Reactive.Fetch.Reader := fun a => if a == 1 then
    Execution.pack {kind := 0, levels := 5, enabled := 7, entry := 61} else 4
  let request : Reactive.Fetch.Request := ⟨context, core⟩
  let resolved := Reactive.Fetch.resolve context core read
  let after := Reactive.stepValue resolved core
  ensure (request.address == 1 && after.pc == 1 && after.pins.levels == 5 && !after.samples[15])
    "terminal capture, branch, successor entry order"
  ensure ((Reactive.Fetch.Request.address ⟨{context with incoming := 0}, core⟩) == 2)
    "branch must respond to the current input"
  ensure (resolved.successor == read 1)
    "selected successor must be available on this edge"
  IO.println "Timed contracts: edge phases, latency mutation, terminal capture and successor entry passed."
