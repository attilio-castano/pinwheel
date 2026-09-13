import Pinwheel

open Pinwheel.Engine.Reactive
open Pinwheel.Engine.Reactive.Counted

private def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def serialProgram (byte : BitVec 8) (pin : Fin 3) (enable msbFirst invert : Bool) :
    Counted.Program :=
  ⟨.seq (.repeat 1 (.repeat 7 (.emit
      (.action (.serial ⟨5, 6⟩ pin enable ⟨.loop 1, .loop 0, msbFirst, invert⟩) 0))))
      (.emit .halt),
    #v[byte, ~~~byte], {}, by exact (show 17 ≤ 128 from by decide),
    by exact (show 5 ≤ 64 from by decide), by exact (show 2 ≤ 2 from by decide)⟩

private def serialization : IO Unit := do
  let mut cases := 0
  for byte in [:256] do
    for pin in ([0, 1, 2] : List (Fin 3)) do
      for enable in [false, true] do
        for msbFirst in [false, true] do
          for invert in [false, true] do
            let p := serialProgram (BitVec.ofNat 8 byte) pin enable msbFirst invert
            let mut state := Fetch.start p.store 0
            for i in [:16] do
              let value := (if i < 8 then byte else 255 - byte).testBit
                (if msbFirst then 7 - i % 8 else i % 8) != invert
              for j in [:3] do
                let expectedLevel := if j == pin.val && !enable then value else (5 : Nat).testBit j
                let expectedEnable := if j == pin.val && enable then value else (6 : Nat).testBit j
                ensure (state.pins.levels[j]! == expectedLevel && state.pins.enabled[j]! == expectedEnable)
                  s!"serial operand mismatch byte={byte} step={i} pin={j}"
              ensure (busy state) "loop ended before its final bit"
              state := Fetch.advance p.store state 0
            ensure (state.control == .stopped .completed && state.pins == {}) "loop/halt boundary"
            cases := cases + 1
  IO.println s!"Passed {cases} generic two-byte serial loops: both bit orders, both polarities, every output field/pin."

private def invalidOperands : IO Unit := do
  let badData : Counted.Program :=
    ⟨.emit (.action (.serial {} 1 true ⟨.literal 7, .literal 0, true, true⟩) 0),
      #v[0, 0], {}, by decide, by decide, by decide⟩
  ensure ((Fetch.start badData.store 0).control == .stopped .fault) "bad data index did not fault on entry"
  ensure ((Fetch.start badData.store 0).pins == {}) "bad fetch did not release pins"
  ensure (Target.next.eval 127 == none) "next target wrapped"
  let badJump : Counted.Program :=
    ⟨.emit (.checked (.literal (.openDrain 3)) 0 ⟨0, 0⟩ none (some ⟨1, .literal 2⟩)
      (.jump (.absolute 127))), #v[0, 0], {}, by decide, by decide, by decide⟩
  let stopped := Fetch.advance badJump.store (Fetch.start badJump.store 0) 2
  ensure (stopped.control == .stopped .fault && stopped.samples[2] && stopped.pins == {})
    "invalid jump failed to retain terminal capture or release pins"
  let m : Fetch.Machine := ⟨badJump.store, Fetch.start badJump.store 0⟩
  let (rejected, accepted) := Fetch.load m badData.store
  ensure (!accepted && rejected.state == m.state) "busy load accepted"
  let reset := Fetch.step badJump.store m.state true true 3
  let (loaded, accepted) := Fetch.load ⟨badJump.store, reset⟩ badData.store
  ensure (accepted && loaded.state == Fetch.reset badData.store) "stopped load failed"
  ensure ((Fetch.start loaded.program 0).control == .stopped .fault) "replacement used stale program"
  IO.println "Passed invalid data/jump, no-wrap, terminal capture, reset, and busy/stopped loading checks."

def main : IO Unit := do
  serialization
  invalidOperands
