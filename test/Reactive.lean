import Pinwheel

open Pinwheel
open Pinwheel.Engine.Reactive

private def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def inputs (scl sda : Bool) : Inputs :=
  BitVec.ofNat 2 ((if scl then 1 else 0) + (if sda then 2 else 0))

/-- Independent bus resolution. Open-drain commands must never actively drive high. -/
private def observe (pins : Pins) (targetClockLow : Bool) : IO Inputs := do
  ensure (pins.enabled &&& pins.levels == 0) "active-high drive in open-drain pulse"
  ensure (!pins.enabled[2]) "unassigned output was enabled"
  return inputs (!pins.enabled[0] && !targetClockLow) (!pins.enabled[1])

private def pulse (d w : Fin 256) (blocked : Nat) (data : Bool) (trace : Bool := false)
    (transition : Program → State → Inputs → State := advance) : IO Nat := do
  ensure (blocked <= w.val) "harness requires readiness before timeout"
  let h := d.val + 1
  let p := Compile.StretchedPulse.program d w data
  let readyAt := h + blocked + 1
  let fallAt := readyAt + h
  let doneAt := fallAt + h
  let mut s := start p 3
  let mut csv := "cycle,scl,sda,clock_enabled,data_enabled,target_clock_low,busy,sample0\n"
  for t in [:doneAt + 2] do
    -- A target holds the released clock low for exactly `blocked` observations.
    let targetLow := h <= t && t < h + blocked
    let bus ← observe s.pins targetLow
    let expectedClockLow := t < h || (fallAt <= t && t < doneAt)
    ensure (s.pins.enabled[0] == expectedClockLow) s!"clock command deadline at {t}"
    ensure (s.pins.enabled[1] == (!data && t < doneAt)) s!"data command deadline at {t}"
    ensure (bus[0] == (!expectedClockLow && !targetLow)) s!"resolved clock at {t}"
    ensure (busy s == (t < doneAt)) s!"completion deadline at {t}"
    ensure (s.samples[0] == (data && fallAt <= t)) s!"capture boundary at {t}"
    for slot in [1:8] do ensure (!s.samples[slot]!) "wrong capture destination"
    ensure (result s == if t < doneAt then none else some s.samples) "result visibility"
    ensure (step p s true true bus == reset p) "reset priority during pulse"
    if t < doneAt then
      ensure (step p s false true bus == advance p s bus) "busy start changed pulse"
      ensure (load ⟨p, s⟩ (embedProgram (Compile.UART.program ⟨0⟩ 0xa6)) == (⟨p, s⟩, false))
        "busy replacement changed pulse"
    if trace then
      let bit := fun b => if b then 1 else 0
      csv := csv ++ s!"{t},{bit bus[0]},{bit bus[1]},{bit s.pins.enabled[0]},{bit s.pins.enabled[1]},{bit targetLow},{bit (busy s)},{bit s.samples[0]}\n"
    s := transition p s bus
  if trace then IO.FS.writeFile "build/reactive/stretched-pulse.csv" csv
  return doneAt + 2

private def boundaries : IO Unit := do
  let slots : Engine.Samples := Vector.replicate 8 true
  for k in [:256] do
    let w : Fin 256 := Fin.ofNat 256 k
    for source in ([0, 1] : List (Fin 2)) do
      for level in [false, true] do
        let wait : Wait := ⟨.openDrain 2, ⟨source, level⟩, w⟩
        let action : Action := ⟨.openDrain 1, w, some ⟨source, 3⟩⟩
        let p : Program := ⟨Vector.ofFn (fun pc => if pc.val == 0 then .wait wait
          else if pc.val == 1 then .action action else .halt), {}, 31⟩
        let bus := fun value => if source.val == 0 then inputs value (!value) else inputs (!value) value
        let mut s := enter p 0 slots (bus level)
        ensure (s.control == .waiting 0 w && s.samples == slots) "wait used pre-command entry observation"
        for n in [:k + 1] do
          let ready := advance p s (bus level)
          ensure (ready.control == .active 1 w && ready.pins == action.pins) "ready lost or timer not fresh"
          ensure (ready.samples[3] == level && ready.samples[0]) "ready-edge capture selection"
          let mut timed := ready
          -- Check all durations once per budget/source/polarity, including duration one.
          if n == k then
            for _ in [:k] do
              timed := advance p timed (bus (!level))
              ensure (busy timed && timed.samples == ready.samples) "duration or sample retention"
            timed := advance p timed (bus (!level))
            ensure (timed.control == .stopped .completed) "timed boundary after readiness"
          s := advance p s (bus (!level))
          if n < k then
            ensure (s.control == .waiting 0 (Fin.ofNat 256 (k - n - 1)) &&
              s.pins == wait.pins && s.samples == slots) "blocked wait mutated pins/samples/PC"
        ensure (s.control == .stopped .timeout && s.pins == p.idle && s.samples == slots && result s == none)
          "persistent blocking timeout"
        ensure (advance p s 3 == s) "timeout did not retain state"
        ensure (step p s false true 3 == start p 3) "timeout restart"
        let (loaded, accepted) := load ⟨p, s⟩ p
        ensure (accepted && loaded.state == reset p) "reload after timeout"
  let p := Compile.StretchedPulse.program 0 0 true
  ensure ((advance p ⟨.waiting 0 0, {}, slots⟩ 3).control == .stopped .fault) "invalid wait PC"
  let last : Program := ⟨Vector.replicate 128 (.wait ⟨{}, ⟨0, true⟩, 0⟩), {}, 31⟩
  ensure ((advance last (enter last 31 slots 0) 1).control == .stopped .fault) "ready wait wrapped at slot 31"
  ensure ((advance last (enter last 31 slots 0) 0).control == .stopped .timeout) "last-slot timeout"
  IO.println "Passed all 256 wait budgets and durations, both inputs/polarities, deadline readiness, capture, timeout/restart/reload, and malformed/final-slot waits."

private def legacy : IO Unit := do
  for d in ([0, 3] : List (Fin 256)) do
    for byte in [:256] do
      let value := BitVec.ofNat 8 byte
      for isSPI in [false, true] do
        let p := if isSPI then Compile.SPI.program ⟨d⟩ value else Compile.UART.program ⟨d⟩ value
        let q := embedProgram p
        let endAt := (if isSPI then 17 else 10) * (d.val + 1)
        let incoming := fun t => inputs (t % 3 == 0) (t % 2 == 0)
        let mut original := Engine.start p (incoming 0)[0]
        let mut extended := start q (incoming 0)
        for t in [:endAt + 2] do
          ensure (extended == embedState original) "legacy state compatibility"
          let expected := if isSPI then Compile.SPI.encodePins (SPI.expectedPins ⟨d⟩ value t)
            else Compile.UART.encodePin (UART.expected ⟨d⟩ value t)
          ensure (extended.pins == Pins.pushPull expected) "legacy independent waveform"
          if isSPI then
            ensure (extended.samples == SPI.expectedSamples ⟨d⟩ (fun t => (incoming t)[0]) t)
              "legacy independent SPI samples"
          original := Engine.advance p original (incoming (t + 1))[0]
          extended := advance q extended (incoming (t + 1))
  -- One machine successively receives old and new instruction families.
  let programs := [embedProgram (Compile.UART.program ⟨0⟩ 0x53),
    embedProgram (Compile.SPI.program ⟨0⟩ 0xa6), Compile.StretchedPulse.program 3 7 true,
    embedProgram (Compile.UART.program ⟨3⟩ 0xff)]
  let seed := embedProgram (Compile.UART.program ⟨0⟩ 0x53)
  let mut m : Machine := ⟨seed, reset seed⟩
  for p in programs do
    let (next, accepted) := load m p
    ensure (accepted && next.state == reset p) "mixed reload failed to reset state"
    m := {next with state := start p 3}
    for t in [:128] do
      -- For the pulse this delays readiness without relying on its instruction PC.
      m := {m with state := advance p m.state (inputs (t >= 7) true)}
      if !busy m.state then break
    ensure (m.state.control == .stopped .completed) "mixed reload program failed"
  IO.println "Passed 1,024 UART/SPI transfers against old execution and independent contracts; UART -> SPI -> stretched pulse -> UART reload."

private def negativeChecks : IO Unit := do
  let variants : List (String × (Program → State → Inputs → State)) := [
    ("clock command deadline", fun p s bus => match s.control with
      | .waiting pc _ => next p pc s.samples bus
      | _ => advance p s bus),
    ("clock command deadline", fun p s bus => match s.control with
      | .waiting .. =>
        let s' := advance p s bus
        match s'.control with
        | .active pc _ => {s' with control := .active pc 0}
        | _ => s'
      | _ => advance p s bus),
    ("capture boundary", fun p s bus =>
      let next := advance p s bus
      if next.samples[0] then {next with samples := Vector.replicate 8 false} else next)]
  for (expected, transition) in variants do
    let failure ← try
      let _ ← pulse 3 7 3 true false transition
      pure none
    catch e => pure (some e.toString)
    ensure (failure.any (fun message => (message.splitOn expected).length > 1))
      s!"mutation not rejected for {expected}: {failure}"
  IO.println "Rejected ignored readiness, shortened post-wait duration, and lost capture variants."

def main : IO Unit := do
  IO.FS.createDirAll "build/reactive"
  let mut cycles := 0
  for d in [:256] do
    for blocked in [0, 255] do
      for data in [false, true] do
        cycles := cycles + (← pulse (Fin.ofNat 256 d) 255 blocked data)
  boundaries
  legacy
  negativeChecks
  let _ ← pulse 3 7 3 true true
  IO.FS.writeFile "build/reactive/coverage.txt" s!"pulse_cases=1024\npulse_observations={cycles}\nlegacy_transfers=1024\n"
  IO.println s!"Passed 1,024 stretched-pulse cases across {cycles} observations. Wrote build/reactive/ trace and coverage."
