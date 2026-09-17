import Pinwheel.Compile.UARTLink

open Pinwheel
open UART.Link

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def timing (txCycles rxCycles txTick rxTick start phase : Nat) (pin : Fin 2 := 0) : IO Timing := do
  let some rx := UART.Rx.Config.ofCycles rxCycles pin
    | throw (IO.userError s!"invalid RX period {rxCycles}")
  if h : 1 ≤ txCycles ∧ txCycles ≤ 256 ∧ 0 < txTick ∧ 0 < rxTick then
    return {
      tx := ⟨⟨txCycles - 1, by omega⟩⟩
      rx := rx
      txTick := txTick
      txTickPositive := h.2.2.1
      rxTick := rxTick
      rxTickPositive := h.2.2.2
      txStart := start
      rxPhase := phase }
  else throw (IO.userError "invalid TX period or clock tick")

private def bounds (earliest spread : Nat) : Latency :=
  ⟨earliest, earliest + spread, Nat.le_add_right _ _⟩

private def ageAt (b : Latency) (mode cycle : Nat) : Nat :=
  match mode with
  | 0 => b.earliest
  | 1 => b.latest
  | 2 => if cycle % 2 = 0 then b.earliest else b.latest
  | _ => b.earliest + (cycle * 48271 + cycle / 7) % (b.spread + 1)

/-- Advance actual TX reference and compiled machines once per TX clock, retaining their wire.
The later RX simulation reads this trace; it does not regenerate a byte-level sender. -/
private def txTrace (t : Timing) (byte : BitVec 8) : IO (Array Bool) := do
  let p := Compile.UART.program t.tx byte
  let mut reference := UART.initial t.tx byte
  let mut core := Engine.start p false
  let mut wire := #[]
  for cycle in [:t.tx.frameCycles + 2] do
    ensure (core == Compile.UART.liftState t.tx reference) s!"TX compiler at {cycle}"
    ensure (core.levels[0] == UART.pin reference) s!"TX wire at {cycle}"
    wire := wire.push core.levels[0]
    reference := UART.advance reference
    core := Engine.advance p core (cycle % 3 == 0)
  pure wire

/-- Separate direct global-time oracle: one division by the physical bit period. -/
private def oracle (t : Timing) (byte : BitVec 8) (age cycle : Nat) : Bool :=
  let now := t.rxPhase + cycle * t.rxTick
  if now < t.txStart + age then true else
    let symbol := (now - t.txStart - age) / (t.tx.cycles * t.txTick)
    if symbol = 0 then false else if symbol ≤ 8 then byte.getLsbD (symbol - 1) else true

private def simulate (t : Timing) (b : Latency) (byte : BitVec 8) (age : Nat → Nat)
    (guaranteed : Bool := true) : IO (Option UART.Rx.Outcome × Nat) := do
  if guaranteed then ensure (decide (Safe t b)) "simulation outside sufficient timing bounds"
  let trace ← txTrace t byte
  let source := fun cycle => trace[cycle]?.getD true
  let wire := observe t source age
  let p := Compile.UARTRx.program t.rx
  let mut reference := UART.Rx.initial
  let mut core := Engine.Reactive.start p (Compile.UARTLink.pins t.rx.input (wire 0) true)
  let mut firstLow : Option Nat := none
  let limit := completion t (firstEdge t b.latest) + 2
  for cycle in [1:limit + 1] do
    let signal := wire cycle
    ensure (signal == oracle t byte (age cycle) cycle) s!"global-time wire oracle at {cycle}"
    if firstLow.isNone && !signal then firstLow := some cycle
    let incoming := Compile.UARTLink.pins t.rx.input signal (cycle % 3 == 0)
    reference := UART.Rx.advance t.rx reference signal
    core := Engine.Reactive.advance p core incoming
    ensure (core == Compile.UARTRx.lift t.rx reference) s!"RX compiler at {cycle}"
    ensure (core.pins == {}) "receiver drove an output"
    if guaranteed then
      ensure (b.earliest ≤ age cycle && age cycle ≤ b.latest) "observation age outside contract"
      if let some detected := firstLow then
        ensure (firstEdge t b.earliest ≤ detected && detected ≤ firstEdge t b.latest && 2 ≤ detected)
          s!"detected edge {detected} outside proved interval"
        let expected := if cycle < completion t detected then none else some (UART.Rx.Outcome.byte byte)
        ensure (Compile.UARTRx.result core == expected)
          s!"link result at {cycle}: {repr (Compile.UARTRx.result core)}, expected {repr expected}"
      else ensure ((Compile.UARTRx.result core).isNone) "result before start detection"
  let result := Compile.UARTRx.result core
  if guaranteed then ensure (result == some (.byte byte)) "link did not deliver the transmitted byte"
  pure (result, limit)

/-- Check every candidate detection edge against both delay extremes, for every symbol. -/
private def windows (t : Timing) (b : Latency) : IO Unit := do
  let lo := firstEdge t b.earliest
  let hi := firstEdge t b.latest
  ensure (2 ≤ lo && lo ≤ hi) "invalid detection interval"
  for detected in [lo:hi + 1] do
    for symbol in [:10] do
      let sample := detected + t.rx.half + symbol * t.rx.bitCycles
      for age in [b.earliest, b.latest] do
        ensure (t.txStart + age + symbol * t.txBit ≤ t.edge sample &&
          t.edge sample < t.txStart + age + (symbol + 1) * t.txBit)
          s!"sample window failed d={detected}, symbol={symbol}, age={age}"

private def timingSweep : IO (Nat × Nat) := do
  let mut accepted := 0
  let mut excluded := 0
  for txCycles in [1, 8, 16, 256] do
    for rxCycles in [8, 9, 16, 257, 6656] do
      for percent in [90, 94, 97, 99, 100, 101, 103, 106, 110] do
        let rxTick := txCycles * 100
        for phase in [0, 1, rxTick / 2, rxTick - 1] do
          for spread in [0, rxTick / 2, 2 * rxTick] do
            let t ← timing txCycles rxCycles (rxCycles * percent) rxTick (phase + 3 * rxTick + 1) phase
            let b := bounds (rxTick / 3) spread
            if decide (Safe t b) then
              windows t b
              accepted := accepted + 1
            else excluded := excluded + 1
  pure (accepted, excluded)

private def transitionBoundaries : IO Unit := do
  let t ← timing 8 8 1 1 3 0
  let byte : BitVec 8 := 0x55
  let trace ← txTrace t byte
  let wire := observe t (fun cycle => trace[cycle]?.getD true) (fun _ => 0)
  for symbol in [1:10] do
    let edge := 3 + symbol * 8
    ensure (wire edge == oracle t byte 0 edge) "transition belongs to new symbol"
    ensure (wire (edge - 1) == oracle t byte 0 (edge - 1)) "edge before transition belongs to old symbol"
    ensure (wire edge != wire (edge - 1)) "alternating frame lost a transition"

private def counterexamples : IO Unit := do
  for txTick in [85, 115] do
    let t ← timing 8 8 txTick 100 300 0
    ensure (!decide (Safe t (.fixed 0))) "drift counterexample satisfies Safe"
    let (result, _) ← simulate t (.fixed 0) 0x53 (fun _ => 0) false
    ensure (result != some (.byte 0x53)) s!"drift {txTick} unexpectedly recovered byte"
  let unarmed ← timing 8 8 1 1 0 0
  ensure (!decide (Safe unarmed (.fixed 0))) "unarmed case satisfies Safe"
  let (missed, _) ← simulate unarmed (.fixed 0) 0 (fun _ => 0) false
  ensure missed.isNone "receiver detected frame without observing idle high"
  let delayed ← timing 16 16 100 100 300 0
  ensure (decide (Safe delayed (.fixed 0))) "delay counterexample timing"
  let (late, _) ← simulate delayed (.fixed 0) 0x53 (fun n => if n ≤ 4 then 0 else 6400) false
  ensure (late != some (.byte 0x53)) "out-of-contract delay did not disrupt reception"
  -- Safe reserves a whole RX tick for arbitrary phase; one known phase can work outside it.
  let conservative ← timing 8 8 96 100 300 0
  ensure (!decide (Safe conservative (.fixed 0))) "conservative example satisfies Safe"
  let (works, _) ← simulate conservative (.fixed 0) 0xa6 (fun _ => 0) false
  ensure (works == some (.byte 0xa6)) "sufficient-bound example did not recover byte"

def main : IO Unit := do
  IO.FS.createDirAll "build/uart-link"
  let mut idealFrames := 0
  let mut variedFrames := 0
  let mut edges := 0
  for period in [8, 9, 16, 127, 255, 256] do
    for pin in [:2] do
      let t ← timing period period 1 1 3 0 (Fin.ofNat 2 pin)
      for value in [:256] do
        let (_, count) ← simulate t (.fixed 0) (BitVec.ofNat 8 value) (fun _ => 0)
        idealFrames := idealFrames + 1
        edges := edges + count
  IO.println s!"UART link ideal: {idealFrames} frames, all bytes, six shared periods, both RX inputs."
  for pin in [:2] do
    for (txCycles, rxCycles, txTick, rxTick) in
        [(8, 8, 97, 100), (9, 9, 103, 100), (16, 16, 97, 100), (16, 16, 103, 100),
         (8, 16, 200, 100), (1, 8, 800, 100), (16, 257, 257, 16)] do
      for phase in [0, 1, rxTick - 1] do
        let t ← timing txCycles rxCycles txTick rxTick (3 * rxTick + 1) phase (Fin.ofNat 2 pin)
        let b := bounds 20 40
        for mode in [:4] do
          for value in [0, 0x53, 0xa6, 255] do
            let (_, count) ← simulate t b (BitVec.ofNat 8 value) (ageAt b mode)
            variedFrames := variedFrames + 1
            edges := edges + count
    -- Long RX period and exact equality at each sufficient-window boundary.
    for (txCycles, rxCycles, txTick, rxTick, spread) in
        [(256, 6656, 26, 1, 0), (8, 8, 1, 1, 3), (4, 8, 19, 9, 0), (10, 8, 77, 100, 0)] do
      let t ← timing txCycles rxCycles txTick rxTick (3 * rxTick) 0 (Fin.ofNat 2 pin)
      let b := bounds 0 spread
      windows t b
      for mode in [:4] do
        for value in [0, 0x53, 0xa6, 255] do
          let (_, count) ← simulate t b (BitVec.ofNat 8 value) (ageAt b mode)
          variedFrames := variedFrames + 1
          edges := edges + count
  let (accepted, excluded) ← timingSweep
  transitionBoundaries
  counterexamples
  IO.FS.writeFile "build/uart-link/report.json"
    s!"\{\"ideal_frames\":{idealFrames},\"varied_frames\":{variedFrames},\"rx_edges\":{edges},\"safe_timings\":{accepted},\"outside_sufficient_bounds\":{excluded},\"failing_assumption_examples\":4,\"successful_outside_bounds\":1,\"boundary\":\"Lean TX/RX and compiled program instances; integer clocks and digital observation age; no RTL or physical sampler validation\"}\n"
  IO.println s!"UART link varied clocks/delay: {variedFrames} frames; {edges} total RX edges."
  IO.println s!"Timing sweep: {accepted} safe, {excluded} outside sufficient bounds; four failing assumptions and one successful outside-bound example."
