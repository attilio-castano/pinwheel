import Pinwheel.Compile.UARTStreamLink

open Pinwheel
open UART.Link

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def timing (txCycles rxCycles txTick rxTick start phase : Nat) (pin : Fin 2 := 0) : IO Timing := do
  let some rx := UART.Rx.Config.ofCycles rxCycles pin | throw (IO.userError "invalid RX period")
  if h : 1 ≤ txCycles ∧ txCycles ≤ 256 ∧ 0 < txTick ∧ 0 < rxTick then
    pure {
      tx := ⟨⟨txCycles - 1, by omega⟩⟩
      rx := rx
      txTick := txTick
      txTickPositive := h.2.2.1
      rxTick := rxTick
      rxTickPositive := h.2.2.2
      txStart := start
      rxPhase := phase }
  else throw (IO.userError "invalid clock or TX period")

private def bounds (earliest spread : Nat) : Latency :=
  ⟨earliest, earliest + spread, Nat.le_add_right _ _⟩

private def ageAt (b : Latency) (mode n : Nat) : Nat :=
  match mode with
  | 0 => b.earliest
  | 1 => b.latest
  | 2 => if n % 2 == 0 then b.earliest else b.latest
  | _ => b.earliest + (n * 48271 + n / 7) % (b.spread + 1)

/-- Independent direct calculation in global time: one division by the physical bit period. -/
private def oracle (t : Timing) (bytes : Array (BitVec 8)) (age n : Nat) : Bool :=
  let now := t.rxPhase + n * t.rxTick
  if now < t.txStart + age then true else
    let symbol := (now - t.txStart - age) / (t.tx.cycles * t.txTick)
    match bytes[symbol / 10]? with
    | none => true
    | some byte => if symbol % 10 == 0 then false else if symbol % 10 == 9 then true
      else byte.getLsbD (symbol % 10 - 1)

/-- Actual per-byte reference and compiled TX traces, cached before RX execution. -/
private def txBank (cfg : UART.Config) : IO (Array (Array Bool)) := do
  let mut bank := #[]
  for value in [:256] do
    let byte := BitVec.ofNat 8 value
    let program := Compile.UART.program cfg byte
    let mut model := UART.initial cfg byte
    let mut core := Engine.start program false
    let mut samples := #[]
    for _ in [:cfg.frameCycles] do
      ensure (core == Compile.UART.liftState cfg model) "TX compiler state"
      ensure (core.levels[0] == UART.pin model) "TX pin projection"
      samples := samples.push core.levels[0]
      model := UART.advance model
      core := Engine.advance program core false
    bank := bank.push samples
  pure bank

private def source (bank : Array (Array Bool)) (frameCycles : Nat) (bytes : Array (BitVec 8))
    (n : Nat) : Bool :=
  match bytes[n / frameCycles]? with
  | none => true
  | some byte => (bank[byte.toNat]?.getD #[])[n % frameCycles]?.getD true

/-- Ceiling in global RX coordinates; independent of the model's local firstEdge formula. -/
private def first (t : Timing) (start delay : Nat) : Nat :=
  (start + delay - t.rxPhase + t.rxTick - 1) / t.rxTick

private def checkWindow (t : Timing) (b : Latency) (d : Nat) : IO Unit := do
  for symbol in [:10] do
    let sample := d + t.rx.half + symbol * t.rx.bitCycles
    for delay in [b.earliest, b.latest] do
      ensure (t.txStart + delay + symbol * t.txBit ≤ t.edge sample &&
        t.edge sample < t.txStart + delay + (symbol + 1) * t.txBit) "symbol window"
  ensure (t.edge (d + t.rx.half + 9 * t.rx.bitCycles + 2) <
    t.txStart + 10 * t.txBit + b.earliest) "rearm/idle-high window"

/-- Predict each detection from delayed start visibility, without consulting RX state. -/
private def schedule (t : Timing) (b : Latency) (bytes : Array (BitVec 8)) (age : Nat → Nat) : IO (Array Nat) := do
  let mut detections := #[]
  let mut rearm := 0
  for index in [:bytes.size] do
    let start := t.txStart + index * 10 * t.txBit
    let lo := first t start b.earliest
    let hi := first t start b.latest
    let mut detected : Option Nat := none
    for n in [lo:hi + 1] do
      if detected.isNone && t.edge n ≥ start + age n then detected := some n
    let some d := detected | throw (IO.userError "no visible start inside interval")
    let localTiming := {t with txStart := start, rxPhase := t.edge rearm}
    ensure (decide (UART.StreamLink.Safe localTiming b)) "shifted continuous timing contract"
    ensure (2 ≤ d - rearm && firstEdge localTiming b.earliest ≤ d - rearm &&
      d - rearm ≤ firstEdge localTiming b.latest) "local detection bounds"
    ensure (oracle t bytes (age (rearm + 1)) (rearm + 1)) "missing idle high after rearm"
    checkWindow {t with txStart := start} b d
    detections := detections.push d
    rearm := d + t.rx.half + 9 * t.rx.bitCycles + 1
  pure detections

structure Stats where
  streams : Nat := 0
  frames : Nat := 0
  edges : Nat := 0
  deliveries : Nat := 0
  drops : Nat := 0
  pending : Nat := 0
  deriving Repr

private def Stats.add (a b : Stats) : Stats :=
  ⟨a.streams + b.streams, a.frames + b.frames, a.edges + b.edges,
    a.deliveries + b.deliveries, a.drops + b.drops, a.pending + b.pending⟩

private def simulate (t : Timing) (b : Latency) (bank : Array (Array Bool))
    (bytes : Array (BitVec 8)) (age : Nat → Nat) (consumer : Nat) : IO Stats := do
  ensure (decide (UART.StreamLink.Safe t b)) "stream outside sufficient bounds"
  let detections ← schedule t b bytes age
  let limit := (detections.back?).getD 0 + t.rx.half + 9 * t.rx.bitCycles + 3
  let mut events : Array (Option UART.Rx.Outcome) := Array.replicate (limit + 1) none
  for i in [:detections.size] do
    let edge := detections[i]! + t.rx.half + 9 * t.rx.bitCycles
    events := events.set! edge (some (.byte bytes[i]!))
    -- Check the new stream wire at every critical completion/rearm/idle boundary.
    for n in [detections[i]!, edge, edge + 1, edge + 2] do
      ensure (UART.StreamLink.sampled t bytes.toList age n == oracle t bytes (age n) n) "proved wire boundary"
  let program := Compile.UARTRx.program t.rx
  let wire := observe t (source bank t.tx.frameCycles bytes) age
  let mut model : UART.Rx.Stream.State := {}
  let mut core : Compile.UARTRxStream.State :=
    ⟨Engine.Reactive.start program (Compile.UARTLink.pins t.rx.input (wire 0) false), {}⟩
  let mut queue : Array UART.Rx.Outcome := #[]
  let mut sticky := false
  let mut arrived := 0
  let mut delivered := 0
  let mut dropped := 0
  for n in [1:limit + 1] do
    let signal := wire n
    ensure (b.earliest ≤ age n && age n ≤ b.latest) "age outside declared interval"
    unless signal == oracle t bytes (age n) n do throw (IO.userError s!"wire at {n}")
    let take := if consumer == 0 then true else if consumer == 1 then false
      else n % (3 * 10 * t.rx.bitCycles + 1) == 0
    let clear := n % 149 == 0
    let input : UART.Rx.Stream.Input := {line := signal, take := take, clearOverrun := clear}
    let actual := UART.Rx.Stream.step t.rx model input
    let compiled := Compile.UARTRxStream.step program t.rx.input core input (n % 3 == 0)
    let mut receipt : UART.Rx.Buffer.Receipt := {}
    if clear then sticky := false
    if take && !queue.isEmpty then
      receipt := {delivered := queue[0]?}
      queue := #[]
    if let some value := events[n]! then
      if queue.isEmpty then
        queue := #[value]
        receipt := {receipt with accepted := some value}
      else
        sticky := true
        receipt := {receipt with dropped := some value}
    model := actual.state
    core := compiled.state
    unless UART.Rx.Stream.arrival model == events[n]! do
      throw (IO.userError s!"stream event at {n}: {repr (UART.Rx.Stream.arrival model)} vs {repr events[n]!}")
    ensure (core == Compile.UARTRxStream.lift t.rx model) "compiled RX/supervisor state"
    ensure (core.core.pins == {}) "RX drove an output"
    ensure (actual.receipt == receipt && compiled.receipt == receipt) "queue ownership oracle"
    ensure (model.buffer.pending == queue[0]? && model.buffer.overrun == sticky) "pending/overrun oracle"
    arrived := arrived + (events[n]!).toList.length
    delivered := delivered + receipt.delivered.toList.length
    dropped := dropped + receipt.dropped.toList.length
  ensure (arrived == bytes.size && arrived == delivered + dropped + queue.size) "stream occurrence accounting"
  if consumer == 0 then ensure (delivered == bytes.size) "always-ready consumer lost a result"
  pure ⟨1, arrived, limit, delivered, dropped, queue.size⟩

/-- Explore every candidate detection edge, including all branches of the next two rearm windows. -/
private def timingTree (t : Timing) (b : Latency) : Nat → IO Nat
  | 0 => pure 0
  | fuel + 1 => do
    ensure (decide (UART.StreamLink.Safe t b)) "recursive timing outside bounds"
    let mut count := 0
    for d in [firstEdge t b.earliest:firstEdge t b.latest + 1] do
      checkWindow t b d
      count := count + 1 + (← timingTree (UART.StreamLink.next t (completion t d + 1)) b fuel)
    pure count

private def sweep : IO (Nat × Nat × Nat × Nat) := do
  let mut accepted := 0
  let mut singleOnly := 0
  let mut excluded := 0
  let mut windows := 0
  for tx in [1, 8, 16, 256] do
    for rx in [8, 9, 16, 257, 6656] do
      for percent in [90, 94, 97, 99, 100, 101, 103, 106, 110] do
        let rxTick := tx * 100
        for phase in [0, 1, rxTick / 2, rxTick - 1] do
          for spread in [0, rxTick / 2, 2 * rxTick] do
            let t ← timing tx rx (rx * percent) rxTick (3 * rxTick + 1) phase
            let b := bounds (rxTick / 3) spread
            if decide (UART.StreamLink.Safe t b) then
              windows := windows + (← timingTree t b 3)
              accepted := accepted + 1
            else if decide (Safe t b) then singleOnly := singleOnly + 1
            else excluded := excluded + 1
  pure (accepted, singleOnly, excluded, windows)

/-- Outside-contract runs retain actual event edges to distinguish wrong data from missed deadlines. -/
private def observedEvents (t : Timing) (bank : Array (Array Bool)) (bytes : Array (BitVec 8))
    (age : Nat → Nat) (limit : Nat) : IO (Array (Nat × UART.Rx.Outcome)) := do
  let wire := observe t (source bank t.tx.frameCycles bytes) age
  let program := Compile.UARTRx.program t.rx
  let mut model : UART.Rx.Stream.State := {}
  let mut core : Compile.UARTRxStream.State :=
    ⟨Engine.Reactive.start program (Compile.UARTLink.pins t.rx.input (wire 0) false), {}⟩
  let mut found := #[]
  for n in [1:limit + 1] do
    ensure (wire n == oracle t bytes (age n) n) "counterexample wire oracle"
    let input : UART.Rx.Stream.Input := {line := wire n, take := true}
    model := (UART.Rx.Stream.step t.rx model input).state
    core := (Compile.UARTRxStream.step program t.rx.input core input false).state
    ensure (core == Compile.UARTRxStream.lift t.rx model) "counterexample compiler state"
    ensure (!core.buffer.overrun) "timing failure became consumer overrun"
    if let some result := UART.Rx.Stream.arrival model then found := found.push (n, result)
  pure found

private def counterexamples : IO Unit := do
  let t ← timing 10 8 77 100 300 0
  let bank ← txBank t.tx
  ensure (decide (Safe t (.fixed 0)) && !decide (UART.StreamLink.Safe t (.fixed 0))) "missing rearm bound setup"
  let missed ← observedEvents t bank #[0, 0] (fun _ => 0) 165
  ensure (missed == #[(79, .byte 0)]) "single-frame bounds accidentally guarantee two frames"
  for tick in [85, 115] do
    let t ← timing 16 16 tick 100 300 0
    let bank ← txBank t.tx
    ensure (!decide (UART.StreamLink.Safe t (.fixed 0))) "drift outside continuous bound"
    let bad ← observedEvents t bank #[0x53, 0xa6] (fun _ => 0) 400
    ensure (bad.map Prod.snd != #[.byte 0x53, .byte 0xa6]) "excessive drift preserved stream"
  let t ← timing 16 16 100 100 300 0
  let bank ← txBank t.tx
  ensure (decide (UART.StreamLink.Safe t (.fixed 0))) "age counterexample nominal timing"
  let late ← observedEvents t bank #[0x53, 0xa6] (fun _ => 16000) 316
  ensure (late.size < 2) "out-of-contract age met nominal stream deadline"
  -- The sufficient bound reserves arbitrary phase: this known phase still works just outside it.
  let t ← timing 8 8 98 100 300 0
  let bank ← txBank t.tx
  ensure (!decide (UART.StreamLink.Safe t (.fixed 0))) "conservative example inside bound"
  let works ← observedEvents t bank #[0, 0] (fun _ => 0) 170
  ensure (works.map Prod.snd == #[.byte 0, .byte 0]) "excluded known-phase example did not work"

def main (args : List String) : IO Unit := do
  IO.FS.createDirAll "build/uart-stream-clocks"
  let focused := args.contains "--focused"
  let values := (List.range (if focused then 8 else 256)).toArray.map (BitVec.ofNat 8)
  let mut stats : Stats := {}
  for txTick in [97, 103] do
    let base ← timing 16 16 txTick 100 301 0
    let bank ← txBank base.tx
    for pin in [:2] do
      for phase in [0, 1, 99] do
        let t ← timing 16 16 txTick 100 301 phase (Fin.ofNat 2 pin)
        let b := bounds 20 20
        for mode in [:4] do
          for consumer in [:3] do
            stats := stats.add (← simulate t b bank values (ageAt b mode) consumer)
  IO.println s!"Unequal clocks: {stats.streams} payload/consumer/age streams passed."
  for (tx, rx, txTick, rxTick, spread) in
      [(9, 9, 99, 100, 110), (8, 16, 200, 100, 40), (1, 8, 800, 100, 100),
       (16, 257, 257, 16, 40), (256, 512, 2, 1, 5)] do
    let base ← timing tx rx txTick rxTick (3 * rxTick + 1) 0
    let bank ← txBank base.tx
    for pin in [:2] do
      for phase in [0, rxTick - 1] do
        let t ← timing tx rx txTick rxTick (3 * rxTick + 1) phase (Fin.ofNat 2 pin)
        let b := bounds 7 spread
        for mode in [:4] do
          for consumer in [:3] do
            stats := stats.add (← simulate t b bank #[0, 255, 0x55, 0xaa, 0x53, 0xa6, 0, 0] (ageAt b mode) consumer)
  let base ← timing 256 6656 26 1 4 0
  let bank ← txBank base.tx
  for pin in [:2] do
    let t ← timing 256 6656 26 1 4 0 (Fin.ofNat 2 pin)
    for mode in [:4] do
      stats := stats.add (← simulate t (bounds 2 5) bank #[0x53, 0xa6, 0] (ageAt (bounds 2 5) mode) (mode % 3))
  let (accepted, singleOnly, excluded, windows) ← sweep
  counterexamples
  let path := if focused then "build/uart-stream-clocks/report-focused.json" else "build/uart-stream-clocks/report.json"
  IO.FS.writeFile path
    s!"\{\"all_byte_values\":{values.size},\"streams\":{stats.streams},\"frames\":{stats.frames},\"rx_edges\":{stats.edges},\"deliveries\":{stats.deliveries},\"drops\":{stats.drops},\"pending\":{stats.pending},\"safe_timings\":{accepted},\"single_frame_only_timings\":{singleOnly},\"outside_single_frame_bounds\":{excluded},\"candidate_windows\":{windows},\"failing_assumption_examples\":4,\"successful_excluded_examples\":1,\"boundary\":\"Independent-clock digital UART streams and compiled RX supervisor; physical sampler, TX launch scheduler and buffer circuitry excluded\"}\n"
  IO.println s!"Unequal-clock stream: {repr stats}."
  IO.println s!"Timing sweep: {accepted} continuous-safe, {singleOnly} single-frame-only, {excluded} excluded; {windows} candidate windows."
