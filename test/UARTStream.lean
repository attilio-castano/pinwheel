import Pinwheel.Compile.UARTRxStream

open Pinwheel
open UART.Rx

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def config (period : Nat) (pin : Fin 2 := 0) : IO Config := do
  let some cfg := Config.ofCycles period pin | throw (IO.userError s!"invalid period {period}")
  pure cfg

/-- Independent bit-index oracle; no use of Stream.wire or UART.expected. -/
private def wireOracle (period start : Nat) (bytes : Array (BitVec 8)) (n : Nat) : Bool :=
  if n < start then true else
    let offset := n - start
    match bytes[offset / (10 * period)]? with
    | none => true
    | some byte =>
      let symbol := offset / period % 10
      if symbol == 0 then false else if symbol == 9 then true else byte.getLsbD (symbol - 1)

private def events (cfg : Config) (start : Nat) (bytes : Array (BitVec 8)) (n : Nat) : Option Outcome :=
  if n < start then none else
    let offset := n - start
    if offset % (10 * cfg.bitCycles) == cfg.half + 9 * cfg.bitCycles then
      bytes[offset / (10 * cfg.bitCycles)]? |>.map Outcome.byte
    else none

/-- Cache actual reference and compiled TX traces; receive loops reuse these samples. -/
private def txBank (period : Nat) : IO (Array (Array Bool)) := do
  if h : 1 ≤ period ∧ period ≤ 256 then
    let cfg : UART.Config := ⟨⟨period - 1, by omega⟩⟩
    let mut bank := #[]
    for value in [:256] do
      let byte := BitVec.ofNat 8 value
      let program := Compile.UART.program cfg byte
      let mut model := UART.initial cfg byte
      let mut core := Engine.start program false
      let mut samples := #[]
      for n in [:10 * period] do
        ensure (core == Compile.UART.liftState cfg model) "TX state correspondence"
        ensure (core.levels[0] == wireOracle period 0 #[byte] n) "TX independent wire oracle"
        samples := samples.push core.levels[0]
        model := UART.advance model
        core := Engine.advance program core false
      bank := bank.push samples
    pure bank
  else throw (IO.userError "TX bank outside supported period")

private def bankWire (bank : Array (Array Bool)) (period start : Nat)
    (bytes : Array (BitVec 8)) (n : Nat) : Bool :=
  if n < start then true else
    let offset := n - start
    match bytes[offset / (10 * period)]? with
    | none => true
    | some byte => (bank[byte.toNat]?.getD #[])[offset % (10 * period)]?.getD true

structure Stats where
  edges : Nat := 0
  arrivals : Nat := 0
  deliveries : Nat := 0
  drops : Nat := 0
  flushes : Nat := 0
  deriving Repr

private def Stats.add (a b : Stats) : Stats :=
  ⟨a.edges + b.edges, a.arrivals + b.arrivals, a.deliveries + b.deliveries,
    a.drops + b.drops, a.flushes + b.flushes⟩

private def controls (mode n : Nat) : Stream.Input :=
  match mode with
  | 0 => {take := true}
  | 1 => {}
  | 2 => {take := n % 163 == 0, clearOverrun := n % 79 == 0}
  | _ => {take := (n * 48271 + n / 7) % 11 < 3, clearOverrun := n % 43 == 0}

/-- Queue oracle owns a separate array and applies pop, then push, in explicit imperative steps.
Expected arrivals are supplied independently of both receiver implementations. -/
private def simulate (cfg : Config) (program : Compile.UARTRx.RxProgram)
    (incoming : Nat → Stream.Input) (expected : Nat → Option Outcome) (limit : Nat) : IO Stats := do
  let mut model : Stream.State := {}
  let mut core : Compile.UARTRxStream.State :=
    ⟨Engine.Reactive.start program (Compile.UARTLink.pins cfg.input (incoming 0).line true), {}⟩
  let mut queue : Array Outcome := #[]
  let mut sticky := false
  let mut stats : Stats := {}
  for n in [1:limit + 1] do
    let input := incoming n
    let event := expected n
    let actual := Stream.step cfg model input
    let compiled := Compile.UARTRxStream.step program cfg.input core input (n % 3 == 0)
    let mut receipt : Buffer.Receipt := {}
    if input.reset then
      receipt := {flushed := queue[0]?}
      queue := #[]
      sticky := false
      ensure event.isNone "reset must abort the completion edge"
    else
      if input.clearOverrun then sticky := false
      if input.take && !queue.isEmpty then
        receipt := {receipt with delivered := queue[0]?}
        queue := #[]
      if let some value := event then
        if queue.isEmpty then
          queue := queue.push value
          receipt := {receipt with accepted := some value}
        else
          sticky := true
          receipt := {receipt with dropped := some value}
    model := actual.state
    core := compiled.state
    ensure (Stream.arrival model == event) s!"arrival at {n}: {repr (Stream.arrival model)}, expected {repr event}"
    ensure (core == Compile.UARTRxStream.lift cfg model) s!"compiled state at {n}"
    ensure (core.core.pins == {}) s!"RX drove an output at {n}"
    ensure (actual.receipt == receipt && compiled.receipt == receipt) s!"ownership receipt at {n}"
    ensure (model.buffer.pending == queue[0]? && model.buffer.overrun == sticky) s!"buffer oracle at {n}"
    stats := ⟨stats.edges + 1, stats.arrivals + event.toList.length,
      stats.deliveries + receipt.delivered.toList.length,
      stats.drops + receipt.dropped.toList.length, stats.flushes + receipt.flushed.toList.length⟩
  ensure (stats.arrivals == stats.deliveries + stats.drops + stats.flushes + queue.size) "occurrence accounting"
  pure stats

private def ideal (cfg : Config) (program : Compile.UARTRx.RxProgram)
    (wire : Nat → Bool) (bytes : Array (BitVec 8)) (mode : Nat) : IO Stats := do
  let incoming := fun n => {controls mode n with line := wire n}
  let stats ← simulate cfg program incoming (events cfg 3 bytes) (3 + bytes.size * 10 * cfg.bitCycles + 3)
  ensure (stats.arrivals == bytes.size) "missing ideal frame"
  if mode == 0 then ensure (stats.deliveries == bytes.size && stats.drops == 0) "always-ready stream lost data"
  if mode == 1 then ensure (stats.deliveries == 0 && stats.drops + 1 == bytes.size) "stalled stream accounting"
  pure stats

/-- Exhaust every old-slot state, arrival kind, and consumer/clear combination. -/
private def bufferEdges : IO Nat := do
  let values : List (Option Outcome) := [none, some (.byte 0), some (.byte 255), some (.framingError 0x53)]
  let mut count := 0
  for old in values do
    for event in values do
      for overrun in [false, true] do
        for take in [false, true] do
          for clear in [false, true] do
            let mut queue := old.toList.toArray
            let mut sticky := overrun && !clear
            let mut receipt : Buffer.Receipt := {}
            if take then
              receipt := {delivered := queue[0]?}
              queue := #[]
            if let some value := event then
              if queue.isEmpty then
                queue := #[value]
                receipt := {receipt with accepted := event}
              else
                sticky := true
                receipt := {receipt with dropped := event}
            let result := Buffer.step ⟨old, overrun⟩ (.cycle event take clear)
            ensure (result == ⟨⟨queue[0]?, sticky⟩, receipt⟩) "buffer truth table"
            ensure (Buffer.step ⟨old, overrun⟩ .reset == ⟨{}, {flushed := old}⟩) "buffer reset"
            count := count + 1
  -- These concrete discriminators reject overwrite-old, push-before-pop, bypass,
  -- and clear-dominates-drop policies, even when common happy-path traces agree.
  let full := Buffer.step ⟨some (.byte 1), true⟩ (.cycle (some (.byte 2)) false true)
  ensure (full.state.pending != some (.byte 2)) "overwrite-old mutation survived"
  ensure full.state.overrun "clear-dominates-drop mutation survived"
  let swap := Buffer.step ⟨some (.byte 1), false⟩ (.cycle (some (.byte 2)) true false)
  ensure (swap.receipt.dropped.isNone && swap.state.pending == some (.byte 2)) "push-before-pop mutation survived"
  let empty := Buffer.step {} (.cycle (some (.byte 2)) true false)
  ensure empty.receipt.delivered.isNone "bypass mutation survived"
  pure count

private def recoveryCases : IO (Stats × Nat) := do
  let mut stats : Stats := {}
  let mut count := 0
  for pin in [:2] do
    let cfg ← config 8 (Fin.ofNat 2 pin)
    let program := Compile.UARTRx.program cfg
    -- Corrupt stop, remain low after completion, then recover to a good frame.
    let broken := fun n => if 75 ≤ n && n < 100 then false
      else if n < 100 then wireOracle 8 3 #[0x53] n else wireOracle 8 110 #[0xa6] n
    let brokenEvents := fun n => if n == 79 then some (Outcome.framingError 0x53)
      else if n == 186 then some (.byte 0xa6) else none
    for take in [false, true] do
      stats := stats.add (← simulate cfg program (fun n => {line := broken n, take := take}) brokenEvents 195)
      count := count + 1
    -- A one-edge false start is rejected at the midpoint; the next valid start works.
    stats := stats.add (← simulate cfg program
      (fun n => {line := if n == 3 then false else wireOracle 8 20 #[0x53] n, take := true})
      (fun n => if n == 96 then some (.byte 0x53) else none) 110)
    count := count + 1
    -- Initial held-low cannot manufacture a frame, including after automatic rearm.
    stats := stats.add (← simulate cfg program
      (fun n => {line := if n < 150 then false else wireOracle 8 153 #[0xa6] n, take := true})
      (fun n => if n == 229 then some (.byte 0xa6) else none) 240)
    count := count + 1
    for resetEdge in [1, 2, 3, 7, 15, 75, 78, 79, 80, 81, 83, 90] do
      let incoming := fun n => {
        line := if n < resetEdge then wireOracle 8 3 #[0x53] n
          else if n < resetEdge + 90 then false else wireOracle 8 (resetEdge + 93) #[0xa6] n
        take := n ≥ resetEdge + 170
        reset := n == resetEdge }
      let expected := fun n => if n == 79 && 79 < resetEdge then some (Outcome.byte 0x53)
        else if n == resetEdge + 169 then some (.byte 0xa6) else none
      let result ← simulate cfg program incoming expected (resetEdge + 174)
      ensure (result.flushes == if 79 < resetEdge then 1 else 0) "reset flush boundary"
      stats := stats.add result
      count := count + 1
    -- Consume the old value on exactly the next completion edge; retain the new one.
    let bytes := #[0x53, 0xa6]
    let simultaneous ← simulate cfg program
      (fun n => {line := wireOracle 8 3 bytes n, take := n == 159}) (events cfg 3 bytes) 166
    ensure (simultaneous.deliveries == 1 && simultaneous.drops == 0) "same-edge consumption"
    stats := stats.add simultaneous
    count := count + 1
    stats := stats.add (← simulate cfg program
      (fun n => {line := wireOracle 8 3 bytes n, clearOverrun := n == 159}) (events cfg 3 bytes) 166)
    count := count + 1
  -- Safe for a single frame, but edge 80 is both automatic rearm and the next start.
  let cfg ← config 8
  let t : UART.Link.Timing := {
    tx := ⟨9⟩, rx := cfg, txTick := 77, txTickPositive := by decide,
    rxTick := 100, rxTickPositive := by decide, txStart := 300, rxPhase := 0 }
  ensure (decide (UART.Link.Safe t (.fixed 0))) "single-frame Safe counterexample setup"
  let missed ← simulate cfg (Compile.UARTRx.program cfg)
    (fun n => {line := wireOracle 770 300 #[0, 0] (100 * n), take := true})
    (fun n => if n == 79 then some (.byte 0) else none) 165
  ensure (missed.arrivals == 1 && missed.drops == 0) "rearm failure confused with buffer overrun"
  stats := stats.add missed
  count := count + 1
  pure (stats, count)

def main (args : List String) : IO Unit := do
  IO.FS.createDirAll "build/uart-stream"
  let cases ← bufferEdges
  let cfg ← config 8
  let program := Compile.UARTRx.program cfg
  let bank ← txBank 8
  let (initialStats, recoveryCases) ← recoveryCases
  let mut stats := initialStats
  let pairLimit := if args.contains "--focused" then 4 else 256
  for a in [:pairLimit] do
    for b in [:pairLimit] do
      let bytes := #[BitVec.ofNat 8 a, BitVec.ofNat 8 b]
      stats := stats.add (← ideal cfg program (bankWire bank 8 3 bytes) bytes 0)
  IO.println s!"UART stream: {pairLimit * pairLimit} ordered byte pairs passed through reference and compiled RX."
  for period in [8, 9, 16, 255, 256] do
    let bank ← txBank period
    for pin in [:2] do
      let cfg ← config period (Fin.ofNat 2 pin)
      let program := Compile.UARTRx.program cfg
      let bytes := #[0, 255, 0x55, 0xaa, 0x81, 0x7e, 0, 0] |>.map (BitVec.ofNat 8)
      for mode in [:4] do
        stats := stats.add (← ideal cfg program (bankWire bank period 3 bytes) bytes mode)
  let long := (List.range 256 ++ (List.range 256).reverse).toArray.map (BitVec.ofNat 8)
  for mode in [:4] do
    stats := stats.add (← ideal cfg program (bankWire bank 8 3 long) long mode)
  -- Synthetic ideal source extends beyond the current transmitter's 256-cycle limit.
  for period in [257, 512, 6656] do
    for pin in [:2] do
      let cfg ← config period (Fin.ofNat 2 pin)
      let bytes := #[0x53, 0xa6, 0] |>.map (BitVec.ofNat 8)
      stats := stats.add (← ideal cfg (Compile.UARTRx.program cfg) (wireOracle period 3 bytes) bytes 0)
  let report := if args.contains "--focused" then "build/uart-stream/report-focused.json"
    else "build/uart-stream/report.json"
  IO.FS.writeFile report
    s!"\{\"ordered_byte_pairs\":{pairLimit * pairLimit},\"buffer_edge_cases\":{cases},\"recovery_cases\":{recoveryCases},\"single_frame_safe_rearm_counterexamples\":1,\"rx_edges\":{stats.edges},\"arrivals\":{stats.arrivals},\"deliveries\":{stats.deliveries},\"drops\":{stats.drops},\"flushes\":{stats.flushes},\"boundary\":\"Lean continuous RX and compiled-program supervisor; no RTL buffer or physical sampler claim\"}\n"
  IO.println s!"UART stream: {repr stats}; {cases} buffer edge cases."
