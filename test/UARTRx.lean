import Pinwheel.Hardware.UARTRx
import Pinwheel.Hardware.Storage.Dense

open Pinwheel
open Engine.Reactive
open Compile.UARTRx

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def config (cycles : Nat) (input : Fin 2 := 0) : IO UART.Rx.Config :=
  match UART.Rx.Config.ofCycles cycles input with
  | some cfg => pure cfg
  | none => throw (IO.userError s!"invalid RX period {cycles}")

private def pins (cfg : UART.Rx.Config) (level : Bool) (cycle : Nat) : Inputs :=
  BitVec.ofNat 2 ((if level then 2 ^ cfg.input.val else 0) +
    (if cycle % 3 = 0 then 2 ^ (1 - cfg.input.val) else 0))

/-- Sender time is in hundredths of a receiver cycle. No program state drives this waveform. -/
private def sender (byte : BitVec 8) (start period cycle : Nat) (stop : Bool := true) : Bool :=
  if 100 * cycle < start then true else
    let symbol := (100 * cycle - start) / period
    if symbol = 0 then false else if symbol ≤ 8 then byte.getLsbD (symbol - 1)
    else if symbol = 9 then stop else true

private def store (cfg : UART.Rx.Config) (backend : Nat) : IO (Fetch.Store 255 15) := do
  let p := program cfg
  if backend = 0 then return Fetch.Store.ofProgram p
  if backend = 1 then return Hardware.Execution.directStore (Hardware.UARTRx.words cfg) p.idle p.last
  let dense := (Hardware.UARTRx.words cfg).map (Hardware.Storage.Dense.expand ∘ Hardware.Storage.Dense.compress)
  ensure (dense == Hardware.UARTRx.words cfg) "dense record roundtrip"
  match Hardware.Storage.lower32 dense with
  | none => throw (IO.userError "RX dictionary overflow")
  | some image => return image.val.store p

private def receive (cfg : UART.Rx.Config) (byte : BitVec 8) (detected : Nat)
    (wire : Nat → Bool) (stop : Bool := true) (backend : Nat := 0)
    (mutate : RxProgram → RxProgram := id) (compareReference : Bool := true) : IO Unit := do
  let compiled ← if compareReference then store cfg backend
    else pure (Fetch.Store.ofProgram (mutate (program cfg)))
  let mut reference := UART.Rx.initial
  let mut core := Fetch.start compiled (pins cfg (wire 0) 0)
  let complete := detected + cfg.half + 9 * cfg.bitCycles
  for t in [1:complete + 3] do
    let input := pins cfg (wire t) t
    reference := UART.Rx.advance cfg reference (wire t)
    core := Fetch.advance compiled core input
    if compareReference then ensure (core == lift cfg reference) s!"RX reference at {t} B={cfg.bitCycles}"
    ensure (core.pins == {}) "RX drove an output"
    for k in [10:16] do ensure (!core.samples[k]!) "RX touched a reserved sample"
    ensure (busy core == (t < complete)) s!"RX completion edge {t}, expected {complete}"
    let expected := if t < complete then none else some (if stop then UART.Rx.Outcome.byte byte
      else UART.Rx.Outcome.framingError byte)
    ensure (Compile.UARTRx.result core == expected)
      s!"RX result at {t}: {repr (Compile.UARTRx.result core)}, expected {repr expected}"

private def lifecycle : IO Unit := do
  for duration in [8, 257] do
    let cfg ← config duration
    let p := program cfg
    let wire := sender 0xa6 500 (100 * duration)
    let mut reference := UART.Rx.initial
    let mut core := start p 1
    for t in [1:5 + cfg.half + 9 * duration + 2] do
      let input := pins cfg (wire t) t
      ensure (step p core true true input == reset p) "reset/start priority"
      ensure (UART.Rx.step cfg reference true true (wire t) == UART.Rx.reset) "reference reset"
      if busy core then
        ensure (step p core false true input == advance p core input) "busy start changed RX"
        let loaded := load ⟨p, core⟩ p
        ensure (!loaded.2 && loaded.1.state == core) "busy load changed RX"
      reference := UART.Rx.advance cfg reference (wire t)
      core := advance p core input
    ensure (step p core false false 0 == core) "completed result retention"
    ensure (step p core false true 1 == lift cfg UART.Rx.initial) "rearm did not clear data"
    let other ← config 16 1
    let replaced := load ⟨p, core⟩ (program other)
    ensure (replaced.2 && replaced.1.state == reset (program other)) "stopped replacement"
    ensure (replaced.1.program == program other) "replacement image"
  let cfg ← config 8
  let p := program cfg
  let mut reference := UART.Rx.reset
  let mut core := reset p
  for t in [:6000] do
    let input := BitVec.ofNat 2 ((t * 48271 + t / 7) % 4)
    let resetRequested := t % 197 == 0
    let startRequested := t % 17 == 0
    reference := UART.Rx.step cfg reference resetRequested startRequested input[0]
    core := step p core resetRequested startRequested input
    ensure (core == lift cfg reference) s!"arbitrary control history at {t}"

private def capacity : IO (Nat × Nat) := do
  let mut largest := 0
  let mut mostRecords := 0
  for cycles in [8:6657] do
    for pin in [:2] do
      let cfg ← config cycles (Fin.ofNat 2 pin)
      let p := program cfg
      let words := Hardware.UARTRx.words cfg
      let records := words.toList.eraseDups.length
      largest := max largest (p.last.val + 1)
      mostRecords := max mostRecords records
      ensure (p.last.val == haltPC cfg && p.last.val < 256) "RX address wrap"
      ensure (words.all fun w => (Hardware.Execution.decode w).isSome) "invalid E64 record"
      ensure (words.all fun w => Hardware.Storage.Dense.expand (Hardware.Storage.Dense.compress w) == w)
        "RX dense encoding"
      match Hardware.UARTRx.compact cfg with
      | none => throw (IO.userError s!"RX capacity B={cycles} pin={pin}")
      | some image => ensure (image.val.expand == words) "RX compact lookup"
  for cycles in [0, 1, 7, 6657, 100000] do
    ensure ((UART.Rx.Config.ofCycles cycles).isNone) "unsupported period accepted"
  IO.println s!"RX capacity: all 13,298 configurations; maxima {largest} instructions, {mostRecords} records."
  return (largest, mostRecords)

private def corrupt (kind : Nat) (p : RxProgram) : RxProgram :=
  {p with memory := p.memory.map fun instruction => match instruction with
    | .checked a =>
      if kind = 0 && a.action.durationMinusOne.val > 0 then
        .checked {a with action := {a.action with durationMinusOne := Fin.ofNat 256 (a.action.durationMinusOne.val + 1)}}
      else .checked {a with terminalCapture := a.terminalCapture.map fun c =>
        if kind = 1 && c.destination.val < 8 then {c with destination := Fin.ofNat 16 (7 - c.destination.val)}
        else if kind = 2 && c.destination.val = 9 then {c with destination := 10}
        else if kind = 3 then {c with input := Fin.ofNat 2 (1 - c.input.val)} else c}
    | i => i}

def main : IO Unit := do
  IO.FS.createDirAll "build/uart-rx"
  let mut frames := 0
  for duration in [8, 9, 16, 255, 256, 257, 434] do
    for pin in [:2] do
      let cfg ← config duration (Fin.ofNat 2 pin)
      for value in [:256] do
        let byte := BitVec.ofNat 8 value
        let detected := 3 + value % 7
        receive cfg byte detected (sender byte (detected * 100) (duration * 100))
        frames := frames + 1
  IO.println s!"RX exact-clock: {frames} frames, all bytes at seven periods on both input pins."
  let mut backendFrames := 0
  for duration in [8, 257, 434, 5208, 6656] do
    for pin in [:2] do
      let cfg ← config duration (Fin.ofNat 2 pin)
      for backend in [1, 2] do
        for value in [0, 0x53, 0xa6, 255] do
          let byte := BitVec.ofNat 8 value
          receive cfg byte 5 (sender byte 500 (duration * 100)) true backend
          backendFrames := backendFrames + 1
  IO.println s!"RX decoded/dense compact backends: {backendFrames} frames, including maximum period."
  let mut shifted := 0
  let mut excluded := 0
  for duration in [8, 9, 16, 257] do
    let cfg ← config duration
    for phase in [0, 1, 49, 99] do
      for percent in [90, 94, 97, 99, 100, 101, 103, 106, 110] do
        let start := 300 + phase
        let detected := (start + 99) / 100
        let period := duration * percent
        let windows := (List.range 10).all fun symbol =>
          (100 * (detected + cfg.half + symbol * duration) - start) / period == symbol
        if windows then
          for value in [0, 0x53, 0xa6, 255] do
            let byte := BitVec.ofNat 8 value
            receive cfg byte detected (sender byte start period)
            shifted := shifted + 1
        else excluded := excluded + 1
  IO.println s!"RX fractional sender clocks: {shifted} frames within explicit sampling windows; {excluded} timing combinations outside the premise."
  let cfg ← config 16
  for backend in [:3] do
    for value in [:256] do
      let byte := BitVec.ofNat 8 value
      receive cfg byte 5 (sender byte 500 1600 · false) false backend
    -- An initially low line must first be observed high; a short pulse must fail midpoint confirmation.
    receive cfg 0x53 40 (fun t => if t < 10 then false else sender 0x53 4000 1600 t) true backend
    receive cfg 0xa6 40 (fun t => if 5 ≤ t && t < 8 then false else sender 0xa6 4000 1600 t) true backend
    let compiled ← store cfg backend
    let mut s := Fetch.start compiled 0
    for _ in [:1024] do s := Fetch.advance compiled s 0
    ensure (busy s && (Compile.UARTRx.result s).isNone && !s.samples[9]) "stuck-low line completed"
  lifecycle
  for kind in [:4] do
    let rejected ← try
        receive cfg 0x53 5 (sender 0x53 500 1600) true 0 (corrupt kind) false
        pure false
      catch _ => pure true
    ensure rejected s!"RX mutation {kind} survived waveform oracle"
  let (largest, records) ← capacity
  let mut images := ""
  for (name, duration, input) in [("uart-rx", 16, 0), ("uart-rx-split", 257, 1),
      ("uart-rx-long", 5208, 0), ("uart-rx-max", 6656, 1)] do
    let cfg ← config duration (Fin.ofNat 2 input)
    let p := program cfg
    images := images ++ name ++ " " ++ String.intercalate " "
      (([p.last.val, p.idle.levels.toNat, p.idle.enabled.toNat] ++
        (Hardware.UARTRx.words cfg).toList.map BitVec.toNat).map toString) ++ "\n"
  IO.FS.writeFile "build/uart-rx/images.txt" images
  IO.FS.writeFile "build/uart-rx/model-report.json"
    s!"\{\"exact_frames\":{frames},\"backend_frames\":{backendFrames},\"fractional_frames\":{shifted},\"outside_sampling_premise\":{excluded},\"bad_stop_frames\":768,\"configurations\":13298,\"max_instructions\":{largest},\"max_records\":{records},\"mutations_rejected\":4}\n"
  IO.println "RX malformed frames, false starts, reset/rearm/load controls and four waveform mutations passed."
