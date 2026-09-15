import Pinwheel

/-! Executable checks of the shared machine, independent protocol contracts, and host loading. -/
open Pinwheel
open Pinwheel.Engine

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def haltedProgram (idle : Levels) : Program :=
  ⟨Vector.replicate 32 .halt, idle⟩

private def response (cfg : SPI.Config) (reply : BitVec 8) (noisy : Bool) (cycle : Nat) : Bool := Id.run do
  for bit in [:8] do
    if cycle == (2 * bit + 1) * cfg.halfCycles then return reply.getLsbD (7 - bit)
  return noisy && cycle % 2 == 0

/-- Uses the supplied independent cycle contract, not the compiler's action memory. -/
private def transaction (m : Machine) (duration : Nat) (expected : Nat → Levels)
    (incoming : Nat → Bool) (reply : BitVec 8) : IO Machine := do
  let p := m.program
  let mut state := step p m.state false true (incoming 0)
  for cycle in [:duration + 2] do
    ensure (state.levels == expected cycle) s!"output mismatch at cycle {cycle}"
    ensure (busy state == decide (cycle < duration)) s!"busy mismatch at cycle {cycle}"
    match result state with
    | none => ensure (cycle < duration) s!"missing result at cycle {cycle}"
    | some slots =>
      ensure (cycle >= duration && samplesByte slots == reply) s!"incorrect result at cycle {cycle}"
    ensure (step p state true true true == reset p) s!"reset priority mismatch at cycle {cycle}"
    let next := step p state false false (incoming (cycle + 1))
    if busy state then
      ensure (step p state false true (incoming (cycle + 1)) == next)
        s!"busy start changed execution at cycle {cycle}"
    else
      ensure (next == state) "stopped execution did not retain state"
    state := next
  return ⟨p, state⟩

private def loaded (m : Machine) (p : Program) : IO Machine := do
  let (next, accepted) := load m p
  ensure accepted "stopped load rejected"
  ensure (next.program == p && next.state == reset p) "load leaked execution state or wrong program"
  ensure (result next.state == none && samplesByte next.state.samples == 0 && next.state.levels == p.idle)
    "load did not clear receive data, valid, or apply idle profile"
  return next

private def checkPrograms : IO Unit := do
  let seed : Machine := ⟨haltedProgram 0, reset (haltedProgram 0)⟩
  for divisor in ([0, 3, 255] : List (Fin 256)) do
    let uart : UART.Config := ⟨divisor⟩
    let spi : SPI.Config := ⟨divisor⟩
    for value in [:256] do
      let byte := BitVec.ofNat 8 value
      let um ← loaded seed (Compile.UART.program uart byte)
      let _ ← transaction um uart.frameCycles
        (fun t => Compile.UART.encodePin (UART.expected uart byte t))
        (fun t => t % 2 == 0) 0
      for noisy in [false, true] do
        let sm ← loaded seed (Compile.SPI.program spi byte)
        let _ ← transaction sm spi.transferCycles
          (fun t => Compile.SPI.encodePins (SPI.expectedPins spi byte t))
          (response spi (~~~byte) noisy) (~~~byte)
    IO.println s!"Passed 256 UART values and 512 SPI transfers at duration {divisor.val + 1}."
  let cfg : SPI.Config := ⟨0⟩
  for value in [:256] do
    let reply := BitVec.ofNat 8 value
    let sm ← loaded seed (Compile.SPI.program cfg 0x53)
    let _ ← transaction sm cfg.transferCycles
      (fun t => Compile.SPI.encodePins (SPI.expectedPins cfg 0x53 t))
      (response cfg reply true) reply

/-- Durations differ; capture also occurs at cycle zero and overwrites a prior sample. -/
private def checkMixedActions : IO Unit := do
  let actions : Array Action := #[⟨1, 0, some 0⟩, ⟨6, 3, some 7⟩, ⟨3, 255, some 0⟩, ⟨0, 0, none⟩]
  let p : Program :=
    ⟨Vector.ofFn (fun pc => match actions[pc.val]? with
      | some a => .action a
      | none => .halt), 7⟩
  let incoming := fun t => t % 3 != 2
  let mut state := start p (incoming 0)
  for cycle in [:264] do
    let expected : Levels := if cycle < 1 then 1 else if cycle < 5 then 6
      else if cycle < 261 then 3 else if cycle < 262 then 0 else 7
    ensure (state.levels == expected) s!"mixed-duration gap at {cycle}"
    let expectedByte : BitVec 8 := (if cycle < 5 then 128 else 0) + (if cycle >= 1 then 1 else 0)
    ensure (samplesByte state.samples == expectedByte) s!"entry/overwrite capture mismatch at {cycle}"
    ensure (busy state == decide (cycle < 262)) "mixed-duration completion mismatch"
    ensure ((result state).isSome == decide (cycle >= 262)) "mixed-duration valid mismatch"
    state := step p state false false (incoming (cycle + 1))
  IO.println "Passed mixed 1/4/256/1-cycle actions, entry-edge captures, overwrite, and exact 262-cycle completion."

private def checkBoundaries : IO Unit := do
  let a : Action := ⟨3, 0, none⟩
  for withHalt in [false, true] do
    let p : Program := ⟨Vector.ofFn (fun pc =>
      if withHalt && pc.val == 31 then .halt else .action a), 0⟩
    let limit := if withHalt then 31 else 32
    let mut state := start p true
    for cycle in [:limit + 3] do
      ensure (busy state == decide (cycle < limit)) "program-boundary busy mismatch"
      if cycle >= limit then
        ensure (state.control == .stopped (if withHalt then .completed else .fault))
          "last-slot halt or fall-through fault mismatch"
        ensure (state.levels == 0 && (result state).isSome == withHalt) "fault/complete outputs mismatch"
        ensure (step p state false true false == start p false) "restart from stopped state failed"
        if cycle == limit then
          let _ ← loaded ⟨p, state⟩ (haltedProgram 6)
      state := step p state false false true
  let p := haltedProgram 6
  ensure ((start p true).control == .stopped .completed) "halt in slot zero must complete immediately"
  ensure (samplesByte (start p true).samples == 0) "empty program captured an input"
  IO.println "Passed halt at slot zero/31, exhaustion fault at slot 31, and restart from completion/fault."

private def checkReload : IO Unit := do
  let uc : UART.Config := ⟨3⟩
  let sc : SPI.Config := ⟨3⟩
  let up := Compile.UART.program uc 0x53
  let sp := Compile.SPI.program sc 0xa6
  let actionCount := fun (p : Program) => p.memory.toArray.foldl (fun n instruction =>
    match instruction with | .action _ => n + 1 | .halt => n) 0
  ensure (actionCount up == 10 && up.fetch 10 == .halt) "UART program size mismatch"
  ensure (actionCount sp == 17 && sp.fetch 17 == .halt) "SPI program size mismatch"
  let mut m : Machine := ⟨haltedProgram 0, reset (haltedProgram 0)⟩
  m ← loaded m up
  m ← transaction m uc.frameCycles
    (fun t => Compile.UART.encodePin (UART.expected uc 0x53 t)) (fun _ => true) 0
  m ← loaded m sp
  m ← transaction m sc.transferCycles
    (fun t => Compile.SPI.encodePins (SPI.expectedPins sc 0xa6 t)) (response sc 0xff true) 0xff
  ensure (samplesByte m.state.samples == 255) "reload test did not produce nonzero SPI receive data"
  m ← loaded m up
  m ← transaction m uc.frameCycles
    (fun t => Compile.UART.encodePin (UART.expected uc 0x53 t)) (fun _ => true) 0
  ensure (samplesByte m.state.samples == 0) "SPI receive data leaked into reloaded UART"
  let mut state := start sp false
  for cycle in [:sc.transferCycles] do
    let active : Machine := ⟨sp, state⟩
    ensure (load active up == (active, false)) s!"busy load changed machine at {cycle}"
    let aborted := step sp state true true true
    ensure (aborted == reset sp) s!"abort failed at {cycle}"
    let _ ← loaded ⟨sp, aborted⟩ up
    ensure (step sp aborted false true false == start sp false) "restart after abort failed"
    state := step sp state false true (response sc 0xff true (cycle + 1))
  let _ ← loaded ⟨sp, state⟩ up
  IO.println "Passed UART -> SPI -> UART on one machine; busy-load rejection and abort/reload at every SPI cycle."

private def writeTraces : IO Unit := do
  IO.FS.createDirAll "build/engine"
  let cfg : SPI.Config := ⟨3⟩
  let p := Compile.SPI.program cfg 0x53
  let mut state := start p (response cfg 0xa6 true 0)
  let mut csv := "cycle,cs_n,sclk,mosi,miso,busy,valid,rx\n"
  let bit := fun value => if value then 1 else 0
  for t in [:cfg.transferCycles + 2] do
    csv := csv ++ s!"{t},{bit (state.levels.getLsbD 2)},{bit (state.levels.getLsbD 1)},{bit (state.levels.getLsbD 0)},{bit (response cfg 0xa6 true t)},{bit (busy state)},{bit (result state).isSome},{(samplesByte state.samples).toNat}\n"
    state := step p state false false (response cfg 0xa6 true (t + 1))
  IO.FS.writeFile "build/engine/spi-0x53-rx0xa6-4cycles.csv" csv
  let uc : UART.Config := ⟨3⟩
  let up := Compile.UART.program uc 0x53
  let mut us := start up false
  let mut uartCsv := "cycle,tx,busy\n"
  for t in [:uc.frameCycles + 2] do
    uartCsv := uartCsv ++ s!"{t},{bit (us.levels.getLsbD 0)},{bit (busy us)}\n"
    us := step up us false false true
  IO.FS.writeFile "build/engine/uart-0x53-4cycles.csv" uartCsv

def main : IO Unit := do
  checkPrograms
  checkMixedActions
  checkBoundaries
  checkReload
  writeTraces
  IO.println "Passed 2,560 compiled protocol transfers plus engine boundary/reload cases. Wrote build/engine/ CSV traces."
