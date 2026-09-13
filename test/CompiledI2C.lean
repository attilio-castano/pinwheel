import Pinwheel

open Pinwheel.I2C

private def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

/-- Target and monitor use only pin commands and resolved wire transitions, never controller phases. -/
private def transaction (cfg : Config) (request : Request) (reply : Reply)
    (stretch : Nat → Nat) (trace : Bool := false)
    (transform : Pinwheel.Engine.Reactive.Program → Pinwheel.Engine.Reactive.Program := id)
    (looped : Bool := false)
    (storeTransform : Pinwheel.Engine.Reactive.Fetch.Store → Pinwheel.Engine.Reactive.Fetch.Store := id) : IO Nat := do
  let mut state := initial cfg request
  let p := transform (Pinwheel.Compile.I2C.program cfg request)
  let store := storeTransform (Pinwheel.Compile.I2CLoop.program cfg request).store
  let tick := if looped then Pinwheel.Engine.Reactive.Fetch.advance store
    else Pinwheel.Engine.Reactive.advance p
  let mut core := if looped then Pinwheel.Engine.Reactive.Fetch.start store 0
    else Pinwheel.Engine.Reactive.start p 0
  let mut baseline := Pinwheel.Engine.Reactive.start p 0
  let mut target : Pins := {}
  let mut previous : Bus := {}
  let mut previousCommand : Pins := {}
  let mut stretchLeft := 0
  let mut clocks : Array Bool := #[]
  let mut pending : Option Bool := none
  let mut started := false
  let mut stopped := false
  let mut riseAt := 0
  let mut fallAt := 0
  let mut cycles := 0
  let mut csv := "cycle,scl,sda,controller_scl_low,controller_sda_low,target_scl_low,target_sda_low,phase,slot,remaining,wait_left\n"
  let limit := 128 * cfg.phaseCycles + 20 * (cfg.waitCycles + 2)
  for t in [:limit] do
    ensure (core == baseline) s!"store state mismatch at {t}"
    ensure (core.pins == Pinwheel.Compile.I2C.encodePins (pins state)) s!"compiler pins at {t}"
    ensure (Pinwheel.Engine.Reactive.busy core == busy state) s!"compiler busy at {t}"
    ensure (Pinwheel.Compile.I2C.outcome core == result state) s!"compiler result at {t}"
    let command : Pins := ⟨if core.pins.enabled[0] then .low else .release,
      if core.pins.enabled[1] then .low else .release⟩
    ensure (core.pins.levels == 0 && !core.pins.enabled[2]) "compiler unsafe drive"
    if previousCommand.scl == .low && command.scl == .release then
      stretchLeft := stretch clocks.size
    target := {target with scl := if stretchLeft > 0 then .low else .release}
    let bus := resolve command target
    if previous.scl && bus.scl && previous.sda != bus.sda then
      if previous.sda then
        ensure (!started) s!"unexpected START at {t}"
        ensure (t >= cfg.phaseCycles) "insufficient bus-free interval"
        started := true
      else
        ensure started "STOP before START"
        ensure (t - riseAt >= cfg.phaseCycles) "STOP setup too short"
        stopped := true
        pending := none
    if !previous.scl && bus.scl && started && !stopped then
      ensure (t - fallAt >= cfg.phaseCycles) s!"low interval too short at {t}"
      riseAt := t
      pending := some bus.sda
    if previous.scl && !bus.scl then
      fallAt := t
      if let some bit := pending then
        ensure (t - riseAt >= cfg.phaseCycles) s!"high interval too short at {t}"
        clocks := clocks.push bit
        pending := none
    -- The target changes its data command only while SCL is low.
    if !bus.scl then
      let ack := if clocks.size == 8 then reply.addressAck
        else if clocks.size == 17 then reply.dataAck else false
      target := {target with sda := if ack then .low else .release}
    let observed := resolve command target
    if clocks.size == 8 || clocks.size == 17 then
      if observed.scl && pending.isSome then
        ensure (command.sda == .release) "controller drove ACK slot"
    if trace then
      let bit := fun b => if b then 1 else 0
      csv := csv ++ s!"{t},{bit observed.scl},{bit observed.sda},{bit (command.scl == .low)},{bit (command.sda == .low)},{bit (target.scl == .low)},{bit (target.sda == .low)},{repr state.phase},{state.slot.val},{state.remaining.val},{state.waitLeft.val}\n"
    let resetCore := if looped then
        Pinwheel.Engine.Reactive.Fetch.step store core true true (Pinwheel.Compile.I2C.encodeInputs observed)
      else Pinwheel.Engine.Reactive.step p core true true (Pinwheel.Compile.I2C.encodeInputs observed)
    if looped then
      let (loaded, accepted) := Pinwheel.Engine.Reactive.Fetch.load ⟨store, core⟩ store
      ensure (!accepted && loaded.state == core) "looped busy reload"
    ensure (resetCore == Pinwheel.Engine.Reactive.reset p && resetCore.pins == {}) "compiled reset did not clear/release"
    ensure (Pinwheel.Engine.Reactive.load ⟨p, core⟩ p == (⟨p, core⟩, false)) "compiled busy reload"
    if trace then
      for scl in [false, true] do
        for sda in [false, true] do
          let mut refFork := state
          let mut coreFork := core
          for _ in [:cfg.waitCycles + cfg.phaseCycles + 2] do
            let incoming : Bus := ⟨scl, sda⟩
            refFork := step cfg refFork incoming
            coreFork := tick coreFork (Pinwheel.Compile.I2C.encodeInputs incoming)
            ensure (coreFork.pins == Pinwheel.Compile.I2C.encodePins (pins refFork)) "fault-path pin mismatch"
            ensure (Pinwheel.Compile.I2C.outcome coreFork == result refFork) "fault-path result mismatch"
    previous := observed
    previousCommand := command
    core := tick core (Pinwheel.Compile.I2C.encodeInputs observed)
    baseline := Pinwheel.Engine.Reactive.advance p baseline (Pinwheel.Compile.I2C.encodeInputs observed)
    state := step cfg state observed
    stretchLeft := stretchLeft - 1
    cycles := t + 1
    if !busy state then break
  ensure (core == baseline) "store terminal state mismatch"
  ensure (Pinwheel.Compile.I2C.outcome core == result state) "compiler terminal result"
  ensure (core.pins == Pinwheel.Compile.I2C.encodePins (pins state)) "compiler terminal pins"
  ensure (!busy state) "transaction exceeded harness bound"
  let expected := if !reply.addressAck then Outcome.addressNack
    else if !reply.dataAck then Outcome.dataNack else Outcome.success
  ensure (result state == some expected) s!"wrong outcome {repr state.outcome}, expected {repr expected}"
  ensure (started && stopped) "missing START/STOP"
  ensure (clocks.size == if reply.addressAck then 18 else 9) s!"wrong pulse count {clocks.size}"
  for k in [:clocks.size] do
    let expectedBit := if k < 8 then (request.address.val * 2).testBit (7 - k)
      else if k == 8 then !reply.addressAck
      else if k < 17 then request.data.toNat.testBit (16 - k) else !reply.dataAck
    ensure (clocks[k]! == expectedBit) s!"wire bit mismatch at pulse {k}"
  ensure (step cfg state ⟨false, false⟩ == state) "completed state changed without reset"
  if trace then
    let dir := if looped then "build/looped-i2c" else "build/compiled-i2c"
    IO.FS.writeFile s!"{dir}/write-0x53-0xa6-stretched.csv" csv
  return cycles

private def negativeChecks : IO Unit := do
  let variants : List (String × (Pinwheel.Engine.Reactive.Program → Pinwheel.Engine.Reactive.Program)) := [
    ("missing ACK capture", fun p => {p with memory := p.memory.map (fun i => match i with
      | .checked a => .checked {a with terminalCapture := none}
      | _ => i)}),
    ("ignored NACK branch", fun p => {p with memory := p.memory.map (fun i => match i with
      | .checked a => .checked {a with finish := .sequential}
      | _ => i)}),
    ("early ACK capture", fun p => {p with memory := p.memory.map (fun i => match i with
      | .checked a => .checked {a with action := {a.action with capture := a.terminalCapture}, terminalCapture := none}
      | _ => i)})]
  for (name, transform) in variants do
    let failure ← try
      let _ ← transaction ⟨3, 7⟩ ⟨0x53, 0xa6⟩ ⟨false, false⟩ (fun _ => 0)
        (name == "early ACK capture") transform
      pure none
    catch e => pure (some e.toString)
    let expected := if name == "early ACK capture" then "fault-path" else "compiler"
    ensure (failure.any (fun message => (message.splitOn expected).length > 1))
      s!"compiled mutation not rejected: {name}: {failure}"
  IO.println "Rejected missing ACK capture, ignored NACK branch, and early ACK capture programs."

private def reloadCheck : IO Unit := do
  let uart := Pinwheel.Engine.Reactive.embedProgram (Pinwheel.Compile.UART.program ⟨0⟩ 0x53)
  let spi := Pinwheel.Engine.Reactive.embedProgram (Pinwheel.Compile.SPI.program ⟨0⟩ 0xa6)
  let i2c := Pinwheel.Compile.I2C.program ⟨0, 7⟩ ⟨0x53, 0xa6⟩
  let mut m : Pinwheel.Engine.Reactive.Machine := ⟨uart, Pinwheel.Engine.Reactive.reset uart⟩
  for p in [uart, spi, i2c, uart] do
    let (next, accepted) := Pinwheel.Engine.Reactive.load m p
    ensure (accepted && next.state == Pinwheel.Engine.Reactive.reset p) "mixed reload rejected or stale state"
    m := {next with state := Pinwheel.Engine.Reactive.start p 3}
    for _ in [:128] do
      -- With released target SDA the I2C address is NACKed; its program must still issue STOP.
      let observed : Bus := ⟨!m.state.pins.enabled[0], !m.state.pins.enabled[1]⟩
      m := {m with state := Pinwheel.Engine.Reactive.advance p m.state (Pinwheel.Compile.I2C.encodeInputs observed)}
      if !Pinwheel.Engine.Reactive.busy m.state then break
    ensure (m.state.control == .stopped .completed) "mixed protocol execution failed"
    if p == i2c then ensure (Pinwheel.Compile.I2C.outcome m.state == some .addressNack) "reload I2C result"
  IO.println "Passed UART -> SPI -> I2C write/NACK/STOP -> UART through program replacement."

private def loopNegativeChecks : IO Unit := do
  let cfg : Config := ⟨3, 7⟩
  let request : Request := ⟨0x53, 0x3c⟩
  let p := Pinwheel.Compile.I2CLoop.program cfg request
  let variants : List (String × (Pinwheel.Engine.Reactive.Fetch.Store → Pinwheel.Engine.Reactive.Fetch.Store)) := [
    ("wrong byte selection", fun _ => ({p with data := #v[p.data[0], p.data[0]]}).store),
    ("wrong bit order", fun _ => ({p with data := p.data.map BitVec.reverse}).store),
    ("skipped final bit", fun store => {store with
      fetch := fun pc =>
        store.fetch (if pc.val == 30 then 34 else pc)}),
    ("wrong ACK destination", fun store => {store with
      fetch := fun pc =>
        (store.fetch pc).map (fun i => match i with
          | .checked a => .checked {a with terminalCapture := a.terminalCapture.map (fun c => {c with destination := 0})}
            | _ => i)}),
    ("ignored NACK branch", fun store => {store with
      fetch := fun pc =>
        (store.fetch pc).map (fun i => match i with
          | .checked a => .checked {a with finish := .sequential}
          | _ => i)})]
  for (name, transform) in variants do
    let failure ← try
      let _ ← transaction cfg request
        (if name == "ignored NACK branch" then ⟨false, false⟩ else ⟨true, false⟩)
        (fun pulse => pulse % 4) false id true transform
      pure none
    catch e => pure (some e.toString)
    ensure (failure.any (fun message => (message.splitOn "store").length > 1))
      s!"loop mutation not rejected: {name}: {failure}"
  IO.println "Rejected wrong byte, bit order, loop boundary, ACK destination, and NACK branch variants."

private def loopReloadCheck : IO Unit := do
  let uart := Pinwheel.Engine.Reactive.Fetch.Store.ofProgram
    (Pinwheel.Engine.Reactive.embedProgram (Pinwheel.Compile.UART.program ⟨0⟩ 0x53))
  let spi := Pinwheel.Engine.Reactive.Fetch.Store.ofProgram
    (Pinwheel.Engine.Reactive.embedProgram (Pinwheel.Compile.SPI.program ⟨0⟩ 0xa6))
  let first := (Pinwheel.Compile.I2CLoop.program ⟨0, 7⟩ ⟨0x53, 0x3c⟩).store
  let second := (Pinwheel.Compile.I2CLoop.program ⟨0, 7⟩ ⟨0x27, 0xc3⟩).store
  let mut m : Pinwheel.Engine.Reactive.Fetch.Machine := ⟨uart, Pinwheel.Engine.Reactive.Fetch.reset uart⟩
  for store in [uart, spi, first, second, uart] do
    let (loaded, accepted) := Pinwheel.Engine.Reactive.Fetch.load m store
    ensure (accepted && loaded.state == Pinwheel.Engine.Reactive.Fetch.reset store) "loop mixed reload stale state"
    m := {loaded with state := Pinwheel.Engine.Reactive.Fetch.start store 3}
    for _ in [:128] do
      let observed : Bus := ⟨!m.state.pins.enabled[0], !m.state.pins.enabled[1]⟩
      m := {m with state := Pinwheel.Engine.Reactive.Fetch.advance m.program m.state (Pinwheel.Compile.I2C.encodeInputs observed)}
      if !Pinwheel.Engine.Reactive.busy m.state then break
    ensure (m.state.control == .stopped .completed) "loop mixed execution failed"
  IO.println "Passed UART -> SPI -> looped I2C -> changed-data looped I2C -> UART through one fetch machine."

def main (args : List String) : IO Unit := do
  ensure (args.isEmpty || args == ["--looped"]) "usage: CompiledI2C.lean [--looped]"
  let looped := args == ["--looped"]
  let dir := if looped then "build/looped-i2c" else "build/compiled-i2c"
  IO.FS.createDirAll dir
  let mut count := 0
  let mut edges := 0
  for d in ([0, 3] : List (Fin 256)) do
    let cfg : Config := ⟨d, 7⟩
    for byte in [:256] do
      for aa in [false, true] do
        for da in [false, true] do
          for stretched in [false, true] do
            edges := edges + (← transaction cfg ⟨0x53, BitVec.ofNat 8 byte⟩ ⟨aa, da⟩
              (fun pulse => if stretched then pulse % 4 else 0) false id looped)
            count := count + 1
  for addr in [:128] do
    if 8 <= addr && addr < 120 then
      edges := edges + (← transaction ⟨0, 7⟩ ⟨Fin.ofNat 128 addr, 0xa6⟩ ⟨true, true⟩ (fun _ => 1) false id looped)
      count := count + 1
  for byte in [0, 83, 166, 255] do
    for aa in [false, true] do
      for da in [false, true] do
        edges := edges + (← transaction ⟨255, 255⟩ ⟨0x53, BitVec.ofNat 8 byte⟩ ⟨aa, da⟩ (fun _ => 255) false id looped)
        count := count + 1
  let quiet ← transaction ⟨3, 7⟩ ⟨0x53, 0xa6⟩ ⟨true, true⟩ (fun _ => 0) false id looped
  let stretched ← transaction ⟨3, 7⟩ ⟨0x53, 0xa6⟩ ⟨true, true⟩ (fun pulse => pulse % 4) true id looped
  ensure (stretched == quiet + 27) "stretch delay did not add exact blocked observations"
  negativeChecks
  if looped then
    loopNegativeChecks
    loopReloadCheck
  else reloadCheck
  IO.FS.writeFile s!"{dir}/coverage.txt" s!"transactions={count}\nobserved_cycles={edges}\nquiet_example_cycles={quiet}\nstretched_example_cycles={stretched}\n"
  IO.println s!"Passed {count} transactions across {edges} observed cycles; example {quiet} -> {stretched} cycles with stretching."
