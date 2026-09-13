import Pinwheel

open Pinwheel.I2C

private def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

/-- Target and monitor use only pin commands and resolved wire transitions, never controller phases. -/
private def transaction (cfg : Config) (request : Request) (reply : Reply)
    (stretch : Nat → Nat) (trace : Bool := false)
    (transition : Config → State → Bus → State := fun cfg s bus => step cfg s bus) : IO Nat := do
  let mut state := initial cfg request
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
    let command := pins state
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
    ensure (pins (step cfg state observed true) == ({} : Pins)) "reset did not release both lines"
    ensure (result (step cfg state observed true) == some .resetAbort) "reset result mismatch"
    previous := observed
    previousCommand := command
    state := transition cfg state observed
    stretchLeft := stretchLeft - 1
    cycles := t + 1
    if !busy state then break
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
  if trace then IO.FS.writeFile "build/i2c/write-0x53-0xa6-stretched.csv" csv
  return cycles

private def boundaries : IO Unit := do
  let request : Request := ⟨0x53, 0xa6⟩
  for wait in [:256] do
    let cfg : Config := ⟨3, Fin.ofNat 256 wait⟩
    for phase in [Phase.free, .rise, .stopRise] do
      let seed := {initial cfg request with phase := phase}
      let mut s := seed
      for n in [:wait + 1] do
        ensure (busy s) "timeout occurred too early"
        let ready := step cfg s ⟨true, true⟩
        ensure (ready.outcome != .timeout) "ready observation lost to timeout"
        s := step cfg s ⟨false, true⟩
        if n < wait then
          ensure (s.slot == seed.slot && s.outcome == .success && s.remaining == cfg.phaseMinusOne)
            "stretch consumed high time or changed slot/outcome"
      ensure (result s == some .timeout && pins s == ({} : Pins)) "missing timeout/release"
      ensure ((resolve (pins s) ⟨.low, .release⟩).scl == false) "abort falsely repaired stuck clock"
    let cfg : Config := ⟨Fin.ofNat 256 wait, 255⟩
    let seed := {initial cfg request with phase := .high, slot := 8}
    let mut s := seed
    for n in [:wait] do
      s := step cfg s ⟨true, n % 2 == 0⟩
      ensure (s.phase == .high && s.outcome == .success) "premature high completion or ACK capture"
    s := step cfg s ⟨true, true⟩
    ensure (s.phase == .fall && s.outcome == .addressNack) "ACK did not use terminal high observation"
  for phase in [Phase.startHold, .high, .stopHigh] do
    let cfg : Config := ⟨3, 7⟩
    let seed := {initial cfg request with phase := phase}
    ensure (result (step cfg seed ⟨false, true⟩) == some .busFault) "missing unexpected-clock-low fault"
  let cfg : Config := ⟨3, 7⟩
  let mut s := initial cfg request
  for _ in [:8] do s := step cfg s ⟨true, false⟩
  ensure (result s == some .timeout) "stuck SDA did not time out before START"
  IO.println "Passed all 256 wait budgets and high durations, ready-at-deadline, reset, stuck SDA/SCL, and bus-fault cases."

private def negativeChecks : IO Unit := do
  let variants : List (String × (Config → State → Bus → State)) := [
    ("wire bit mismatch", fun cfg s bus => step cfg
      (if s.phase == .free then {s with request := {s.request with data := 0}} else s) bus),
    ("high interval too short", fun cfg s bus =>
      if s.phase == .high then afterHigh cfg s bus.sda else step cfg s bus),
    ("wrong outcome", fun cfg s bus =>
      if s.phase == .rise then move cfg s .high else step cfg s bus)]
  for (expected, transition) in variants do
    let failure ← try
      let _ ← transaction ⟨3, 7⟩ ⟨0x53, 0xa6⟩ ⟨true, true⟩
        (fun _ => if expected == "wrong outcome" then 3 else 0) false transition
      pure none
    catch e => pure (some e.toString)
    ensure (failure.any (fun message => (message.splitOn expected).length > 1))
      s!"faulty transition was not rejected for {expected}: {failure}"
  IO.println "Rejected wrong payload, shortened high period, and ignored stretching variants."

def main : IO Unit := do
  IO.FS.createDirAll "build/i2c"
  let mut count := 0
  let mut edges := 0
  for d in ([0, 3] : List (Fin 256)) do
    let cfg : Config := ⟨d, 7⟩
    for byte in [:256] do
      for aa in [false, true] do
        for da in [false, true] do
          for stretched in [false, true] do
            edges := edges + (← transaction cfg ⟨0x53, BitVec.ofNat 8 byte⟩ ⟨aa, da⟩
              (fun pulse => if stretched then pulse % 4 else 0))
            count := count + 1
  for addr in [:128] do
    if 8 <= addr && addr < 120 then
      edges := edges + (← transaction ⟨0, 7⟩ ⟨Fin.ofNat 128 addr, 0xa6⟩ ⟨true, true⟩ (fun _ => 1))
      count := count + 1
  for byte in [0, 83, 166, 255] do
    for aa in [false, true] do
      for da in [false, true] do
        edges := edges + (← transaction ⟨255, 255⟩ ⟨0x53, BitVec.ofNat 8 byte⟩ ⟨aa, da⟩ (fun _ => 255))
        count := count + 1
  boundaries
  negativeChecks
  let quiet ← transaction ⟨3, 7⟩ ⟨0x53, 0xa6⟩ ⟨true, true⟩ (fun _ => 0)
  let stretched ← transaction ⟨3, 7⟩ ⟨0x53, 0xa6⟩ ⟨true, true⟩ (fun pulse => pulse % 4) true
  ensure (stretched == quiet + 27) "stretch delay did not add exact blocked observations"
  IO.FS.writeFile "build/i2c/coverage.txt" s!"transactions={count}\nobserved_cycles={edges}\nquiet_example_cycles={quiet}\nstretched_example_cycles={stretched}\n"
  IO.println s!"Passed {count} transactions across {edges} observed cycles; example {quiet} -> {stretched} cycles with stretching."
