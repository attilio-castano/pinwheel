import Pinwheel.Compile.I2CReadProofs
import Pinwheel.Hardware.Execution.Images

open Pinwheel.I2C
open Pinwheel.Compile.I2CRead

private def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

/-- Target decisions depend on observed edges and byte count, never reference phases or PCs. -/
def readTransaction (cfg : Config) (request : RegisterRead.Request) (byte : BitVec 8)
    (acks : Vector Bool 3) (stretch : Nat → Nat) (trace : Bool := false)
    (transform : ReadProgram → ReadProgram := id)
    (backend : ReadProgram → Pinwheel.Engine.Reactive.Fetch.Store 255 15 :=
      Pinwheel.Engine.Reactive.Fetch.Store.ofProgram) : IO Nat := do
  let p := transform (program cfg request)
  let store := backend p
  let mut reference := RegisterRead.initial cfg
  let mut core := Pinwheel.Engine.Reactive.Fetch.start store 3
  let mut target : Pins := {}
  let mut previous : Bus := {}
  let mut previousCommand : Pins := {}
  let mut stretchLeft := 0
  let mut releases := 0
  let mut clocks : Array Bool := #[]
  let mut pending : Option Bool := none
  let mut starts := 0
  let mut stopped := false
  let mut riseAt := 0
  let mut fallAt := 0
  let mut cycles := 0
  let mut csv := "cycle,scl,sda,scl_low,sda_low,target_scl_low,target_sda_low,starts,pulses\n"
  let limit := 160 * cfg.phaseCycles + 40 * (cfg.waitCycles + 2)
  for t in [:limit] do
    ensure (core == lift request reference) s!"reference mismatch at {t}"
    ensure (result core == RegisterRead.result reference) s!"result mismatch at {t}"
    let command : Pins := ⟨if core.pins.enabled[0] then .low else .release,
      if core.pins.enabled[1] then .low else .release⟩
    ensure (core.pins.levels == 0 && !core.pins.enabled[2]) "unsafe drive"
    if previousCommand.scl == .low && command.scl == .release then
      stretchLeft := stretch releases
      releases := releases + 1
    target := {target with scl := if stretchLeft > 0 then .low else .release}
    let bus := resolve command target
    if previous.scl && bus.scl && previous.sda != bus.sda then
      if previous.sda then
        starts := starts + 1
        ensure (starts == 1 || (starts == 2 && clocks.size == 18)) "unexpected START"
        ensure (t - riseAt >= cfg.phaseCycles) "START setup too short"
        pending := none
      else
        ensure (starts > 0 && t - riseAt >= cfg.phaseCycles) "invalid STOP"
        stopped := true
        pending := none
    if !previous.scl && bus.scl && starts > 0 && !stopped then
      ensure (t - fallAt >= cfg.phaseCycles) "low interval too short"
      riseAt := t
      pending := some bus.sda
    if previous.scl && !bus.scl then
      fallAt := t
      if let some bit := pending then
        ensure (t - riseAt >= cfg.phaseCycles) "high interval too short"
        clocks := clocks.push bit
        pending := none
    if !bus.scl then
      let low := if clocks.size == 8 then acks[0]
        else if clocks.size == 17 then acks[1]
        else if clocks.size == 26 then acks[2]
        else if acks[2] && 27 <= clocks.size && clocks.size < 35 then !byte.toNat.testBit (34 - clocks.size)
        else false
      target := {target with sda := if low then .low else .release}
    let observed := resolve command target
    if observed.scl && pending.isSome && clocks.size < (if !acks[0] then 9 else if !acks[1] then 18 else if !acks[2] then 27 else 36) &&
        (clocks.size == 8 || clocks.size == 17 || clocks.size >= 26) then
      ensure (command.sda == .release) "controller drove target data/ACK or final NACK"
    let inputs := Pinwheel.Compile.I2C.encodeInputs observed
    ensure ((Pinwheel.Engine.Reactive.Fetch.step store core true true inputs) ==
      Pinwheel.Engine.Reactive.Fetch.reset store) "reset priority/state"
    let (loaded, accepted) := Pinwheel.Engine.Reactive.Fetch.load ⟨store, core⟩ store
    ensure (!accepted && loaded.state == core) "busy reload changed running program"
    if trace then
      let bit := fun b => if b then 1 else 0
      csv := csv ++ s!"{t},{bit observed.scl},{bit observed.sda},{bit (command.scl == .low)},{bit (command.sda == .low)},{bit (target.scl == .low)},{bit (target.sda == .low)},{starts},{clocks.size}\n"
      for scl in [false, true] do
        for sda in [false, true] do
          let mut rf := reference
          let mut cf := core
          for _ in [:cfg.waitCycles + cfg.phaseCycles + 2] do
            rf := RegisterRead.step cfg rf ⟨scl, sda⟩
            cf := Pinwheel.Engine.Reactive.Fetch.advance store cf (Pinwheel.Compile.I2C.encodeInputs ⟨scl, sda⟩)
            ensure (cf == lift request rf) "fault fork mismatch"
    previous := observed
    previousCommand := command
    core := Pinwheel.Engine.Reactive.Fetch.advance store core inputs
    reference := RegisterRead.step cfg reference observed
    stretchLeft := stretchLeft - 1
    cycles := t + 1
    if !Pinwheel.Engine.Reactive.busy core then break
  ensure (core == lift request reference) "terminal reference mismatch"
  let expected : RegisterRead.Outcome := if !acks[0] then .writeAddressNack
    else if !acks[1] then .registerNack else if !acks[2] then .readAddressNack else .success byte
  ensure (result core == some expected) s!"wrong read result: {repr (result core)}"
  ensure (stopped && starts == if acks[0] && acks[1] then 2 else 1) "missing START/repeated START/STOP"
  let count := if !acks[0] then 9 else if !acks[1] then 18 else if !acks[2] then 27 else 36
  ensure (clocks.size == count) s!"wrong pulse count {clocks.size}"
  let outgoing := #[request.address.val * 2, request.register.toNat, request.address.val * 2 + 1, byte.toNat]
  for k in [:clocks.size] do
    let expectedBit := if k % 9 == 8 then (if k < 27 then !acks[k / 9]! else true)
      else outgoing[k / 9]!.testBit (7 - k % 9)
    ensure (clocks[k]! == expectedBit) s!"wire bit mismatch at {k}"
  ensure ((Pinwheel.Engine.Reactive.Fetch.advance store core 0) == core) "finished state not retained"
  let (reloaded, accepted) := Pinwheel.Engine.Reactive.Fetch.load ⟨store, core⟩ store
  ensure (accepted && reloaded.state == Pinwheel.Engine.Reactive.Fetch.reset store) "stopped reload"
  if trace then IO.FS.writeFile "build/i2c-read/register-read.csv" csv
  return cycles

private def negatives : IO Unit := do
  let variants : List (String × (ReadProgram → ReadProgram)) := [
    ("capture removed", fun p => {p with memory := p.memory.map (fun i => match i with
      | .checked a => .checked {a with terminalCapture := none} | _ => i)}),
    ("capture too early", fun p => {p with memory := p.memory.map (fun i => match i with
      | .checked a => .checked {a with action := {a.action with capture := a.terminalCapture}, terminalCapture := none}
      | _ => i)}),
    ("NACK continuation", fun p => {p with memory := p.memory.map (fun i => match i with
      | .checked a => .checked {a with finish := .sequential} | _ => i)}),
    ("received bit overwrites status", fun p => {p with memory := p.memory.map (fun i => match i with
      | .checked a => .checked {a with terminalCapture := a.terminalCapture.map (fun c =>
          if c.destination.val < 8 then {c with destination := 8} else c)} | _ => i)}),
    ("missing repeated START", fun p => {p with memory := p.memory.set 77 (.halt)}),
    ("final ACK instead of NACK", fun p => {p with memory := p.memory.set 148 (.checked ⟨⟨.openDrain 2, 3, none⟩, Pinwheel.Compile.I2C.clockHigh, none, .sequential⟩)})]
  for (name, transform) in variants do
    let error ← try
      let _ ← readTransaction ⟨3, 7⟩ ⟨0x53, 0xa6⟩ 0x96
        (if name == "NACK continuation" then #v[true, true, false] else #v[true, true, true])
        (fun n => n % 4) true transform
      pure none
    catch e => pure (some e.toString)
    ensure (error.any (fun s => (s.splitOn "mismatch").length > 1)) s!"mutation not rejected: {name}: {error}"
  IO.println "Rejected six capture, status, NACK, repeated-START, and final-NACK mutations."

private def packedTransaction (mode : String) (cfg : Config) (request : RegisterRead.Request)
    (byte : BitVec 8) (acks : Vector Bool 3) (stretch : Nat → Nat) (trace : Bool := false) : IO Nat := do
  let p := program cfg request
  let words := Pinwheel.Hardware.Execution.imageWords p
  let store ← if mode == "direct" then
      pure (Pinwheel.Hardware.Execution.directStore words p.idle p.last)
    else if mode == "indexed" then do
      let some lowered := Pinwheel.Hardware.Execution.lowerIndexed words
        | throw (IO.userError "register-read dictionary overflow")
      pure (lowered.val.store p.idle p.last)
    else pure (Pinwheel.Engine.Reactive.Fetch.Store.ofProgram p)
  readTransaction cfg request byte acks stretch (trace && mode == "typed") id (fun _ => store)

def main (args : List String) : IO Unit := do
  ensure (args.isEmpty || args == ["direct"] || args == ["indexed"]) "usage: I2CRead.lean [direct|indexed]"
  let mode := args.headD "typed"
  IO.FS.createDirAll "build/i2c-read"
  let mut count := 0
  let mut edges := 0
  let replies := [#v[false, true, true], #v[true, false, true], #v[true, true, false], #v[true, true, true]]
  for d in ([0, 3] : List (Fin 256)) do
    for byte in [:256] do
      for acks in replies do
        for stretched in [false, true] do
          edges := edges + (← packedTransaction mode ⟨d, 7⟩ ⟨0x53, 0xa6⟩ (BitVec.ofNat 8 byte) acks
            (fun n => if stretched then n % 4 else 0))
          count := count + 1
  for register in [:256] do
    edges := edges + (← packedTransaction mode ⟨0, 7⟩ ⟨0x53, BitVec.ofNat 8 register⟩ 0x69 #v[true,true,true] (fun _ => 1))
    count := count + 1
  for address in [:128] do
    if 8 <= address && address < 120 then
      edges := edges + (← packedTransaction mode ⟨0, 7⟩ ⟨Fin.ofNat 128 address, 0xa6⟩ 0x96 #v[true,true,true] (fun _ => 0))
      count := count + 1
  for acks in replies do
    edges := edges + (← packedTransaction mode ⟨255, 255⟩ ⟨0x53, 0xa6⟩ 0x96 acks (fun _ => 255))
    count := count + 1
  if mode == "typed" then negatives
  let quiet ← packedTransaction mode ⟨3, 7⟩ ⟨0x53, 0xa6⟩ 0x96 #v[true,true,true] (fun _ => 0)
  let stretched ← packedTransaction mode ⟨3, 7⟩ ⟨0x53, 0xa6⟩ 0x96 #v[true,true,true] (fun n => n % 4) true
  ensure (stretched == quiet + 55) "stretch accounting"
  IO.FS.writeFile (if mode == "typed" then "build/i2c-read/coverage.txt" else s!"build/execution/{mode}-read-coverage.txt") s!"transactions={count}\nobserved_cycles={edges}\nquiet_example_cycles={quiet}\nstretched_example_cycles={stretched}\n"
  IO.println s!"{mode}: passed {count} register reads/NACK transactions, {edges} cycles; example {quiet} -> {stretched}."
