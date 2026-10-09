import Pinwheel.Compile.I2CWriteTransactionProofs
import Lean.Data.Json

/-! Frozen I2C recordings for the offline design explorer.

The canonical compiler and decoded Fetch engine execute one unchanged one-byte
write image in four environments. The edge-driven peer is the ideal resolved-wire
peer from test/I2CWriteTransactions.lean: it observes bus edges and byte count, not
the program counter or reference phase. Every consumed edge is compared with the
independent I2C.WriteTransaction reference. No transition logic runs in the browser.

Reproduce from the repository root:
  lake build Pinwheel.Compile.I2CWriteTransactionProofs
  lake env lean --run scripts/ExplorerI2CTrace.lean docs/explorer/i2c-traces.json

This is the digital consumed-input model, with ideal open-drain resolution and no
input synchronizer delay. It is not paired RTL simulation or physical-chip evidence.
-/

open Lean Pinwheel

private def cfg : I2C.Config := ⟨3, 31⟩
private def request : I2C.WriteTransaction.Request := ⟨0x53, 0, 0xa6⟩
private def compiled := Compile.I2CWriteTransaction.program cfg request
private def store := Hardware.Execution.directStore
  (Hardware.Execution.imageWords compiled) compiled.idle compiled.last

private structure Fixture where
  id : String
  title : String
  scenario : String
  acks : Array Nat
  stretchCycles : Nat := 0
  stuck : Bool := false

private def fixtures : List Fixture := [
  ⟨"i2c-success", "I²C write: acknowledged", "Target acknowledges the address and payload.", #[0, 0], 0, false⟩,
  ⟨"i2c-stretch", "I²C write: clock stretching", "Target holds SCL low for three extra cycles after every controller release, including STOP.", #[0, 0], 3, false⟩,
  ⟨"i2c-nack", "I²C write: address NACK", "Target leaves the address ACK high. The same program branches directly to STOP and skips the payload.", #[1, 1], 0, false⟩,
  ⟨"i2c-timeout", "I²C write: bus never becomes free", "Target holds SCL low from the beginning. Bus qualification consumes its 32-cycle budget before START.", #[0, 0], 0, true⟩]

private def bit (value : Bool) : Nat := if value then 1 else 0

private def require (ok : Bool) (message : String) : IO Unit := do
  unless ok do throw (IO.userError s!"Explorer I2C validation failed: {message}")

private def rawSamples (samples : Vector Bool 16) : Nat :=
  (List.range 16).foldl (fun value k => value + if samples[k]! then 2^k else 0) 0

private def part (slot : Nat) : String :=
  if slot < 9 then "Address" else if slot < 18 then "Payload" else "Unused second payload"

private def slotName (slot : Nat) : String :=
  if slot % 9 == 8 then s!"{part slot} ACK" else s!"{part slot} bit {7 - slot % 9}"

private def instructionLabel (pc : Nat) : String :=
  if pc == 0 then "Qualify free bus"
  else if pc == 1 then "START hold"
  else if pc < 110 then
    let slot := (pc - 2) / 4
    let phase := match (pc - 2) % 4 with
      | 0 => "setup" | 1 => "wait SCL" | 2 => "high" | _ => "fall"
    s!"{slotName slot}: {phase}"
  else if pc == 110 then "STOP: pull both low"
  else if pc == 111 then "STOP: wait SCL"
  else if pc == 112 then "STOP: SCL high hold"
  else if pc == 113 then "STOP: release and qualify"
  else "Halt"

private def instructionDescription (pc : Nat) : String :=
  if pc == 0 then "Release both lines; require four consecutive high observations within a bounded wait budget."
  else if pc == 1 then "Pull SDA low while SCL remains high to form START; guard each high phase."
  else if pc < 110 then
    let slot := (pc - 2) / 4
    let unusedNote := if slot >= 18 then "This slot belongs to the unused second payload byte. " else ""
    unusedNote ++ (match (pc - 2) % 4 with
      | 0 => if slot % 9 == 8 then "Hold SCL low and release SDA so the target owns the ACK bit."
        else "Hold SCL low and set this outgoing data bit using pull-low or release."
      | 1 => "Release SCL and wait for observed SCL high; a low observation consumes the 32-cycle wait budget."
      | 2 => if slot % 9 == 8 then
          s!"Require observed SCL high for four cycles; capture SDA into slot {slot / 9} on the terminal edge. Low means ACK, high means NACK."
        else "Keep the outgoing bit stable and require observed SCL high for four cycles."
      | _ => if slot == 8 then "Hold SCL low, then branch on captured slot 0: NACK goes to STOP at PC 110; ACK starts payload at PC 38."
        else if slot == 17 then "Hold SCL low, then finish this one-byte request at STOP PC 110. The canonical compiler also supports a second payload byte."
        else "Hold SCL low for four cycles, then continue to the next bit.")
  else if pc == 110 then "Pull SCL and SDA low before generating STOP."
  else if pc == 111 then "Release SCL while keeping SDA low; wait for observed SCL high."
  else if pc == 112 then "Hold SDA low for four observed SCL-high cycles."
  else if pc == 113 then "Release SDA to form STOP; require both resolved lines high for four cycles."
  else "Complete the engine and retain the sampled ACK flags. Protocol success is decoded separately."

private def checkedProgram : IO (Array Json) := do
  let words := Hardware.Execution.imageWords compiled
  for pc in [:256] do
    require (Hardware.Execution.decode words[pc]! == some (compiled.fetch (BitVec.ofNat 8 pc).toFin))
      s!"canonical image decode at PC {pc}"
  require (compiled.last.val == 114) "canonical image length"
  let mut instructions := #[]
  for pc in [:compiled.last.val + 1] do
    let instruction := compiled.fetch (Fin.ofNat 256 pc)
    let (kind, duration) : String × Json := match instruction with
      | .action a => ("action", toJson a.duration)
      | .wait _ => ("wait", Json.null)
      | .checked a => ("checked", toJson a.action.duration)
      | .qualify q => ("qualify", toJson (q.durationMinusOne.val + 1))
      | .halt => ("halt", toJson (0 : Nat))
    instructions := instructions.push (Json.mkObj [
      ("pc", toJson pc), ("kind", toJson kind),
      ("label", toJson (instructionLabel pc)),
      ("description", toJson (instructionDescription pc)), ("durationCycles", duration)])
  return instructions

private def phaseName (phase : I2C.WriteTransaction.Phase) : String := match phase with
  | .free => "Bus qualification" | .startHold => "START"
  | .setup slot => s!"{slotName slot.val}: setup"
  | .rise slot => s!"{slotName slot.val}: wait for SCL"
  | .high slot => s!"{slotName slot.val}: high"
  | .fall slot => s!"{slotName slot.val}: fall"
  | .stopLow => "STOP low" | .stopRise => "STOP wait for SCL"
  | .stopHigh => "STOP high" | .stopFree => "STOP qualification"
  | .finished => "Completed" | .timeout => "Timed out" | .fault => "Bus fault"

private def expectedOutcome (f : Fixture) : I2C.WriteTransaction.Outcome :=
  if f.stuck then .timeout else if f.acks[0]! == 1 then .addressNack else .success

private def outcomeJson (f : Fixture) : Json := Json.mkObj [
  ("engine", toJson (if f.stuck then "timeout" else "complete")),
  ("protocol", toJson (if f.stuck then "timeout" else if f.acks[0]! == 1 then "nack" else "success")),
  ("summary", toJson (if f.stuck then
    "Bus qualification timed out before START. The controller released both lines; there is no completed result and zero clocks were sent."
    else if f.acks[0]! == 1 then
    "The engine completed a STOP after address NACK. Capture slot 0 is 1; the payload was skipped. Engine completion does not mean protocol success."
    else "Address and payload were acknowledged, then STOP completed. Capture slots 0 and 1 are both 0 (ACK); the other 14 slots remain untouched."))]

private def controlFields (s : Compile.I2CWriteTransaction.WriteState) : Json × Json × Json :=
  match s.control with
  | .active pc remaining | .checked pc remaining =>
    (toJson pc.val, toJson remaining.val, Json.null)
  | .waiting pc remaining => (toJson pc.val, Json.null, toJson remaining.val)
  | .qualifying pc remaining waitLeft => (toJson pc.val, toJson remaining.val, toJson waitLeft.val)
  | .stopped _ => (Json.null, Json.null, Json.null)

private def frame (cycle : Nat) (s : Compile.I2CWriteTransaction.WriteState)
    (reference : I2C.WriteTransaction.State) (command target : I2C.Pins) (bus : I2C.Bus)
    (captureIndex : Option Nat) (validSlots : Array Nat) (event annotation : String) : Json :=
  let (pc, remaining, waitLeft) := controlFields s
  Json.mkObj [
    ("cycle", toJson cycle), ("pc", pc), ("remaining", remaining), ("waitLeft", waitLeft),
    ("busy", toJson (Engine.Reactive.busy s)),
    ("complete", toJson (s.control == .stopped .completed)),
    ("fault", toJson (s.control == .stopped .fault)),
    ("signals", Json.mkObj [
      ("scl", toJson (bit bus.scl)), ("sda", toJson (bit bus.sda)),
      ("sclEnable", toJson (bit (command.scl == .low))),
      ("sdaEnable", toJson (bit (command.sda == .low))),
      ("peerHeldSCL", toJson (bit (target.scl == .low))),
      ("peerHeldSDA", toJson (bit (target.sda == .low)))]),
    ("captures", toJson (s.samples.toArray.map bit)), ("rawResult", toJson (rawSamples s.samples)),
    ("decoded", Json.null), ("captureIndex", toJson captureIndex),
    ("validSlots", toJson validSlots),
    ("annotation", toJson annotation), ("event", toJson event),
    ("phase", toJson (phaseName reference.phase))]

private def annotation (reference : I2C.WriteTransaction.State) (bus : I2C.Bus) : String :=
  match reference.phase with
  | .free => if bus.scl && bus.sda then "Both lines are high. Count a consecutive free-bus interval before START."
    else "The bus is not free. The qualification interval resets while the bounded wait budget decreases."
  | .startHold => "SDA is pulled low while SCL is high: START."
  | .setup slot => if slot.val % 9 == 8 then "Controller releases SDA; the target owns the ACK bit."
    else "SCL is low; controller establishes the next outgoing bit."
  | .rise _ => if bus.scl then "SCL is observed high; the next edge enters the guarded high interval."
    else "Controller released SCL, but the target still holds it low. Execution stays on the same wait instruction."
  | .high slot => if slot.val % 9 == 8 then "Hold SCL high, then sample the target ACK on the terminal edge."
    else "Guarded high interval: outgoing SDA is held stable."
  | .fall slot => if slot.val == 8 then
      if reference.samples[0] then "Captured address NACK=1. At the end of this low interval, branch to STOP and skip the payload."
      else "Captured address ACK=0. At the end of this low interval, branch to payload PC 38."
    else if slot.val == 17 then "The one-byte payload is finished. The next instruction path goes to STOP."
    else "SCL is pulled low to finish this bit and prepare the next."
  | .stopLow => "Pull both lines low to prepare STOP."
  | .stopRise => if bus.scl then "SCL is high while SDA remains low; enter STOP hold."
    else "The target stretches SCL during STOP; wait for the observed line to rise."
  | .stopHigh => "Hold SDA low while SCL remains high before releasing SDA."
  | .stopFree => "Release SDA while SCL is high: STOP. Qualify both lines high before engine completion."
  | .finished => "Engine completion retains the ACK flags. Decode them to distinguish protocol success from NACK."
  | .timeout => "The wait budget expired. Engine execution stopped and controller drive commands released both lines."
  | .fault => "A guarded observation failed. Execution stopped and controller drives released."

private def source (path : String) (first last : Nat) (label : String) : Json :=
  Json.mkObj [("path", toJson path), ("start", toJson first), ("end", toJson last),
    ("label", toJson label)]

private def sources : Array Json := #[
  source "Pinwheel/Compile/I2CWriteTransaction.lean" 19 45 "Canonical write program and ACK-dependent successors",
  source "Pinwheel/Compile/I2CWriteTransaction.lean" 47 62 "Outcome decoder and decoded-image correspondence",
  source "Pinwheel/I2C/WriteTransaction.lean" 48 80 "Independent wire ordering, ACK capture and branching",
  source "Pinwheel/I2C/WriteTransaction.lean" 98 129 "Reference waits, guarded highs, STOP and terminal outcomes",
  source "Pinwheel/I2C/Bus.lean" 27 35 "Ideal open-drain resolved-wire model",
  source "Pinwheel/Engine/Fetch.lean" 45 87 "Decoded Fetch engine advance semantics",
  source "test/I2CWriteTransactions.lean" 94 162 "Independent edge-driven ACK peer and wire checks"]

private def sourceFiles : List String := [
  "Pinwheel/Compile/I2CWriteTransaction.lean", "Pinwheel/Compile/I2CWriteTransactionProofs.lean",
  "Pinwheel/Compile/I2C.lean", "Pinwheel/Compile/I2CPhases.lean",
  "Pinwheel/Engine/Reactive.lean", "Pinwheel/Engine/Fetch.lean", "Pinwheel/Engine/FetchProofs.lean",
  "Pinwheel/Engine/Step.lean", "Pinwheel/Engine/ISA.lean",
  "Pinwheel/Hardware/Execution/Images.lean", "Pinwheel/Hardware/Execution/Record.lean",
  "Pinwheel/Hardware/Execution/RecordProofs.lean", "Pinwheel/I2C/WriteTransaction.lean",
  "Pinwheel/I2C/WriteTransactionProofs.lean", "Pinwheel/I2C/Spec.lean", "Pinwheel/I2C/Bus.lean",
  "test/I2CWriteTransactions.lean", "scripts/ExplorerI2CTrace.lean"]

private def revision : IO String := do
  let result ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  require (result.exitCode == 0) "cannot identify source revision"
  let value := result.stdout.trimAscii.toString
  require (value.length == 40) "source revision is not a complete Git SHA"
  return value

private def hashes : IO Json := do
  let mut entries := []
  for path in sourceFiles do
    let result ← IO.Process.output { cmd := "shasum", args := #["-a", "256", path] }
    require (result.exitCode == 0) s!"cannot hash {path}"
    let hash := (result.stdout.splitOn " ").head!
    require (hash.length == 64) s!"invalid source hash for {path}"
    entries := entries ++ [(path, toJson hash)]
  return Json.mkObj entries

/-- Peer decisions use only commands, observed edges and finished wire-clock count.
The program and reference are observers of the same resolved digital bus. -/
private def checkedTrace (f : Fixture) (program : Array Json) (revision : String)
    (sourceHashes : Json) : IO (Json × Nat) := do
  require (f.acks.size == 2 && f.acks.all (· ≤ 1)) s!"invalid ACK reply: {f.id}"
  let mut reference := I2C.WriteTransaction.initial cfg
  let mut core := Engine.Reactive.Fetch.start store 3
  let mut target : I2C.Pins := {}
  let mut previous : I2C.Bus := {}
  let mut previousCommand : I2C.Pins := {}
  let mut stretchLeft := 0
  let mut clocks : Array Bool := #[]
  let mut pending : Option Bool := none
  let mut starts := 0
  let mut stopped := false
  let mut frames := #[]
  let mut validSlots : Array Nat := #[]
  let mut captureIndex : Option Nat := none
  let mut transitionEvent := "Program entry"
  let mut cycles := 0
  for t in [:160 * cfg.phaseCycles + 40 * (cfg.waitCycles + 2)] do
    require (core == Compile.I2CWriteTransaction.lift request reference) s!"reference state: {f.id}/{t}"
    require (Compile.I2CWriteTransaction.result request core == I2C.WriteTransaction.result request reference)
      s!"reference outcome: {f.id}/{t}"
    let command : I2C.Pins := ⟨if core.pins.enabled[0] then .low else .release,
      if core.pins.enabled[1] then .low else .release⟩
    require (core.pins.levels == 0 && !core.pins.enabled[2]) s!"open-drain safety: {f.id}/{t}"
    if previousCommand.scl == .low && command.scl == .release then stretchLeft := f.stretchCycles
    target := {target with scl := if f.stuck || stretchLeft > 0 then .low else .release}
    let bus := I2C.resolve command target
    let mut wireEvent := ""
    if previous.scl && bus.scl && previous.sda != bus.sda then
      if previous.sda then
        starts := starts + 1
        require (starts == 1) s!"extra START: {f.id}/{t}"
        wireEvent := "START"
      else
        require (starts == 1) s!"STOP without START: {f.id}/{t}"
        stopped := true
        wireEvent := "STOP"
      pending := none
    if !previous.scl && bus.scl && starts > 0 && !stopped then pending := some bus.sda
    if previous.scl && !bus.scl then
      if let some value := pending then clocks := clocks.push value
      pending := none
    if !bus.scl then
      target := {target with sda := if clocks.size % 9 == 8 && f.acks[clocks.size / 9]?.getD 1 == 0
        then .low else .release}
    let observed := I2C.resolve command target
    if observed.scl && clocks.size % 9 == 8 then
      require (command.sda == .release) s!"controller owns target ACK: {f.id}/{t}"
    let input := Compile.I2C.encodeInputs observed
    require ((Engine.Reactive.Fetch.step store core true true input).pins == ({} : Engine.Reactive.Pins))
      s!"reset release: {f.id}/{t}"
    let note := if let some index := captureIndex then
        s!"Captured SDA into slot {index}: {if core.samples[index]! then "1 (NACK)" else "0 (ACK)"} on the preceding edge. " ++ annotation reference observed
      else annotation reference observed
    let event := if captureIndex.isSome then "ACK capture" else if wireEvent != "" then wireEvent else transitionEvent
    frames := frames.push (frame t core reference command target observed captureIndex validSlots event note)
    captureIndex := none
    transitionEvent := ""
    if !Engine.Reactive.busy core then
      require (Engine.Reactive.Fetch.advance store core input == core) s!"terminal stability: {f.id}"
      frames := frames.push (frame (t + 1) core reference command target observed none validSlots "" (annotation reference observed))
      cycles := t
      break
    let next := Engine.Reactive.Fetch.advance store core input
    match core.control with
    | .checked pc remaining =>
      if remaining.val == 0 then
        match compiled.fetch pc with
        | .checked action =>
          if action.guard.ready input then
            if let some capture := action.terminalCapture then
              captureIndex := some capture.destination.val
              validSlots := validSlots.push capture.destination.val
            match action.finish with
            | .branch sample yes no =>
              let destination := if next.samples[sample.val] then yes.val else no.val
              transitionEvent := s!"Branch to PC {destination}"
            | _ => pure ()
        | _ => pure ()
    | .waiting _ _ => if observed.scl then transitionEvent := "SCL observed high"
    | _ => pure ()
    if !Engine.Reactive.busy next then
      transitionEvent := if next.control == .stopped .completed then "Engine complete"
        else if next.control == .stopped .timeout then "Wait timeout" else "Bus fault"
    previous := observed
    previousCommand := command
    core := next
    reference := I2C.WriteTransaction.step cfg request reference observed
    stretchLeft := stretchLeft - 1
  require (!Engine.Reactive.busy core && frames.size == cycles + 2) s!"terminal frame count: {f.id}"
  require (core == Compile.I2CWriteTransaction.lift request reference) s!"terminal reference: {f.id}"
  require (Compile.I2CWriteTransaction.result request core == some (expectedOutcome f)) s!"expected outcome: {f.id}"
  let expectedClocks := if f.stuck then 0 else if f.acks[0]! == 1 then 9 else 18
  require (clocks.size == expectedClocks) s!"clock count: {f.id}: {clocks.size}"
  require (if f.stuck then starts == 0 && !stopped else starts == 1 && stopped) s!"START/STOP: {f.id}"
  require (rawSamples core.samples == if f.acks[0]! == 1 then 1 else 0) s!"ACK slots: {f.id}"
  require (validSlots == if f.stuck then #[] else if f.acks[0]! == 1 then #[0] else #[0, 1]) s!"valid capture slots: {f.id}"
  let bytes := #[request.address.val * 2, request.payload.toNat]
  for k in [:clocks.size] do
    let expected := if k % 9 == 8 then f.acks[k / 9]! == 1 else bytes[k / 9]!.testBit (7 - k % 9)
    require (clocks[k]! == expected) s!"MSB-first wire bit: {f.id}/{k}"
  require (core.pins == ({} : Engine.Reactive.Pins)) s!"terminal controller release: {f.id}"
  let trace := Json.mkObj [
    ("id", toJson f.id), ("title", toJson f.title), ("protocol", toJson "i2c"),
    ("scenario", toJson f.scenario), ("origin", toJson "Lean decoded reactive Fetch engine with ideal resolved-wire peer"),
    ("scope", toJson "One canonical 256-slot/16-capture I2C write image, decoded from E64 records; every consumed bus observation is cross-checked with I2C.WriteTransaction. Ideal open-drain pull-ups, zero sampler delay. Not paired RTL simulation, analog timing, package measurement or physical-chip qualification."),
    ("sourceRevision", toJson revision), ("sourceHashes", sourceHashes), ("sources", Json.arr sources),
    ("parameters", Json.mkObj [
      ("address", toJson request.address.val), ("payload", toJson (#[0xa6] : Array Nat)),
      ("phaseCycles", toJson cfg.phaseCycles), ("waitCycles", toJson cfg.waitCycles),
      ("stretchCycles", toJson f.stretchCycles), ("stuckSCL", toJson f.stuck),
      ("ackBits", toJson f.acks)]),
    ("signals", Json.arr #[
      Json.mkObj [("key", toJson "scl"), ("label", toJson "Resolved SCL")],
      Json.mkObj [("key", toJson "sda"), ("label", toJson "Resolved SDA")],
      Json.mkObj [("key", toJson "sclEnable"), ("label", toJson "Controller SCL low")],
      Json.mkObj [("key", toJson "sdaEnable"), ("label", toJson "Controller SDA low")],
      Json.mkObj [("key", toJson "peerHeldSCL"), ("label", toJson "Target SCL low")],
      Json.mkObj [("key", toJson "peerHeldSDA"), ("label", toJson "Target SDA low")]]),
    ("program", Json.arr program), ("frames", Json.arr frames), ("outcome", outcomeJson f),
    ("activeCycles", toJson cycles),
    ("convention", toJson "Cycle 0 is program entry. Each frame is the engine state after the preceding edge; its resolved bus is consumed on the next edge. ACK capture markers identify observations latched on the preceding edge. The first terminal state and one stable idle frame are included.")]
  IO.println s!"{f.id}: {cycles} active cycles, {frames.size} states, {clocks.size} wire clocks, {validSlots.size} ACK captures."
  return (trace, cycles)

def main (args : List String) : IO UInt32 := do
  if args.length > 1 then
    IO.eprintln "Usage: lake env lean --run scripts/ExplorerI2CTrace.lean [output.json]"
    return 1
  let output := args.headD "docs/explorer/i2c-traces.json"
  let program ← checkedProgram
  let revision ← revision
  let sourceHashes ← hashes
  let mut traces := #[]
  let mut cycles : Array Nat := #[]
  for fixture in fixtures do
    let (trace, activeCycles) ← checkedTrace fixture program revision sourceHashes
    traces := traces.push trace
    cycles := cycles.push activeCycles
  require (cycles[1]! == cycles[0]! + 19 * 3) "clock-stretch accounting: 18 data/ACK releases plus STOP"
  require (cycles[3]! == cfg.waitCycles) "bus qualification timeout budget"
  IO.FS.writeFile output ((Json.mkObj [("traces", Json.arr traces)]).pretty ++ "\n")
  IO.println s!"Wrote {output}: four independently checked environments for one canonical {program.size}-instruction image."
  return 0
