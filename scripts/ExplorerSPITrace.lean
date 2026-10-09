import Pinwheel.Compile.SPITransaction
import Lean.Data.Json

/-! Export four frozen SPI recordings from the existing compiled reactive-engine
model, checked against both the finite reference and its elapsed-time contract.
The browser only plays these recordings; it does not implement an SPI simulator.

Reproduce from the repository root:
  lake build Pinwheel.Compile.SPITransaction
  lake env lean --run scripts/ExplorerSPITrace.lean docs/explorer/spi-traces.json

MISO is an explicit model-consumed input fixture. Package-pad observation delay,
external peer response and electrical timing are outside these recordings.
-/

open Lean Pinwheel

private abbrev Config := SPI.Transaction.Config
private abbrev State := Engine.Reactive.State 255 15

private def txByte : BitVec 16 := 0xa6
private def rxByte : BitVec 8 := 0x96

private def config (mode : Nat) : Config :=
  { mode := ⟨mode ≥ 2, mode % 2 = 1⟩, halfMinusOne := 3, bytesMinusOne := 0 }

private def bit (value : Bool) : Nat := if value then 1 else 0

private def require (ok : Bool) (message : String) : IO Unit := do
  unless ok do throw (IO.userError s!"Explorer SPI validation failed: {message}")

/-- Fixture history, already at the engine's consumed-input boundary. The first
reply bit is preloaded; later bits change on setup phases for the selected CPHA. -/
private def miso (cfg : Config) (cycle : Nat) : Bool :=
  if cycle < cfg.transferCycles then
    let phase := cycle / cfg.halfCycles
    rxByte.getLsbD (7 - ((phase - if cfg.mode.cpha then 1 else 0) / 2))
  else false

private def incoming (cfg : Config) (cycle : Nat) : Engine.Reactive.Inputs :=
  BitVec.ofNat 2 (bit (miso cfg cycle))

private def execute (cfg : Config) (cycle : Nat) : State :=
  Compile.SPITransaction.execute cfg txByte (incoming cfg) cycle

private def raw (slots : Vector Bool 16) : Nat :=
  (List.finRange 16).foldl (fun value slot => value + bit slots[slot.val] * 2 ^ slot.val) 0

/-- Decode the first eight slots in MSB-first wire order, independently of their
LSB-first raw capture-register representation. Uncaptured bits remain zero. -/
private def decoded (slots : Vector Bool 16) : Nat :=
  (slots.toList.take 8).foldl (fun value slot => 2 * value + bit slot) 0

private def sampleSlot (cfg : Config) (cycle : Nat) : Option (Fin 16) :=
  (List.finRange 16).find? fun slot =>
    slot.val < cfg.bits && SPI.Transaction.sampleTime cfg slot == cycle

private def edgeName (cfg : Config) : String :=
  if cfg.mode.cpol == cfg.mode.cpha then "Rising" else "Falling"

private def phaseLabel (cfg : Config) (phase : Nat) : String :=
  if phase == 0 then "Assert CS / bit 7"
  else match Compile.SPITransaction.entryCapture cfg phase with
    | some c => s!"Sample bit {7 - c.destination.val}"
    | none => if phase == 16 then "Final idle-clock hold"
        else s!"Setup bit {7 - ((phase - if cfg.mode.cpha then 1 else 0) / 2)}"

private def phaseDescription (cfg : Config) (phase : Nat) : String :=
  match Compile.SPITransaction.entryCapture cfg phase with
    | some c => s!"{edgeName cfg} SCLK edge consumes input 0 into capture slot {c.destination.val}; hold commanded pins for four cycles."
    | none => if phase == 0 then
        "Assert chip select, present the first MOSI bit and hold SCLK at its configured idle level."
      else if phase == 16 then
        "Return SCLK to CPOL and retain the final MOSI bit for one half-period before deasserting chip select."
      else "Apply the next setup phase; no receive capture occurs on entry."

private def checkedProgram (cfg : Config) : IO (Array Json) := do
  let compiled := Compile.SPITransaction.program cfg txByte
  let mut instructions := #[]
  for pc in List.finRange 18 do
    let instruction := compiled.fetch ⟨pc.val, by omega⟩
    let (kind, label, description, duration) ← match instruction with
      | .action action => do
        require (pc.val < cfg.phases) s!"action occupies halt slot {pc.val}"
        require (action.duration == cfg.halfCycles) s!"action duration at PC {pc.val}"
        require (action.capture == Compile.SPITransaction.entryCapture cfg pc.val)
          s!"capture operand at PC {pc.val}"
        pure ("action", phaseLabel cfg pc.val, phaseDescription cfg pc.val, action.duration)
      | .halt => do
        require (pc.val == cfg.phases) s!"early halt at PC {pc.val}"
        pure ("halt", "Halt / release CS", "Complete the engine and retain all capture slots; CS_N becomes high, SCLK retains CPOL and MOSI returns low.", 0)
      | _ => throw (IO.userError s!"Unexpected SPI instruction at PC {pc.val}")
    instructions := instructions.push (Json.mkObj [
      ("pc", toJson pc.val), ("kind", toJson kind), ("label", toJson label),
      ("description", toJson description), ("durationCycles", toJson duration)])
  require (instructions.size == 18) "instruction count"
  return instructions

private def frameText (cfg : Config) (cycle : Nat) (state : State) : String × String × String :=
  if cycle == 0 then
    ("start", "Start", "Accepted transfer: assert CS_N, preload bit 7 and begin the first four-cycle half-period.")
  else if cycle == cfg.transferCycles then
    ("complete", "Complete", "Halt entered: CS_N deasserts. Raw capture value 0x69 decodes in wire order to received byte 0x96.")
  else if cycle > cfg.transferCycles then
    ("idle", "Complete", "Completed state and received capture slots remain stable.")
  else match sampleSlot cfg cycle with
    | some slot =>
      ("sample", s!"Sample bit {7 - slot.val}",
        s!"{edgeName cfg} SCLK edge: MISO={bit (miso cfg cycle)} is captured into slot {slot.val} (wire bit {7 - slot.val}). MOSI={bit (state.pins.levels.getLsbD 0)}.")
    | none =>
      let phase := cycle / cfg.halfCycles
      if cycle % cfg.halfCycles == 0 then
        ("setup", phaseLabel cfg phase, phaseDescription cfg phase)
      else ("hold", phaseLabel cfg phase,
        "Hold the current pin commands. The instruction countdown advances; no receive capture occurs on this edge.")

private def checkedFrame (mode : Nat) (cfg : Config) (cycle : Nat) : IO Json := do
  let state := execute cfg cycle
  let reference := SPI.Transaction.run cfg txByte (miso cfg) cycle
  let contractPins := SPI.Transaction.expectedPins cfg txByte cycle
  require (state == Compile.SPITransaction.liftState cfg reference)
    s!"mode {mode}: finite-reference correspondence at cycle {cycle}"
  require (state.pins == Engine.Reactive.Pins.pushPull (Compile.SPI.encodePins contractPins))
    s!"mode {mode}: independent waveform at cycle {cycle}"
  require (state.samples == SPI.Transaction.expectedSamples cfg (miso cfg) cycle)
    s!"mode {mode}: independent capture contract at cycle {cycle}"
  require (Engine.Reactive.busy state == decide (cycle < cfg.transferCycles))
    s!"mode {mode}: busy boundary at cycle {cycle}"
  require ((Engine.Reactive.result state).isSome == decide (cfg.transferCycles ≤ cycle))
    s!"mode {mode}: complete boundary at cycle {cycle}"
  require (state.pins.enabled == 7) s!"mode {mode}: push-pull output enables"
  if let some slot := sampleSlot cfg cycle then
    require (state.samples[slot.val] == rxByte.getLsbD (7 - slot.val))
      s!"mode {mode}: sampled reply bit at cycle {cycle}"
    require (state.pins.levels.getLsbD 0 == txByte.getLsbD (7 - slot.val))
      s!"mode {mode}: MOSI bit at sample edge {cycle}"
    require ((execute cfg (cycle - 1)).pins.levels.getLsbD 1 != state.pins.levels.getLsbD 1)
      s!"mode {mode}: capture occurs on an SCLK transition at cycle {cycle}"
    require (state.pins.levels.getLsbD 1 == (cfg.mode.cpol == cfg.mode.cpha))
      s!"mode {mode}: selected sample edge polarity at cycle {cycle}"
  let (pc, remaining) ← match state.control with
    | .active pc remaining => pure (toJson pc.val, toJson remaining.val)
    | .stopped .completed => pure (Json.null, Json.null)
    | _ => throw (IO.userError s!"Unexpected SPI control at cycle {cycle}")
  let (event, phase, annotation) := frameText cfg cycle state
  let captureIndex := match sampleSlot cfg cycle with
    | some slot => toJson slot.val
    | none => Json.null
  let validSlots := ((List.finRange 16).filter fun slot =>
    slot.val < cfg.bits && SPI.Transaction.sampleTime cfg slot ≤ cycle).map Fin.val
  return Json.mkObj [
    ("cycle", toJson cycle), ("pc", pc), ("remaining", remaining),
    ("busy", toJson (Engine.Reactive.busy state)),
    ("complete", toJson (Engine.Reactive.result state).isSome), ("fault", toJson false),
    ("signals", Json.mkObj [
      ("cs_n", toJson (bit (state.pins.levels.getLsbD 2))),
      ("sclk", toJson (bit (state.pins.levels.getLsbD 1))),
      ("mosi", toJson (bit (state.pins.levels.getLsbD 0))),
      ("miso", toJson (bit (miso cfg cycle)))]),
    ("captures", toJson (state.samples.toList.map bit)),
    ("captureIndex", captureIndex), ("validSlots", toJson validSlots),
    ("rawResult", toJson (raw state.samples)), ("decoded", toJson (decoded state.samples)),
    ("annotation", toJson annotation), ("event", toJson event), ("phase", toJson phase)]

private def source (path : String) (first last : Nat) (label : String) : Json :=
  Json.mkObj [("path", toJson path), ("start", toJson first), ("end", toJson last),
    ("label", toJson label)]

private def sources : Array Json := #[
  source "Pinwheel/SPI/Transaction.lean" 25 41 "Independent SPI waveform and sample-time contract",
  source "Pinwheel/SPI/Transaction.lean" 69 92 "Finite phase/tick reference model",
  source "Pinwheel/Compile/SPITransaction.lean" 10 29 "Mode-specific timed actions and entry captures",
  source "Pinwheel/Compile/SPITransaction.lean" 99 124 "Compiled execution, waveform, captures and completion",
  source "Pinwheel/Engine/Reactive.lean" 124 143 "Capture on action entry and halt completion",
  source "docs/protocols/spi-transactions.md" 16 46 "Four SPI modes and MSB-first receive interpretation",
  source "scripts/ExplorerSPITrace.lean" 34 58 "Consumed-input fixture and raw versus wire-order decode"]

private def sourceFiles : List String := [
  "Pinwheel/SPI/Spec.lean", "Pinwheel/SPI/Transaction.lean", "Pinwheel/Compile/SPI.lean",
  "Pinwheel/Compile/SPITransaction.lean", "Pinwheel/Engine/ISA.lean",
  "Pinwheel/Engine/Step.lean", "Pinwheel/Engine/Reactive.lean",
  "scripts/ExplorerSPITrace.lean"]

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

private def checkedTrace (mode : Nat) (rev : String) (sourceHashes : Json) : IO Json := do
  let cfg := config mode
  let program ← checkedProgram cfg
  let mut frames := #[]
  for cycle in List.range (cfg.transferCycles + 2) do
    frames := frames.push (← checkedFrame mode cfg cycle)
  require (cfg.halfCycles == 4 && cfg.bits == 8 && cfg.transferCycles == 68 && frames.size == 70)
    s!"mode {mode}: trace dimensions"
  let initial := execute cfg 0
  let lastActive := execute cfg 67
  let completed := execute cfg 68
  require (initial.control == .active 0 3) s!"mode {mode}: entry convention"
  require (lastActive.control == .active 16 0) s!"mode {mode}: last active interval"
  require (completed.control == .stopped .completed) s!"mode {mode}: halt entry"
  require (execute cfg 69 == completed) s!"mode {mode}: stable completion"
  require (raw completed.samples == 0x69 && decoded completed.samples == rxByte.toNat)
    s!"mode {mode}: raw and decoded receive result"
  require (((List.range 70).filter (fun cycle => (sampleSlot cfg cycle).isSome)).length == 8)
    s!"mode {mode}: eight sample events, including zero-valued samples"
  return Json.mkObj [
    ("id", toJson s!"spi-mode-{mode}"), ("title", toJson s!"SPI mode {mode}: 0xA6 → 0x96"),
    ("protocol", toJson "spi"),
    ("scenario", toJson s!"Mode {mode} · CPOL={bit cfg.mode.cpol}, CPHA={bit cfg.mode.cpha}"),
    ("origin", toJson "Lean compiled reactive-engine model"),
    ("scope", toJson "256-position, 16-capture model executing Compile.SPITransaction.program, checked against the finite SPI reference and independent elapsed-time waveform/capture contracts. MISO is the value consumed by input 0. Package sampling delay, RTL simulation, electrical timing and physical-chip behavior are outside this recording."),
    ("sourceRevision", toJson rev), ("sourceHashes", sourceHashes),
    ("sources", Json.arr sources),
    ("parameters", Json.mkObj [("mode", toJson mode), ("txByte", toJson txByte.toNat),
      ("rxByte", toJson rxByte.toNat), ("halfCycles", toJson cfg.halfCycles)]),
    ("signals", Json.arr #[
      Json.mkObj [("key", toJson "cs_n"), ("label", toJson "CS_N")],
      Json.mkObj [("key", toJson "sclk"), ("label", toJson "SCLK")],
      Json.mkObj [("key", toJson "mosi"), ("label", toJson "MOSI")],
      Json.mkObj [("key", toJson "miso"), ("label", toJson "MISO (consumed)")]]),
    ("program", Json.arr program), ("frames", Json.arr frames),
    ("outcome", Json.mkObj [("engine", toJson "complete"), ("protocol", toJson "success"),
      ("summary", toJson "Transmitted 0xA6 and received 0x96; raw capture register is 0x69 because slot zero contains the first wire bit.")]),
    ("activeCycles", toJson cfg.transferCycles),
    ("convention", toJson "State immediately after each engine edge; action entry is cycle 0. A capture occurs on entry to its sample phase and consumes incoming(cycle). MISO history is already at the engine input boundary; no package-pad delay is modeled.")]

def main (args : List String) : IO UInt32 := do
  if args.length > 1 then
    IO.eprintln "Usage: lake env lean --run scripts/ExplorerSPITrace.lean [output.json]"
    return 1
  let output := args.headD "docs/explorer/spi-traces.json"
  let rev ← revision
  let sourceHashes ← hashes
  let mut traces := #[]
  for mode in List.range 4 do
    traces := traces.push (← checkedTrace mode rev sourceHashes)
  IO.FS.writeFile output ((Json.mkObj [("traces", Json.arr traces)]).pretty ++ "\n")
  IO.println s!"Wrote {output}: four modes, 18 instructions and 70 checked model states each; eight explicit sample events per mode."
  return 0
