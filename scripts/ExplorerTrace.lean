import Pinwheel.Compile.UART
import Lean.Data.Json

/-! Export the explorer's frozen UART recording from the existing compiled-engine
model. No transition logic is duplicated here or evaluated in the browser.

Reproduce from the repository root:
  lake build Pinwheel.Compile.UART
  lake env lean --run scripts/ExplorerTrace.lean docs/explorer/uart-trace.json

This records the 32-slot educational Engine model. It is not a recording of the
paired hardware, RTL simulation, or a physical chip.
-/

open Lean Pinwheel

private def cfg : UART.Config := { durationMinusOne := 3 }
private def byte : BitVec 8 := 0x53

private def symbol (pc : Nat) : String :=
  if pc == 0 then "Start"
  else if pc == 9 then "Stop"
  else if pc == 10 then "Halt"
  else s!"Data bit {pc - 1}"

private def bit (value : Bool) : Nat := if value then 1 else 0

private def require (ok : Bool) (message : String) : IO Unit := do
  unless ok do throw (IO.userError s!"Explorer trace validation failed: {message}")

private def checkedFrame (cycle : Nat) : IO Json := do
  let state := Compile.UART.execute cfg byte (fun _ => false) cycle
  let reference := UART.run (UART.initial cfg byte) cycle
  let tx := state.levels.getLsbD 0
  require (tx == UART.expected cfg byte cycle) s!"TX contract at cycle {cycle}"
  require (Engine.busy state == UART.busy reference) s!"UART busy model at cycle {cycle}"
  require (Engine.busy state == decide (cycle < cfg.frameCycles)) s!"busy boundary at cycle {cycle}"
  require (state.samples == Vector.replicate 8 false) s!"unexpected capture at cycle {cycle}"
  require ((Engine.result state).isSome == decide (cfg.frameCycles ≤ cycle))
    s!"completion/result boundary at cycle {cycle}"
  let (pc, remaining, label) := match state.control with
    | .active pc remaining => (toJson pc.val, toJson remaining.val, symbol pc.val)
    | .stopped _ => (Json.null, Json.null, "Idle")
  return Json.mkObj [
    ("cycle", toJson cycle), ("pc", pc), ("remaining", remaining),
    ("tx", toJson (bit tx)), ("busy", toJson (Engine.busy state)),
    ("complete", toJson (Engine.result state).isSome), ("symbol", toJson label)]

private def checkedProgram : IO (Array Json) := do
  let compiled := Compile.UART.program cfg byte
  let mut instructions := #[]
  for pc in List.finRange 11 do
    let instruction := compiled.fetch ⟨pc.val, by omega⟩
    let data : Bool × Nat × String ← match instruction with
      | .action action => do
        require (pc.val < 10) "an action occupies the halt slot"
        require (action.duration == cfg.cycles) s!"action duration at PC {pc.val}"
        require (action.capture.isNone) s!"UART unexpectedly captures at PC {pc.val}"
        pure (action.levels.getLsbD 0, action.duration, "action")
      | .halt => do
        require (pc.val == 10) s!"early halt at PC {pc.val}"
        pure (compiled.idle.getLsbD 0, 0, "halt")
    let (tx, duration, kind) := data
    instructions := instructions.push (Json.mkObj [
      ("pc", toJson pc.val), ("symbol", toJson (symbol pc.val)),
      ("tx", toJson (bit tx)), ("durationCycles", toJson duration), ("kind", toJson kind)])
  require (instructions.size == 11) "instruction count"
  return instructions

private def source (path : String) (first last : Nat) (label : String) : Json :=
  Json.mkObj [("path", toJson path), ("start", toJson first), ("end", toJson last),
    ("label", toJson label)]

private def sources : Array Json := #[
  source "Pinwheel/Compile/UART.lean" 8 18 "UART action and program compiler",
  source "Pinwheel/Compile/UART.lean" 63 100 "Compiled-model execution and correspondence proofs",
  source "Pinwheel/Engine/Step.lean" 23 62 "Engine control, completion, and edge semantics",
  source "Pinwheel/UART/Spec.lean" 12 25 "Independent UART waveform contract",
  source "Pinwheel/UART/Tx.lean" 19 58 "UART transmitter reference model"]

private def sourceFiles : List String := [
  "Pinwheel/Compile/UART.lean", "Pinwheel/Engine/Step.lean", "Pinwheel/Engine/ISA.lean",
  "Pinwheel/UART/Spec.lean", "Pinwheel/UART/Tx.lean", "scripts/ExplorerTrace.lean"]

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

def main (args : List String) : IO UInt32 := do
  if args.length > 1 then
    IO.eprintln "Usage: lake env lean --run scripts/ExplorerTrace.lean [output.json]"
    return 1
  let output := args.headD "docs/explorer/uart-trace.json"
  let program ← checkedProgram
  let mut frames := #[]
  for cycle in List.range (cfg.frameCycles + 2) do
    frames := frames.push (← checkedFrame cycle)
  require (cfg.cycles == 4 && cfg.frameCycles == 40 && frames.size == 42) "trace dimensions"
  let initial := Compile.UART.execute cfg byte (fun _ => false) 0
  let lastActive := Compile.UART.execute cfg byte (fun _ => false) 39
  let completed := Compile.UART.execute cfg byte (fun _ => false) 40
  require (initial.control == .active 0 3) "action-entry convention"
  require (lastActive.control == .active 9 0) "last active interval"
  require (completed.control == .stopped .completed) "halt entry"
  require (Compile.UART.execute cfg byte (fun _ => false) 41 == completed) "stable completed state"
  let trace := Json.mkObj [
    ("id", toJson "uart-tx-53"), ("title", toJson "UART transmission: 0x53"),
    ("origin", toJson "Lean compiled-engine model"),
    ("scope", toJson "32-slot educational Engine model executing Compile.UART.program; correspondence to the UART contract is proved in Lean. This is not paired RTL simulation or physical-chip evidence."),
    ("sourceRevision", toJson (← revision)), ("sourceHashes", ← hashes),
    ("byte", toJson byte.toNat), ("cyclesPerBit", toJson cfg.cycles),
    ("activeCycles", toJson cfg.frameCycles),
    ("convention", toJson "State immediately after each edge; action entry is cycle 0."),
    ("sources", Json.arr sources), ("program", Json.arr program), ("frames", Json.arr frames)]
  IO.FS.writeFile output (trace.pretty ++ "\n")
  IO.println s!"Wrote {output}: {program.size} instructions, {frames.size} checked model states."
  return 0
