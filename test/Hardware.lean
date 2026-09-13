import Pinwheel

open Pinwheel.Hardware
open Pinwheel.Hardware.Countdown

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

/-- Clock-edge stimulus, independent of the circuit's control expressions. -/
private def stimuli : Array Inputs := Id.run do
  let mut rows : Array Inputs := #[⟨true, true, 255⟩, {}, {}]
  for duration in [1:257] do
    rows := rows.push ⟨false, true, BitVec.ofNat 8 (duration - 1)⟩
    for _ in [:duration + 2] do rows := rows.push {}
  -- Continuous actions of duration 1, 4, 256, 1: boundary and load coincide.
  for duration in [1, 4, 256, 1] do
    rows := rows.push ⟨false, true, BitVec.ofNat 8 (duration - 1)⟩
    for _ in [:duration - 1] do rows := rows.push {}
  rows := rows.push {}
  -- Interruptions, preemptive loads, reset with load, and idle retention.
  for n in [:4096] do
    rows := rows.push ⟨n % 37 == 0, n % 11 == 0 || n % 13 == 0,
      BitVec.ofNat 8 (73 * n + 19)⟩
  return rows

def main : IO Unit := do
  IO.FS.createDirAll "build/hardware"
  let mlir ← match Emit.countdown with
    | .ok text => pure text
    | .error message => throw <| IO.userError message
  IO.FS.writeFile "build/hardware/countdown.mlir" mlir
  -- An absolute deadline oracle avoids sharing the circuit's decrement recurrence.
  let mut deadline : Option Nat := none
  let mut state : State := ⟨165, 1⟩ -- first reset must establish state, even from a dirty timer
  let mut rows := #["cycle,reset,load,duration_minus_one,boundary_at_edge,remaining,active"]
  let mut cycle := 0
  for input in stimuli do
    let due := !input.reset && deadline == some cycle
    ensure (boundary input state == due) s!"boundary mismatch at edge {cycle}"
    if input.reset then deadline := none
    else if input.load then deadline := some (cycle + input.duration.toNat + 1)
    else if due then deadline := none
    state := tick input state
    let active := deadline.isSome
    let remaining := match deadline with | some endEdge => endEdge - cycle - 1 | none => 0
    ensure (state.active.toNat == active.toNat && state.remaining.toNat == remaining)
      s!"state mismatch at edge {cycle}"
    rows := rows.push s!"{cycle},{input.reset.toNat},{input.load.toNat},{input.duration.toNat},{due.toNat},{state.remaining.toNat},{state.active.toNat}"
    cycle := cycle + 1
  IO.FS.writeFile "build/hardware/countdown-lean.csv" (String.intercalate "\n" rows.toList ++ "\n")
  IO.println s!"Passed {cycle} circuit edges against the absolute-deadline oracle; emitted MLIR and CSV."
