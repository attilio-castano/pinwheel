import Pinwheel.Program.BufferedProofs
import Pinwheel.Program.BufferedI2C

/-! Executable checks of composed reference execution. Raw-input fixtures test
control and ownership; separate package peers establish finite wire evidence.
No protocol success, encoded hardware image or universal refinement is claimed. -/
open Pinwheel.Program.Buffered
open Pinwheel.Engine.Reactive (Pins Inputs)
open Pinwheel.Engine.Reactive.Counted (Schedule)

private def check (condition : Bool) (message : String) : IO Unit :=
  if !condition then throw (IO.userError message) else pure ()

private def begin (p : Program) (tx : List Bool) (rxLimit : Nat) : State :=
  let capacity : Pinwheel.Program.Transfer.Capacity := ⟨tx.length, rxLimit⟩
  let owner : Pinwheel.Program.Transfer.Identity := ⟨0, 1⟩
  let prepared := Pinwheel.Program.Transfer.step capacity {} (.prepare 0 tx rxLimit)
  let buffers := (Pinwheel.Program.Transfer.step capacity prepared.state (.start owner 0)).state
  start p capacity (initial p buffers owner)

private def bounded (s : State) : Bool := match s.buffers.slot with
  | .running e | .completed ⟨e, _⟩ =>
    e.txConsumed ≤ e.request.tx.length && e.rx.length ≤ e.request.rxLimit
  | _ => true

private def pcOf (s : State) : Nat := match s.core.control with
  | .active pc _ | .waiting pc _ | .checked pc _ | .qualifying pc _ _ => pc.val
  | .stopped _ => 0

private def i2cPads (cycle : Nat) (s : State) (nack : Option Nat := none)
    (blockFrom : Option Nat := none) : Inputs :=
  let pc := pcOf s
  let stage := if 35 ≤ pc && pc ≤ 38 then some 0
    else if 71 ≤ pc && pc ≤ 74 then some 1
    else if 112 ≤ pc && pc ≤ 115 then some 2 else none
  if blockFrom.any (fun target => target ≤ pc) then 2
  else if stage.isSome then if stage == nack then 3 else 1
  else if 116 ≤ pc && pc < 260 then BitVec.ofNat 2 (1 + 2 * (cycle % 3))
  else 3

private def i2cCase (nack : Option Nat) (blockFrom : Option Nat)
    (outcome : Pinwheel.Program.Transfer.Outcome) (consumed rxCount : Nat) : IO Nat := do
  let p := Pinwheel.Program.BufferedI2C.program 3 31
  let tx := (List.range 24).map fun n => n % 3 == 1
  let capacity : Pinwheel.Program.Transfer.Capacity := ⟨24, 32⟩
  let mut s := begin p tx 32
  let mut edges := 0
  for cycle in [:1400] do
    if owned s then
      s := advance p capacity s (i2cPads cycle s nack blockFrom)
      edges := edges + 1
      check (bounded s) "I2C exceeded its owned data bounds"
  match s.buffers.slot with
  | .completed result =>
    check (result.outcome == outcome) "I2C raw-input control outcome mismatch"
    check (result.execution.txConsumed == consumed) "I2C TX cursor mismatch"
    check (result.execution.rx.length == rxCount) "I2C RX prefix length mismatch"
    check (s.core.pins == p.idle) "I2C terminal outputs did not restore idle"
    check (advance p capacity s 0 == s) "I2C retained completion changed on another edge"
  | _ => throw (IO.userError "I2C raw-input control case did not terminate")
  pure edges

def main : IO Unit := do
  let p := Pinwheel.Program.BufferedI2C.program 3 31
  check (p.code.span == 270 && p.code.words == 50 && p.code.nodes == 105 &&
    p.code.loops == 6 && p.code.nesting == 2) "I2C compact syntax geometry changed"
  let mut edges := 0
  edges := edges + (← i2cCase none none .complete 24 32)
  for stage in [:3] do
    edges := edges + (← i2cCase (some stage) none .fault (8 * (stage + 1)) 0)
  edges := edges + (← i2cCase none (some 0) .timeout 0 0)
  edges := edges + (← i2cCase none (some 136) .timeout 24 5)
  edges := edges + (← i2cCase none (some 263) .timeout 24 32)
  let shift : Instruction := {operation := .shift 0 false false ⟨⟨0, 7⟩, 0, some ⟨0, 2⟩⟩, append := some 1}
  let tiny : Program := ⟨.seq (.emit shift) (.emit {operation := .halt}), ⟨0, 0⟩,
    by decide, by decide, by decide⟩
  let empty := begin tiny [] 1
  match empty.buffers.slot with
  | .completed c =>
    check (c.outcome == .fault && c.execution.txConsumed == 0 && c.execution.rx.isEmpty)
      "underflow changed the owned TX/RX prefix"
    check empty.core.samples[2] "entry scratch capture did not precede data fault"
  | _ => throw (IO.userError "underflow did not retain a fault")
  let overflow := begin tiny [true] 0
  match overflow.buffers.slot with
  | .completed c =>
    check (c.outcome == .fault && c.execution.txConsumed == 1 && c.execution.rx.isEmpty)
      "overflow did not retain consumed TX with unchanged RX"
  | _ => throw (IO.userError "overflow did not retain a fault")
  let valid := begin tiny [false] 1
  let capacity : Pinwheel.Program.Transfer.Capacity := ⟨1, 1⟩
  let stale := {valid with buffers := (Pinwheel.Program.Transfer.step capacity valid.buffers .reset).state}
  check (advance tiny capacity stale 0 == stale) "stale engine changed reset-owned state or sampler"
  let checked : Instruction := {operation := .checked ⟨⟨0, 7⟩, 0, none⟩ ⟨0, 0⟩ none (.jump 0), append := some 0}
  let looping : Program := ⟨.seq (.emit checked) (.emit {operation := .halt}), ⟨0, 0⟩,
    by decide, by decide, by decide⟩
  let mut loopState := begin looping [] 3
  for count in [:3] do
    loopState := advance looping ⟨0, 3⟩ loopState 3
    check (bounded loopState) s!"self-entry bounds at {count}"
  match loopState.buffers.slot with
  | .completed c =>
    check (c.outcome == .fault && c.execution.rx == [true, true, true])
      "self jump failed to append once on each reentry"
  | _ => throw (IO.userError "self-entry overflow did not terminate")
  for pattern in [:4096] do
    let mut s := begin looping [] 3
    for edge in [:8] do
      s := advance looping ⟨0, 3⟩ s (BitVec.ofNat 2 ((pattern / 4 ^ (edge % 6)) % 4))
      check (bounded s) "input-history case violated data bounds"
  IO.println s!"Buffered: 15 composed safety theorems; 2 counted embedding theorems; 3 I2C geometry theorems; 7 I2C control cases/{edges} edges; underflow/overflow/stale-owner/self-entry; 4096 raw-input histories/32768 edges passed"
