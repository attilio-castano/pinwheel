import Pinwheel.Hardware.Buffered.GenericObservation
import Pinwheel.Hardware.Buffered.GenericStart
import Pinwheel.Hardware.Buffered.MemoEval

/-! Independent source and packed-circuit execution over all eight operations.
No refinement theorem supplies the expected observations. The circuit bank is
materialized at each edge using the separately qualified memo evaluator. This
executable is a native evaluator control; kernel proofs remain separate. -/
namespace Pinwheel.Test.GenericExecution
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive
open Pinwheel.Hardware.Buffered

private def program (instruction : Program.Buffered.Instruction) : Program.Buffered.Program :=
  ⟨.seq (.emit instruction) (.emit {operation := .halt}), ⟨0, 0⟩,
    by simp [Counted.Schedule.span], by simp [Counted.Schedule.nodes],
    by simp [Counted.Schedule.nesting]⟩

private def mapPC (pc : Program.Buffered.PC) : GenericLayout.Coordinates :=
  ⟨BitVec.ofNat 7 pc.val, 0, 0⟩

private def initial (instruction : Program.Buffered.Instruction) : Values Reactive.Register
  | _, .word k =>
    if k == 0 then GenericLayout.record mapPC 0 instruction
    else if k == 1 then 3 else 0
  | _, .valid => 1
  | _, .count => 2
  | _, .virtualSpan => 2
  | _, .generation => 2
  | _, .transfer => 3
  | _, .levels => 5
  | _, .enabled => 3
  | _, .scratch => 65535
  | _, .stage1 => 1
  | _, .stage2 => 2
  | _, _ => 0

private def input (txLength rxCapacity : Nat) : Values Reactive.Input
  | _, .command => 3
  | _, .expectedGeneration => 2
  | _, .txData => 4294967205
  | _, .txLength => BitVec.ofNat 6 txLength
  | _, .rxCapacity => BitVec.ofNat 6 rxCapacity
  | _, .rawInputs => 3
  | _, _ => 0

private structure Snapshot where
  bank : Array Nat

private def snapshot (s : Values Reactive.Register) : Snapshot :=
  ⟨Reactive.registers.map (fun ⟨_, r⟩ => (s r).toNat)⟩

private def Snapshot.values (s : Snapshot) : Values Reactive.Register := fun {w} r =>
  BitVec.ofNat w (s.bank[Reactive.registerIndex r]?.getD 0)

private def expressions : Array (Sigma Reactive.E) :=
  Reactive.registers.map (fun ⟨w, r⟩ => ⟨w, Reactive.next r⟩)

private def tick (s : Snapshot) (i : Values Reactive.Input) : Snapshot :=
  ⟨MemoEval.evalMany i s.values expressions⟩

private def execution (s : Program.Buffered.State) : Option Transfer.Execution :=
  match s.buffers.slot with
  | .running e => some e
  | .completed c => some c.execution
  | _ => none

private def position (s : Program.Buffered.State) : Nat × Nat × Nat :=
  match s.core.control with
  | .stopped _ => (0, 0, 0)
  | .active pc remaining | .waiting pc remaining | .checked pc remaining => (pc.val, remaining.val, 0)
  | .qualifying pc remaining waitLeft => (pc.val, remaining.val, waitLeft.val)

private def agrees (actual : Snapshot) (source : Program.Buffered.State) : Bool :=
  let r : Values Reactive.Register := actual.values
  let pos := position source
  let control := r .phase == Refinement.controlPhase source.core.control &&
    r .virtualPC == BitVec.ofNat 10 pos.1 && r .pc == BitVec.ofNat 7 pos.1 &&
    r .remaining == BitVec.ofNat 8 pos.2.1 &&
    (if r .phase == 4 then r .waitLeft == BitVec.ofNat 8 pos.2.2 else true) &&
    r .levels == source.core.pins.levels && r .enabled == source.core.pins.enabled &&
    r .scratch == (BitVec.ofBoolListLE source.core.samples.toList).setWidth 16 &&
    r .retained == BitVec.ofBool (Refinement.slotRetained source.buffers.slot) &&
    (if Engine.Reactive.busy source.core then
      r .stage1 == source.samplerFirst && r .stage2 == source.samplerSecond else true)
  match execution source with
  | none => false
  | some e => control && r .txConsumed == BitVec.ofNat 6 e.txConsumed &&
      r .txData == (4294967205#32 >>> e.txConsumed) &&
      r .txLength == BitVec.ofNat 6 e.request.tx.length &&
      r .rxCapacity == BitVec.ofNat 6 e.request.rxLimit &&
      r .rxLength == BitVec.ofNat 6 e.rx.length && r .rxData == SpiPacking.rxWord e.rx &&
      r .generation == BitVec.ofNat 16 e.request.programGeneration &&
      r .transfer == BitVec.ofNat 16 e.request.identity.sequence

private def action : Action 15 := ⟨⟨1, 7⟩, 1, some ⟨1, 5⟩⟩

private def fixtures : List (String × Program.Buffered.Instruction × Nat × Nat) :=
  [("drive", {operation := .drive action, append := some 0}, 1, 4),
   ("shift", {operation := .shift 2 true true action, append := some 1}, 1, 4),
   ("keep", {operation := .keep 5 3 action, append := some 0}, 1, 4),
   ("halt", {operation := .halt, append := some 1}, 0, 0),
   ("fault", {operation := .fault .fault, append := some 0}, 0, 0),
   ("timeout", {operation := .fault .timeout}, 0, 0),
   ("wait", {operation := .wait ⟨⟨0, 7⟩, ⟨0, true⟩, 1⟩, preserveLevels := 5, preserveEnabled := 3}, 0, 0),
   ("checked", {operation := .checked action ⟨1, 1⟩ (some ⟨0, 0⟩) .sequential}, 0, 0),
   ("branch", {operation := .checked {action with durationMinusOne := 0} ⟨0, 0⟩ (some ⟨0, 0⟩) (.branch 0 (.absolute 0) (.absolute 1)), append := some 1}, 0, 4),
   ("jump", {operation := .checked {action with durationMinusOne := 0} ⟨0, 0⟩ none (.jump 0)}, 0, 4),
   ("qualify", {operation := .qualify ⟨⟨0, 7⟩, ⟨1, 1⟩, 1, 2⟩, preserveLevels := 5, preserveEnabled := 3}, 0, 0),
   ("underflow", {operation := .shift 0 false false action, append := some 1}, 0, 0),
   ("overflow", {operation := .shift 0 false false action, append := some 1}, 1, 0)]

private def check : IO Unit := do
  let mut checked := 0
  for (label, instruction, tx, rx) in fixtures do
    IO.println s!"Generic execution: checking {label}"
    let p := program instruction
    let i : Values Reactive.Input := input tx rx
    let before := snapshot (initial instruction)
    unless Reactive.starting.eval i before.values == 1 do
      throw (IO.userError s!"unadmitted fixture: {label}")
    for history in List.range 256 do
      let mut actual := tick before i
      let mut source := GenericStart.started p before.values i
      for edge in List.range 13 do
        unless agrees actual source do
          throw (IO.userError s!"source/circuit mismatch: {label}, history={history}, edge={edge}")
        checked := checked + 1
        let raw := BitVec.ofNat 2 (history / 4^(edge % 4))
        actual := tick actual (SpiStart.quietInput raw)
        source := Program.Buffered.advance p Refinement.capacity source raw
  IO.println s!"Generic execution: {fixtures.length} fixtures, all 256 four-sample histories, {checked} source/circuit prefixes; passed"

end Pinwheel.Test.GenericExecution

def main : IO Unit := Pinwheel.Test.GenericExecution.check
