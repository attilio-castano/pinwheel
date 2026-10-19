import Pinwheel.Hardware.Buffered.SpiCircuit

/-! Consequences of actual START admission for the packed SPI circuit. -/
namespace Pinwheel.Hardware.Buffered.SpiAdmission
open Pinwheel.Hardware

private theorem inactive_phase : ∀ p : BitVec 3,
    ~~~BitVec.ofBool (decide (p = 0)) &&& BitVec.ofBool (decide (p.toNat < 5)) = 0 →
      p = 0 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by
  decide +kernel

structure StartingControls (i : Values Reactive.Input) (s : Values Reactive.Register) : Prop where
  executing : SramExecution.ExecutingInput i
  resetting : Reactive.resetting.eval i s = 0
  releasing : Reactive.releasing.eval i s = 0
  entering : Reactive.entering.eval i s = 1
  terminalEdge : Reactive.terminalEdge.eval i s = 0
  heldFault : Reactive.heldFault.eval i s = 0
  heldTimeout : Reactive.heldTimeout.eval i s = 0
  pc : Reactive.entryPC.eval i s = 0
  virtualPC : Reactive.entryVirtual.eval i s = 0
  outer : Reactive.entryOuter.eval i s = 0
  inner : Reactive.entryInner.eval i s = 0

theorem starting_controls (i : Values Reactive.Input) (s : Values Reactive.Register)
    (starting : Reactive.starting.eval i s = 1) : StartingControls i s := by
  have facts := SpiCircuit.starting_facts i s starting
  have phase : s .phase = 0 ∨ s .phase = 5 ∨ s .phase = 6 ∨ s .phase = 7 :=
    inactive_phase (s .phase) facts.busy
  have executing : SramExecution.ExecutingInput i := by
    simp [SramExecution.ExecutingInput, SharedBranches.Runtime, facts.command, facts.cold]
  have resetting := SramExecution.resetting_executing i s executing
  have releasing : Reactive.releasing.eval i s = 0 := by
    simp [Reactive.releasing, Reactive.both, Reactive.cmd, Expr.eval, facts.command]
  have entering : Reactive.entering.eval i s = 1 := by
    simp [Reactive.entering, Reactive.both, Reactive.either, Expr.eval, resetting, starting]
  have inactive : Reactive.terminalEdge.eval i s = 0 ∧
      Reactive.heldFault.eval i s = 0 ∧ Reactive.heldTimeout.eval i s = 0 := by
    rcases phase with phase | phase | phase | phase
    all_goals simp [Reactive.terminalEdge, Reactive.heldFault, Reactive.heldTimeout,
      Reactive.isPhase, Reactive.both, Reactive.either, Expr.eval, phase]
  have absolute : Reactive.absoluteDispatch.eval i s = 0 := by
    simp [Reactive.absoluteDispatch, Reactive.both, Expr.eval, inactive.1]
  refine ⟨executing, resetting, releasing, entering, inactive.1,
    inactive.2.1, inactive.2.2, ?_, ?_, ?_, ?_⟩
  · simp [Reactive.entryPC, Reactive.sequentialPC, Expr.eval, absolute, starting]
  · simp [Reactive.entryVirtual, Expr.eval, starting]
  · simp [Reactive.entryOuter, Reactive.sequentialOuter, Expr.eval, absolute, starting]
  · simp [Reactive.entryInner, Reactive.sequentialInner, Expr.eval, absolute, starting]
  done

theorem starting_record (i : Values Reactive.Input) (s : Values Reactive.Register)
    (starting : Reactive.starting.eval i s = 1) :
    Reactive.entryRecord.eval i s = s (.word 0) := by
  have controls := starting_controls i s starting
  simp [Reactive.entryRecord, Expr.eval, controls.entering,
    Execution.readTree_correct, controls.pc]

theorem starting_data (i : Values Reactive.Input) (s : Values Reactive.Register)
    (starting : Reactive.starting.eval i s = 1) :
    Reactive.entryTx.eval i s = i .txData ∧
    Reactive.entryTxLength.eval i s = i .txLength ∧
    Reactive.entryConsumed.eval i s = 0 ∧ Reactive.entryRxLength.eval i s = 0 ∧
    Reactive.entryCapacity.eval i s = i .rxCapacity := by
  simp [Reactive.entryTx, Reactive.entryTxLength, Reactive.entryConsumed,
    Reactive.entryRxLength, Reactive.entryCapacity, Expr.eval, starting]

end Pinwheel.Hardware.Buffered.SpiAdmission
