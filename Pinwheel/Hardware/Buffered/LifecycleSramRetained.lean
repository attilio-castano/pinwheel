import Pinwheel.Hardware.Buffered.LifecycleSramExecution
import Pinwheel.Hardware.Buffered.LifecycleRetained

/-! A retained result survives rejected administrative commands in the full
digital SRAM product, including the renewed registered memory responses. -/
namespace Pinwheel.Hardware.Buffered.Lifecycle
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

private theorem array_state_ext (a b : Memory.Sram.State 6 64)
    (contents : a.contents = b.contents) (q : a.q = b.q) : a = b := by
  cases a
  cases b
  simp_all

private theorem writing_words (i : Values Reactive.Input) (r : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    Reactive.writing.eval i (SramExecution.withWords r words) = Reactive.writing.eval i r := rfl

private theorem control_writing (s : SramState.State) (i : Values Reactive.Input) :
    (Sram.control SharedBranches.writing).eval (s.inputs i) s.registers =
      Reactive.writing.eval (effectiveInputs s i) (effectiveState s i) := by
  rw [SramExecution.control_correct, SharedBranches.writing, SharedBranches.adapt_correct,
    SramExecution.control_expand, ← SramExecution.mappedInput_same, SramExecution.base_inputs]
  rw [writing_words]
  unfold effectiveState
  rw [writing_words]
  rfl

private theorem resetting_state (i : Values Reactive.Input)
    (r t : Values Reactive.Register) : Reactive.resetting.eval i r = Reactive.resetting.eval i t := rfl

private theorem control_resetting (s : SramState.State) (i : Values Reactive.Input) :
    (Sram.control SharedBranches.resetting).eval (s.inputs i) s.registers =
      Reactive.resetting.eval i s.core := by
  rw [SramExecution.control_correct, SharedBranches.resetting, SharedBranches.raw_correct,
    SramExecution.control_expand, SramExecution.base_inputs]
  apply resetting_state

theorem retained_sram_controls (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (retained : s.core .retained = 1) (phase : StoppedPhase (s.core .phase))
    (release : Reactive.releasing.eval i s.core = 0) :
    (Sram.control SharedBranches.resetting).eval (s.inputs i) s.registers = 0 ∧
    (Sram.control SharedBranches.writing).eval (s.inputs i) s.registers = 0 ∧
    Sram.rowWriting.eval (s.inputs i) s.registers = 0 ∧
    Sram.tableWriting.eval (s.inputs i) s.registers = 0 ∧
    Sram.committing.eval (s.inputs i) s.registers = 0 := by
  have mappedWarm : effectiveInputs s i .command ≠ 7#3 := by
    intro same
    exact warm ((effective_command_nonloader s i 7 (by decide) (by decide) (by decide)).mp same)
  rcases held_controls (effectiveInputs s i) (effectiveState s i) cold mappedWarm retained phase
      (by rw [releasing_effective]; exact release) with
    ⟨hr, _, _, hc, hw, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [control_resetting, ← resetting_effective]
    exact hr
  · rw [control_writing]
    exact hw
  · simp only [Sram.rowWriting, SramExecution.control_correct, SharedBranches.rowWriting,
      SharedBranches.both, Expr.eval]
    rw [← SramExecution.control_correct, control_writing, hw]
    simp
  · simp only [Sram.tableWriting, SramExecution.control_correct, SharedBranches.tableWriting,
      SharedBranches.both, Expr.eval]
    rw [← SramExecution.control_correct, control_writing, hw]
    simp
  · rw [committing_effective]
    exact hc

theorem retained_clock (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (retained : s.core .retained = 1) (phase : StoppedPhase (s.core .phase))
    (release : Reactive.releasing.eval i s.core = 0) :
    s.step i = s.step (quiet i) := by
  have quietRelease : Reactive.releasing.eval (quiet i) s.core = 0 := by
    simp [Reactive.releasing, Reactive.both, Reactive.cmd, Expr.eval, quiet]
  rcases retained_sram_controls s i cold warm retained phase release with ⟨hr, hw, hrow, htable, hc⟩
  rcases retained_sram_controls s (quiet i) rfl (by simp [quiet]) retained phase quietRelease with
    ⟨qr, qw, qrow, qtable, qc⟩
  have masks := SramCoverage.masks_hold (s.inputs i) s.registers hr hw
  have qmasks := SramCoverage.masks_hold (s.inputs (quiet i)) s.registers qr qw
  have scalar {w : Nat} (register : Reactive.Register w) (scalar : Scalar register) :
      Sram.circuit.step (s.inputs i) s.registers (.core register) =
        Sram.circuit.step (s.inputs (quiet i)) s.registers (.core register) :=
    (retained_scalar_step s i cold warm retained phase release register scalar).trans
      (retained_scalar_step s (quiet i) rfl (by simp [quiet]) retained phase quietRelease
        register scalar).symm
  have registers :
      @Circuit.step Sram.Input Sram.Register Sram.Output Sram.circuit (s.inputs i) s.registers =
      @Circuit.step Sram.Input Sram.Register Sram.Output Sram.circuit (s.inputs (quiet i)) s.registers := by
    funext w register
    cases register
    case core register =>
      cases register
      case word k => rfl
      case written => exact masks.1.trans qmasks.1.symm
      all_goals apply scalar
      all_goals trivial
    case branchWritten => exact masks.2.trans qmasks.2.symm
    all_goals simp [Circuit.step, Sram.circuit, Sram.next, Expr.eval,
      hrow, htable, hc, qrow, qtable, qc]
  have address (b : Bool) : (Sram.readAddress b).eval (s.inputs i) s.registers =
      (Sram.readAddress b).eval (s.inputs (quiet i)) s.registers := by
    rw [Sram.readAddress_correct, Sram.readAddress_correct, registers]
  have arrays : Memory.Sram.step (Sram.arrayRequest (s.inputs i) s.registers) s.arrays =
      Memory.Sram.step (Sram.arrayRequest (s.inputs (quiet i)) s.registers) s.arrays := by
    funext port
    have contents :
        (Memory.Sram.step (Sram.arrayRequest (s.inputs i) s.registers) s.arrays port).contents =
        (Memory.Sram.step (Sram.arrayRequest (s.inputs (quiet i)) s.registers) s.arrays port).contents := by
      rw [Sram.array_read_preserves_bank _ _ _ hrow port,
        Sram.array_read_preserves_bank _ _ _ qrow port]
    have response :
        (Memory.Sram.step (Sram.arrayRequest (s.inputs i) s.registers) s.arrays port).q =
        (Memory.Sram.step (Sram.arrayRequest (s.inputs (quiet i)) s.registers) s.arrays port).q := by
      rw [Sram.array_response_read _ _ _ hrow port, Sram.array_response_read _ _ _ qrow port, address]
    exact array_state_ext _ _ contents response
  unfold SramState.State.step
  rw [registers, arrays]

end Pinwheel.Hardware.Buffered.Lifecycle
