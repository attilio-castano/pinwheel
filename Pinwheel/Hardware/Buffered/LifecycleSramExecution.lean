import Pinwheel.Hardware.Buffered.LifecycleExecution

namespace Pinwheel.Hardware.Buffered.Lifecycle
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

private theorem branchBit_inputs (i j : Values Reactive.Input) (r : Values Reactive.Register) :
    Reactive.branchBit.eval i r = Reactive.branchBit.eval j r := by
  rfl
  done

private theorem branchBit_words (i : Values Reactive.Input) (r : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    Reactive.branchBit.eval i (SramExecution.withWords r words) = Reactive.branchBit.eval i r := by
  rfl
  done

theorem branchDecision_inputs (s : SramState.State) (i j : Values Reactive.Input) :
    Sram.branchDecision.eval (s.inputs i) s.registers =
      Sram.branchDecision.eval (s.inputs j) s.registers := by
  simp only [Sram.branchDecision, SramExecution.control_correct,
    SharedBranches.adapt_correct, SramExecution.control_expand, branchBit_words]
  apply branchBit_inputs
  done

theorem effectiveState_quiet (s : SramState.State) (i : Values Reactive.Input)
    (starting : Sram.starting.eval (s.inputs i) s.registers = 0) :
    @effectiveState s i = @effectiveState s (quiet i) := by
  have qs : Sram.starting.eval (s.inputs (quiet i)) s.registers = 0 := by
    rw [starting_effective, starting_direct]
    exact (SpiCircuit.quiet_controls (quiet i) s.core (quiet_input i)).2.2.1
  have instruction : Sram.instruction.eval (s.inputs i) s.registers =
      Sram.instruction.eval (s.inputs (quiet i)) s.registers := by
    simp only [Sram.instruction, Expr.eval, starting, qs, branchDecision_inputs s i (quiet i)]
    rfl
  have rows (k : BitVec 6) : (Sram.rowExpr k).eval (s.inputs i) s.registers =
      (Sram.rowExpr k).eval (s.inputs (quiet i)) s.registers := by
    simp only [Sram.rowExpr, Expr.eval, instruction]
  have selected : @SramExecution.selectedShared (s.inputs i) s.registers =
      @SramExecution.selectedShared (s.inputs (quiet i)) s.registers := by
    funext w register
    cases register
    case row k => exact rows k
    all_goals rfl
  have words : SramExecution.selectedWords (s.inputs i) s.registers =
      SramExecution.selectedWords (s.inputs (quiet i)) s.registers := by
    unfold SramExecution.selectedWords
    rw [selected]
  unfold effectiveState
  rw [words]
  done

theorem execution_scalar_clock (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (busy : Reactive.busy.eval i s.core = 1) (retained : s.core .retained = 0)
    (register : Reactive.Register w) (scalar : Scalar register) :
    (s.step i).core register = (s.step (quiet i)).core register := by
  have mappedWarm : effectiveInputs s i .command ≠ 7#3 := by
    intro same
    exact warm ((effective_command_nonloader s i 7 (by decide) (by decide) (by decide)).mp same)
  have controls := execution_controls (effectiveInputs s i) (effectiveState s i)
    cold mappedWarm busy retained
  have start : Sram.starting.eval (s.inputs i) s.registers = 0 := by
    rw [starting_effective]
    exact controls.starting
  have stateEq := effectiveState_quiet s i start
  rw [stateEq] at controls
  rw [scalar_step s i register scalar, scalar_step s (quiet i) register scalar]
  rw [stateEq]
  rw [effective_runtime s (quiet i) (by simp [SharedBranches.Runtime, quiet])]
  exact congrArg (fun bank : Values Reactive.Register => bank register)
    (reactive_clock (effectiveInputs s i) (quiet i) (effectiveState s (quiet i))
      controls (quiet_controls i _) rfl)
  done

private theorem writing_words (i : Values Reactive.Input) (r : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    Reactive.writing.eval i (SramExecution.withWords r words) = Reactive.writing.eval i r := by
  rfl
  done

private theorem control_writing (s : SramState.State) (i : Values Reactive.Input) :
    (Sram.control SharedBranches.writing).eval (s.inputs i) s.registers =
      Reactive.writing.eval (effectiveInputs s i) (effectiveState s i) := by
  rw [SramExecution.control_correct, SharedBranches.writing, SharedBranches.adapt_correct,
    SramExecution.control_expand, ← SramExecution.mappedInput_same, SramExecution.base_inputs]
  rw [writing_words]
  unfold effectiveState
  rw [writing_words]
  rfl
  done

private theorem resetting_state (i : Values Reactive.Input)
    (r t : Values Reactive.Register) : Reactive.resetting.eval i r = Reactive.resetting.eval i t := by
  rfl
  done

private theorem control_resetting (s : SramState.State) (i : Values Reactive.Input) :
    (Sram.control SharedBranches.resetting).eval (s.inputs i) s.registers =
      Reactive.resetting.eval i s.core := by
  rw [SramExecution.control_correct, SharedBranches.resetting, SharedBranches.raw_correct,
    SramExecution.control_expand, SramExecution.base_inputs]
  apply resetting_state
  done

theorem execution_sram_controls (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (busy : Reactive.busy.eval i s.core = 1) (retained : s.core .retained = 0) :
    (Sram.control SharedBranches.resetting).eval (s.inputs i) s.registers = 0 ∧
    (Sram.control SharedBranches.writing).eval (s.inputs i) s.registers = 0 ∧
    Sram.rowWriting.eval (s.inputs i) s.registers = 0 ∧
    Sram.tableWriting.eval (s.inputs i) s.registers = 0 ∧
    Sram.committing.eval (s.inputs i) s.registers = 0 := by
  have mappedWarm : effectiveInputs s i .command ≠ 7#3 := by
    intro same
    exact warm ((effective_command_nonloader s i 7 (by decide) (by decide) (by decide)).mp same)
  have controls := execution_controls (effectiveInputs s i) (effectiveState s i)
    cold mappedWarm busy retained
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [control_resetting]
    exact (execution_controls i s.core cold warm busy retained).resetting
  · rw [control_writing]
    exact controls.writing
  · simp only [Sram.rowWriting, SramExecution.control_correct, SharedBranches.rowWriting,
      SharedBranches.both, Expr.eval]
    rw [← SramExecution.control_correct, control_writing, controls.writing]
    simp
  · simp only [Sram.tableWriting, SramExecution.control_correct, SharedBranches.tableWriting,
      SharedBranches.both, Expr.eval]
    rw [← SramExecution.control_correct, control_writing, controls.writing]
    simp
  · rw [committing_effective]
    exact controls.committing
  done

private theorem array_state_ext (a b : Memory.Sram.State 6 64)
    (contents : a.contents = b.contents) (q : a.q = b.q) : a = b := by
  cases a
  cases b
  simp_all
  done

/-- Rejected administrative delivery is a real execution clock. This is full
actual SRAM product-state equality, including both newly requested Q values;
it does not equate the delivery edge's rejection/status observations. -/
theorem execution_clock (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (busy : Reactive.busy.eval i s.core = 1) (retained : s.core .retained = 0) :
    s.step i = s.step (quiet i) := by
  rcases execution_sram_controls s i cold warm busy retained with ⟨hr, hw, hrow, htable, hc⟩
  rcases execution_sram_controls s (quiet i) rfl (by simp [quiet]) busy retained with
    ⟨qr, qw, qrow, qtable, qc⟩
  have masks := SramCoverage.masks_hold (s.inputs i) s.registers hr hw
  have qmasks := SramCoverage.masks_hold (s.inputs (quiet i)) s.registers qr qw
  have scalar {w : Nat} (register : Reactive.Register w) (scalar : Scalar register) :
      Sram.circuit.step (s.inputs i) s.registers (.core register) =
        Sram.circuit.step (s.inputs (quiet i)) s.registers (.core register) :=
    execution_scalar_clock s i cold warm busy retained register scalar
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
    apply array_state_ext
    · rw [Sram.array_read_preserves_bank _ _ _ hrow port,
        Sram.array_read_preserves_bank _ _ _ qrow port]
    · rw [Sram.array_response_read _ _ _ hrow port, Sram.array_response_read _ _ _ qrow port, address]
  unfold SramState.State.step
  rw [registers, arrays]
  done

theorem quiet_executing (i : Values Reactive.Input) : SramExecution.ExecutingInput (quiet i) := by
  simp [SramExecution.ExecutingInput, SharedBranches.Runtime, quiet]
  done

theorem execution_resident (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (busy : Reactive.busy.eval i s.core = 1) (retained : s.core .retained = 0)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (resident : SramExecution.Resident s rows dictionary) :
    SramExecution.Resident (s.step i) rows dictionary := by
  rw [execution_clock s i cold warm busy retained]
  exact SramExecution.resident_executing s (quiet i) rows dictionary (quiet_executing i) resident
  done

theorem execution_ready (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (busy : Reactive.busy.eval i s.core = 1) (retained : s.core .retained = 0)
    (rows : Memory.Contents 6 92) (dictionary : Memory.Contents 4 56)
    (resident : SramExecution.Resident s rows dictionary) :
    SramExecution.Ready (s.step i) rows := by
  rw [execution_clock s i cold warm busy retained]
  exact SramExecution.ready_executing s (quiet i) rows dictionary (quiet_executing i) resident
  done

theorem execution_rejection (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3) (nonzero : i .command ≠ 0#3)
    (busy : Reactive.busy.eval i s.core = 1) (retained : s.core .retained = 0) :
    s.observe i .rejected = 1 := by
  rw [observe_effective]
  have mappedWarm : effectiveInputs s i .command ≠ 7#3 := by
    intro same
    exact warm ((effective_command_nonloader s i 7 (by decide) (by decide) (by decide)).mp same)
  have mappedZero : effectiveInputs s i .command ≠ 0#3 := by
    intro same
    exact nonzero ((effective_command_nonloader s i 0 (by decide) (by decide) (by decide)).mp same)
  rcases busy_controls (effectiveInputs s i) (effectiveState s i) cold mappedWarm busy retained with
    ⟨hr, _, hs, hc, hw, hl⟩
  simp [Circuit.observe, Reactive.circuit, Reactive.rejected, Reactive.cmd,
    Reactive.both, Reactive.either, Expr.eval, hr, hs, hc, hw, hl, mappedZero]
  done

end Pinwheel.Hardware.Buffered.Lifecycle
