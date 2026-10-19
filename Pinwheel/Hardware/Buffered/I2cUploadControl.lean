import Pinwheel.Hardware.Buffered.I2cCanonicalUpload

/-! Forward acceptance and coverage effects of the actual SRAM loader. These
facts use only idle ownership/control fields; SRAM contents and Q stay arbitrary. -/
namespace Pinwheel.Hardware.Buffered.I2cCanonicalUpload
open Pinwheel.Hardware
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private theorem writing_words (i : Values Reactive.Input) (r : Values Reactive.Register)
    (words : Memory.Contents 6 144) :
    Reactive.writing.eval i (SramExecution.withWords r words) = Reactive.writing.eval i r := rfl

theorem writing_effective (s : SramState.State) (i : Values Reactive.Input) :
    SramCoverage.writing.eval (s.inputs i) s.registers =
      Reactive.writing.eval (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) := by
  rw [SramCoverage.writing, SramExecution.control_correct, SharedBranches.writing,
    SharedBranches.adapt_correct, SramExecution.control_expand,
    ← SramExecution.mappedInput_same, SramExecution.base_inputs, writing_words]
  unfold Lifecycle.effectiveState
  rw [writing_words]
  rfl
  done

theorem reset_zero (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (warm : i .command ≠ 7#3) :
    SramCoverage.resetting.eval (s.inputs i) s.registers = 0 := by
  simp [SramCoverage.resetting, SramCoverage.control_correct, SharedBranches.resetting,
    SharedBranches.raw_correct, Reactive.resetting, Reactive.cold, Reactive.warm,
    Reactive.cmd, Reactive.both, Reactive.either, Expr.eval,
    SramCoverage.baseInput, SramState.State.inputs, cold, warm]
  done

private theorem writing_idle (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (command : SharedBranches.mappedInput i (SramCoverage.controlState s.registers) .command = 1) :
    SramCoverage.writing.eval (s.inputs i) s.registers = 1 := by
  rw [SramCoverage.writing, SramCoverage.control_correct, SharedBranches.writing,
    SharedBranches.adapt_correct]
  have mcold : SharedBranches.mappedInput (SramCoverage.baseInput (s.inputs i))
      (SramCoverage.controlState s.registers) .initialize = 0 := cold
  have mphase : SharedBranches.expandState (SramCoverage.controlState s.registers) .phase = 0 := phase
  have mretained : SharedBranches.expandState (SramCoverage.controlState s.registers) .retained = 0 := retained
  have mcommand : SharedBranches.mappedInput (SramCoverage.baseInput (s.inputs i))
      (SramCoverage.controlState s.registers) .command = 1#3 := command
  simp [Reactive.writing, Reactive.free, Reactive.resetting, Reactive.cold, Reactive.warm,
    Reactive.cmd, Reactive.busy, Reactive.both, Reactive.either, Expr.eval,
    mcommand, mcold, mphase, mretained]
  done

private theorem mapped_row (s : SramState.State) (k : BitVec 6) :
    SharedBranches.mappedInput (rowInput k) (SramCoverage.controlState s.registers) .command = 1 := by
  have high : (0#52 ++ I2cSource.branchIndex k).extractLsb' 4 52 = 0#52 := BitVec.extractLsb'_append_eq_left
  simp [SharedBranches.mappedInput, SharedBranches.inputExpr, SharedBranches.rowShape,
    SharedBranches.cmd, SharedBranches.both, Expr.eval, rowInput, high]
  done

private theorem mapped_table (s : SramState.State) (k : BitVec 4) :
    SharedBranches.mappedInput (tableInput k) (SramCoverage.controlState s.registers) .command = 1 := by
  have high : (0#2 ++ k).extractLsb' 4 2 = 0#2 := BitVec.extractLsb'_append_eq_left
  simp [SharedBranches.mappedInput, SharedBranches.inputExpr, SharedBranches.tableShape,
    SharedBranches.cmd, SharedBranches.both, Expr.eval, tableInput, high]
  done

theorem row_writing (s : SramState.State) (k : BitVec 6)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    SramCoverage.writing.eval (s.inputs (rowInput k)) s.registers = 1 ∧
    Sram.rowWriting.eval (s.inputs (rowInput k)) s.registers = 1 := by
  have writing := writing_idle s (rowInput k) rfl phase retained (mapped_row s k)
  refine ⟨writing, ?_⟩
  rw [SramCoverage.writing, SramCoverage.control_correct] at writing
  simp [Sram.rowWriting, SramCoverage.control_correct, SharedBranches.rowWriting,
    SharedBranches.both, SharedBranches.cmd, Expr.eval, SramCoverage.baseInput,
    SramState.State.inputs, rowInput, writing]
  done

theorem table_writing (s : SramState.State) (k : BitVec 4)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    SramCoverage.writing.eval (s.inputs (tableInput k)) s.registers = 1 ∧
    Sram.tableWriting.eval (s.inputs (tableInput k)) s.registers = 1 := by
  have writing := writing_idle s (tableInput k) rfl phase retained (mapped_table s k)
  refine ⟨writing, ?_⟩
  rw [SramCoverage.writing, SramCoverage.control_correct] at writing
  simp [Sram.tableWriting, SramCoverage.control_correct, SharedBranches.tableWriting,
    SharedBranches.both, SharedBranches.cmd, Expr.eval, SramCoverage.baseInput,
    SramState.State.inputs, tableInput, writing]
  done

theorem no_commit (s : SramState.State) (i : Values Reactive.Input) (notCommit : i .command ≠ 2#3) :
    Sram.committing.eval (s.inputs i) s.registers = 0 := by
  apply (BitVec.eq_zero_or_eq_one _).resolve_right
  intro accepted
  exact notCommit (SramCoverage.commit_command (s.inputs i) s.registers accepted)
  done

theorem write_pending (s : SramState.State) (i : Values Reactive.Input)
    (reset : SramCoverage.resetting.eval (s.inputs i) s.registers = 0)
    (writing : SramCoverage.writing.eval (s.inputs i) s.registers = 1)
    (commit : Sram.committing.eval (s.inputs i) s.registers = 0) :
    (s.step i).core .pending = 1 := by
  rw [Lifecycle.scalar_step s i .pending trivial]
  change (if Reactive.resetting.eval (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) = 1 then 0
    else if Reactive.committing.eval (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) = 1 then 0
    else if Reactive.writing.eval (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) = 1 then 1
    else Lifecycle.effectiveState s i .pending) = 1
  rw [← Lifecycle.committing_effective, ← writing_effective, Lifecycle.resetting_effective]
  have hr : Reactive.resetting.eval i s.core = 0 := by
    simpa only [SramCoverage.resetting, SramCoverage.control_correct,
      SharedBranches.resetting, SharedBranches.raw_correct, Reactive.resetting,
      Reactive.cold, Reactive.warm, Reactive.cmd, Reactive.both, Reactive.either,
      Expr.eval, SramCoverage.baseInput, SramState.State.inputs] using reset
  simp [hr, writing, commit]
  done

end Pinwheel.Hardware.Buffered.I2cCanonicalUpload
