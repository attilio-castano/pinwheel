import Pinwheel.Hardware.Buffered.I2cUploadAdequacy
import Pinwheel.Hardware.Buffered.SerialCorrespondenceEncoding
import Pinwheel.Hardware.Buffered.SerialPackageRead

/-! Loader operands decoded from the wire may carry unrelated live fields.
These acceptance facts constrain only fields read by the actual loader. -/
namespace Pinwheel.Hardware.Buffered.SerialUpload
open Pinwheel.Hardware I2cCanonicalUpload
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Table (i : Values Reactive.Input) (k : BitVec 4) : Prop where
  cold : i .initialize = 0
  command : i .command = 6
  address : i .address = 0#2 ++ k
  branch : i .branch = I2cSource.dictionary k

structure Row (i : Values Reactive.Input) (k : BitVec 6) : Prop where
  cold : i .initialize = 0
  command : i .command = 1
  address : i .address = k
  word : i .word = I2cSource.word k
  control : i .control = I2cSource.control k
  branch : i .branch = 0#52 ++ I2cSource.branchIndex k

structure Commit (i : Values Reactive.Input) : Prop where
  cold : i .initialize = 0
  command : i .command = 2
  count : i .count = 50
  span : i .virtualSpan = 270
  levels : i .idleLevels = 0
  enabled : i .idleEnabled = 0

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

theorem row_writing (s : SramState.State) (i : Values Reactive.Input) (k : BitVec 6)
    (input : Row i k) (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    SramCoverage.writing.eval (s.inputs i) s.registers = 1 ∧
    Sram.rowWriting.eval (s.inputs i) s.registers = 1 := by
  have high : (i .branch).extractLsb' 4 52 = 0#52 := by
    rw [input.branch, BitVec.extractLsb'_append_eq_left]
  have command : SharedBranches.mappedInput i (SramCoverage.controlState s.registers) .command = 1 := by
    simp [SharedBranches.mappedInput, SharedBranches.inputExpr, SharedBranches.rowShape,
      SharedBranches.cmd, SharedBranches.both, Expr.eval, input.command, high]
  have writing := writing_idle s i input.cold phase retained command
  refine ⟨writing, ?_⟩
  rw [SramCoverage.writing, SramCoverage.control_correct] at writing
  simp [Sram.rowWriting, SramCoverage.control_correct, SharedBranches.rowWriting,
    SharedBranches.both, SharedBranches.cmd, Expr.eval, SramCoverage.baseInput,
    SramState.State.inputs, input.command, writing]
  done

theorem table_writing (s : SramState.State) (i : Values Reactive.Input) (k : BitVec 4)
    (input : Table i k) (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    SramCoverage.writing.eval (s.inputs i) s.registers = 1 ∧
    Sram.tableWriting.eval (s.inputs i) s.registers = 1 := by
  have high : (i .address).extractLsb' 4 2 = 0#2 := by
    rw [input.address, BitVec.extractLsb'_append_eq_left]
  have command : SharedBranches.mappedInput i (SramCoverage.controlState s.registers) .command = 1 := by
    simp [SharedBranches.mappedInput, SharedBranches.inputExpr, SharedBranches.tableShape,
      SharedBranches.cmd, SharedBranches.both, Expr.eval, input.command, high]
  have writing := writing_idle s i input.cold phase retained command
  refine ⟨writing, ?_⟩
  rw [SramCoverage.writing, SramCoverage.control_correct] at writing
  simp [Sram.tableWriting, SramCoverage.control_correct, SharedBranches.tableWriting,
    SharedBranches.both, SharedBranches.cmd, Expr.eval, SramCoverage.baseInput,
    SramState.State.inputs, input.command, writing]
  done

theorem commit_accepted (s : SramState.State) (i : Values Reactive.Input) (input : Commit i)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (pending : s.core .pending = 1) (space : s.core .generation ≠ 65535)
    (covered : ∀ k : Fin 64, k.val < 50 → (s.core .written).getLsbD k.val = true)
    (dictionary : s.registers .branchWritten = 65535) :
    Sram.committing.eval (s.inputs i) s.registers = 1 := by
  rw [Lifecycle.committing_effective]
  have command : Lifecycle.effectiveInputs s i .command = 2#3 := by
    simp [Lifecycle.effectiveInputs, SharedBranches.mappedInput, SharedBranches.inputExpr,
      SharedBranches.cmd, SharedBranches.tableCovered, SharedBranches.both, Expr.eval,
      SramExecution.selectedShared, Sram.registerExpr, input.command, dictionary]
  have free : Reactive.free.eval (Lifecycle.effectiveInputs s i)
      (Lifecycle.effectiveState s i) = 1 := by
    simp [Reactive.free, Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.cmd,
      Reactive.busy, Reactive.both, Reactive.either, Expr.eval, command,
      show Lifecycle.effectiveInputs s i .initialize = 0 from input.cold,
      show Lifecycle.effectiveState s i .phase = 0 from phase,
      show Lifecycle.effectiveState s i .retained = 0 from retained]
  have coverage := covered_prefix (Lifecycle.effectiveInputs s i)
    (Lifecycle.effectiveState s i) input.count covered
  simp [Reactive.committing, Reactive.countValid, Reactive.spanValid, Reactive.space,
    Reactive.both, Reactive.cmd, Expr.eval, free, command, coverage,
    show Lifecycle.effectiveState s i .pending = 1 from pending,
    show Lifecycle.effectiveState s i .generation ≠ 65535#16 from space,
    show Lifecycle.effectiveInputs s i .count = 50 from input.count,
    show Lifecycle.effectiveInputs s i .virtualSpan = 270 from input.span]
  done

private theorem no_row (s : SramState.State) (i : Values Reactive.Input)
    (command : i .command ≠ 1#3) : SramLoading.rowAccepted s i = false := by
  simp [SramLoading.rowAccepted, Sram.rowWriting, SramCoverage.control_correct,
    SharedBranches.rowWriting, SharedBranches.both, SharedBranches.cmd, Expr.eval,
    SramCoverage.baseInput, SramState.State.inputs, command]
  done

private theorem no_table (s : SramState.State) (i : Values Reactive.Input)
    (command : i .command ≠ 6#3) : SramLoading.tableAccepted s i = false := by
  simp [SramLoading.tableAccepted, Sram.tableWriting, SramCoverage.control_correct,
    SharedBranches.tableWriting, SharedBranches.both, SharedBranches.cmd, Expr.eval,
    SramCoverage.baseInput, SramState.State.inputs, command]
  done

theorem Table.source (s : SramState.State) (h : Table i k) : I2cLoading.SourceInput s i := by
  refine ⟨?_, ?_, ?_⟩
  · simp [no_row s i (by simp [h.command])]
  · intro _
    rw [h.branch, h.address, BitVec.extractLsb'_append_eq_right]
  · intro accepted
    have command := SramCoverage.commit_command (s.inputs i) s.registers accepted
    change i .command = 2 at command
    rw [h.command] at command
    contradiction
  done

theorem Row.source (s : SramState.State) (h : Row i k) : I2cLoading.SourceInput s i := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    rw [h.address, h.word, h.control, h.branch, BitVec.extractLsb'_append_eq_right]
    exact ⟨rfl, rfl, rfl⟩
  · simp [no_table s i (by simp [h.command])]
  · intro accepted
    have command := SramCoverage.commit_command (s.inputs i) s.registers accepted
    change i .command = 2 at command
    rw [h.command] at command
    contradiction
  done

theorem Commit.source (s : SramState.State) (h : Commit i) : I2cLoading.SourceInput s i := by
  refine ⟨?_, ?_, fun _ => ⟨h.count, h.span, h.levels, h.enabled⟩⟩
  · simp [no_row s i (by simp [h.command])]
  · simp [no_table s i (by simp [h.command])]
  done

theorem quiet_source (s : SramState.State) (i : Values Reactive.Input)
    (quiet : Serial.Frames.Quiet i) : I2cLoading.SourceInput s i := by
  refine ⟨?_, ?_, ?_⟩
  · simp [no_row s i (by simp [quiet.2])]
  · simp [no_table s i (by simp [quiet.2])]
  · intro accepted
    have command := SramCoverage.commit_command (s.inputs i) s.registers accepted
    change i .command = 2 at command
    exact False.elim ((by decide : (0#3 : BitVec 3) ≠ 2) (quiet.2.symm.trans command))
  done

theorem quiet_writing (s : SramState.State) (i : Values Reactive.Input)
    (quiet : Serial.Frames.Quiet i) : SramCoverage.writing.eval (s.inputs i) s.registers = 0 := by
  rw [writing_effective]
  have command : Lifecycle.effectiveInputs s i .command = 0#3 :=
    (Lifecycle.effective_command_nonloader s i 0 (by decide) (by decide) (by decide)).2 quiet.2
  simp [Reactive.writing, Reactive.both, Reactive.cmd, Expr.eval, command]
  done

structure Hold (before after : SramState.State) : Prop where
  pending : after.core .pending = before.core .pending
  written : after.core .written = before.core .written
  dictionary : after.registers .branchWritten = before.registers .branchWritten
  generation : after.core .generation = before.core .generation
  valid : after.core .valid = before.core .valid

theorem quiet_hold (s : SramState.State) (i : Values Reactive.Input)
    (quiet : Serial.Frames.Quiet i) : Hold s (s.step i) := by
  have reset := reset_zero s i quiet.1 (by simp [quiet.2])
  have writing := quiet_writing s i quiet
  have commit := no_commit s i (by simp [quiet.2])
  have masks := SramCoverage.masks_hold (s.inputs i) s.registers reset writing
  refine ⟨?_, masks.1, masks.2, no_commit_generation s i quiet.1 (by simp [quiet.2]) commit, ?_⟩
  · rw [Lifecycle.scalar_step s i .pending trivial]
    change (if Reactive.resetting.eval (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) = 1 then 0
      else if Reactive.committing.eval (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) = 1 then 0
      else if Reactive.writing.eval (Lifecycle.effectiveInputs s i) (Lifecycle.effectiveState s i) = 1 then 1
      else Lifecycle.effectiveState s i .pending) = s.core .pending
    rw [← Lifecycle.committing_effective, ← writing_effective, Lifecycle.resetting_effective]
    have coldReset : Reactive.resetting.eval i s.core = 0 := by
      simp [Reactive.resetting, Reactive.cold, Reactive.warm, Reactive.cmd,
        Reactive.both, Reactive.either, Expr.eval, quiet.1, quiet.2]
    simp [coldReset, writing, commit, Lifecycle.effectiveState, SramExecution.withWords]
  · change Sram.circuit.step (s.inputs i) s.registers (.core .valid) = s.registers (.core .valid)
    rw [SramCoverage.valid_step]
    simp [reset, writing, commit]
  done

theorem Hold.trans {a b c : SramState.State} (first : Hold a b) (second : Hold b c) : Hold a c :=
  ⟨second.pending.trans first.pending, second.written.trans first.written,
    second.dictionary.trans first.dictionary, second.generation.trans first.generation,
    second.valid.trans first.valid⟩

theorem quiet_run_hold (s : SramState.State) (inputs : List (Values Reactive.Input))
    (quiet : ∀ i ∈ inputs, Serial.Frames.Quiet i) : Hold s (s.run inputs) := by
  induction inputs generalizing s
  case nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  case cons i rest ih =>
    exact (quiet_hold s i (quiet i (by simp))).trans
      (ih (s.step i) (fun j member => quiet j (List.mem_cons_of_mem _ member)))
  done

theorem quiet_history (s : SramState.State) (inputs : List (Values Reactive.Input))
    (quiet : ∀ i ∈ inputs, Serial.Frames.Quiet i) : I2cLoading.SourceHistory s inputs := by
  induction inputs generalizing s
  case nil => trivial
  case cons i rest ih =>
    exact ⟨quiet_source s i (quiet i (by simp)),
      ih (s.step i) (fun j member => quiet j (List.mem_cons_of_mem _ member))⟩
  done

theorem history_append (s : SramState.State) (a b : List (Values Reactive.Input))
    (first : I2cLoading.SourceHistory s a) (second : I2cLoading.SourceHistory (s.run a) b) :
    I2cLoading.SourceHistory s (a ++ b) := by
  induction a generalizing s
  case nil => exact second
  case cons i rest ih => exact ⟨first.1, ih (s.step i) first.2 second⟩
  done

theorem quiet_run_idle (s : SramState.State) (inputs : List (Values Reactive.Input))
    (quiet : ∀ i ∈ inputs, Serial.Frames.Quiet i)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    (s.run inputs).core .phase = 0 ∧ (s.run inputs).core .retained = 0 := by
  apply And.intro ((LifecycleUpload.run s inputs ?_ phase retained).1)
    ((LifecycleUpload.run s inputs ?_ phase retained).2.1)
  all_goals intro i member
  all_goals exact ⟨(quiet i member).1, by simp [(quiet i member).2], by simp [(quiet i member).2]⟩
  done

end Pinwheel.Hardware.Buffered.SerialUpload
