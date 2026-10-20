import Pinwheel.Hardware.Buffered.I2cTimingUpload
import Pinwheel.Hardware.Buffered.SerialUploadTransaction

/-! Symbolic I²C timing operands decoded from actual serial requests.  Only
instruction data vary; admission, coverage, dictionary and layout are reused. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming.SerialUpload
open Pinwheel.Hardware Serial.Frames
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

structure Row (duration budget : Fin 256) (i : Values Reactive.Input) (k : BitVec 6) : Prop where
  cold : i .initialize = 0
  command : i .command = 1
  address : i .address = k
  word : i .word = I2cTiming.word duration budget k
  control : i .control = I2cSource.control k
  branch : i .branch = 0#52 ++ I2cSource.branchIndex k

theorem row_writing (duration budget : Fin 256) (s : SramState.State)
    (i : Values Reactive.Input) (k : BitVec 6) (input : Row duration budget i k)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    SramCoverage.writing.eval (s.inputs i) s.registers = 1 ∧
      Sram.rowWriting.eval (s.inputs i) s.registers = 1 := by
  let shadow : Values Reactive.Input
    | _, .word => I2cSource.word k
    | _, port => i port
  exact Buffered.SerialUpload.row_writing s shadow k
    ⟨input.cold,input.command,input.address,rfl,input.control,input.branch⟩ phase retained

theorem Row.write {duration budget generation n s}
    (h : Buffered.SerialUpload.RowProgress generation n s)
    (i : Values Reactive.Input) (input : Row duration budget i (BitVec.ofNat 6 n)) :
    Buffered.SerialUpload.RowProgress generation (n+1) (s.step i) := by
  have loader : LifecycleUpload.Input i :=
    ⟨input.cold,by simp [input.command],by simp [input.command]⟩
  have reset := I2cCanonicalUpload.reset_zero s i input.cold loader.warm
  have writing := row_writing duration budget s i _ input h.phase h.retained
  have commit := I2cCanonicalUpload.no_commit s i (by simp [input.command])
  have idle := LifecycleUpload.idle_step s i loader h.phase h.retained
  refine ⟨idle.1,idle.2,I2cCanonicalUpload.write_pending s i reset writing.1 commit,
    fun k => I2cCanonicalUpload.table_keep s i reset writing.1 h.pending k (h.dictionary k),?_,
    (I2cCanonicalUpload.no_commit_generation s i input.cold loader.warm commit).trans h.generation⟩
  intro k within
  by_cases same : k.val = n
  · exact I2cCanonicalUpload.written_here s i reset writing.1 writing.2 k
      (input.address.trans (by rw [same]))
  · exact I2cCanonicalUpload.written_keep s i reset writing.1 h.pending k (h.covered k (by omega))

private theorem no_row (s : SramState.State) (i : Values Reactive.Input)
    (command : i .command ≠ 1#3) : SramLoading.rowAccepted s i = false := by
  simp [SramLoading.rowAccepted, Sram.rowWriting, SramCoverage.control_correct,
    SharedBranches.rowWriting, SharedBranches.both, SharedBranches.cmd, Expr.eval,
    SramCoverage.baseInput, SramState.State.inputs, command]

private theorem no_table (s : SramState.State) (i : Values Reactive.Input)
    (command : i .command ≠ 6#3) : SramLoading.tableAccepted s i = false := by
  simp [SramLoading.tableAccepted, Sram.tableWriting, SramCoverage.control_correct,
    SharedBranches.tableWriting, SharedBranches.both, SharedBranches.cmd, Expr.eval,
    SramCoverage.baseInput, SramState.State.inputs, command]

theorem Row.source {duration budget i k} (s : SramState.State)
    (input : Row duration budget i k) : Loading.SourceInput duration budget s i := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    rw [input.address,input.word,input.control,input.branch,BitVec.extractLsb'_append_eq_right]
    exact ⟨rfl,rfl,rfl⟩
  · simp [no_table s i (by simp [input.command])]
  · intro accepted
    have command := SramCoverage.commit_command (s.inputs i) s.registers accepted
    change i .command = 2 at command
    rw [input.command] at command
    contradiction

theorem nonrow_source {duration budget s i} (old : I2cLoading.SourceInput s i)
    (command : i .command ≠ 1#3) : Loading.SourceInput duration budget s i := by
  refine ⟨?_,old.table,old.commit⟩
  simp [no_row s i command]

theorem table_source (duration budget : Fin 256) (s : SramState.State)
    (input : Buffered.SerialUpload.Table i k) : Loading.SourceInput duration budget s i :=
  nonrow_source (input.source s) (by simp [input.command])

theorem commit_source (duration budget : Fin 256) (s : SramState.State)
    (input : Buffered.SerialUpload.Commit i) : Loading.SourceInput duration budget s i :=
  nonrow_source (input.source s) (by simp [input.command])

theorem quiet_source (duration budget : Fin 256) (s : SramState.State)
    (i : Values Reactive.Input) (quiet : Quiet i) : Loading.SourceInput duration budget s i :=
  nonrow_source (Buffered.SerialUpload.quiet_source s i quiet) (by simp [quiet.2])

theorem quiet_history (duration budget : Fin 256) (s : SramState.State)
    (inputs : List (Values Reactive.Input)) (quiet : ∀ i ∈ inputs, Quiet i) :
    Loading.SourceHistory duration budget s inputs := by
  induction inputs generalizing s with
  | nil => trivial
  | cons i rest ih =>
    exact ⟨quiet_source duration budget s i (quiet i (by simp)),
      ih (s.step i) (fun j member => quiet j (List.mem_cons_of_mem _ member))⟩

theorem history_append (duration budget : Fin 256) (s : SramState.State)
    (first rest : List (Values Reactive.Input))
    (head : Loading.SourceHistory duration budget s first)
    (tail : Loading.SourceHistory duration budget (s.run first) rest) :
    Loading.SourceHistory duration budget s (first ++ rest) := by
  induction first generalizing s with
  | nil => exact tail
  | cons i more ih => exact ⟨head.1,ih (s.step i) head.2 tail⟩

end Pinwheel.Hardware.Buffered.I2cTiming.SerialUpload
