import Pinwheel.Hardware.Buffered.GenericUploadControl

namespace Pinwheel.Hardware.Buffered.GenericUpload.Serial
open Pinwheel.Hardware Pinwheel.Program I2cCanonicalUpload
open _root_.Pinwheel.Hardware.Buffered.SerialUpload (TableProgress RowProgress Complete)
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private theorem writing_idle (s : SramState.State) (i : Values Reactive.Input)
    (cold : i .initialize = 0) (phase : s.core .phase = 0) (retained : s.core .retained = 0)
    (command : SharedBranches.mappedInput i (SramCoverage.controlState s.registers) .command = 1) :
    SramCoverage.writing.eval (s.inputs i) s.registers = 1 := by
  rw [SramCoverage.writing,SramCoverage.control_correct,SharedBranches.writing,SharedBranches.adapt_correct]
  have mcold : SharedBranches.mappedInput (SramCoverage.baseInput (s.inputs i))
      (SramCoverage.controlState s.registers) .initialize = 0 := cold
  have mphase : SharedBranches.expandState (SramCoverage.controlState s.registers) .phase = 0 := phase
  have mretained : SharedBranches.expandState (SramCoverage.controlState s.registers) .retained = 0 := retained
  have mcommand : SharedBranches.mappedInput (SramCoverage.baseInput (s.inputs i))
      (SramCoverage.controlState s.registers) .command = 1#3 := command
  simp [Reactive.writing,Reactive.free,Reactive.resetting,Reactive.cold,Reactive.warm,
    Reactive.cmd,Reactive.busy,Reactive.both,Reactive.either,Expr.eval,mcommand,mcold,mphase,mretained]

theorem table_writing (image : Image p layout) (s : SramState.State) (i : Values Reactive.Input)
    (k : BitVec 4) (input : Table image i k) (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    SramCoverage.writing.eval (s.inputs i) s.registers = 1 ∧ Sram.tableWriting.eval (s.inputs i) s.registers = 1 := by
  have high : (i .address).extractLsb' 4 2 = 0#2 := by rw [input.address,BitVec.extractLsb'_append_eq_left]
  have command : SharedBranches.mappedInput i (SramCoverage.controlState s.registers) .command = 1 := by
    simp [SharedBranches.mappedInput,SharedBranches.inputExpr,SharedBranches.tableShape,
      SharedBranches.cmd,SharedBranches.both,Expr.eval,input.command,high]
  have writing := writing_idle s i input.cold phase retained command
  refine ⟨writing,?_⟩
  rw [SramCoverage.writing,SramCoverage.control_correct] at writing
  simp [Sram.tableWriting,SramCoverage.control_correct,SharedBranches.tableWriting,
    SharedBranches.both,SharedBranches.cmd,Expr.eval,SramCoverage.baseInput,SramState.State.inputs,input.command,writing]

theorem row_writing (image : Image p layout) (s : SramState.State) (i : Values Reactive.Input)
    (k : BitVec 6) (input : Row image i k) (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    SramCoverage.writing.eval (s.inputs i) s.registers = 1 ∧ Sram.rowWriting.eval (s.inputs i) s.registers = 1 := by
  have high : (i .branch).extractLsb' 4 52 = 0#52 := by rw [input.branch,BitVec.extractLsb'_append_eq_left]
  have command : SharedBranches.mappedInput i (SramCoverage.controlState s.registers) .command = 1 := by
    simp [SharedBranches.mappedInput,SharedBranches.inputExpr,SharedBranches.rowShape,
      SharedBranches.cmd,SharedBranches.both,Expr.eval,input.command,high]
  have writing := writing_idle s i input.cold phase retained command
  refine ⟨writing,?_⟩
  rw [SramCoverage.writing,SramCoverage.control_correct] at writing
  simp [Sram.rowWriting,SramCoverage.control_correct,SharedBranches.rowWriting,
    SharedBranches.both,SharedBranches.cmd,Expr.eval,SramCoverage.baseInput,SramState.State.inputs,input.command,writing]

theorem table_write (image : Image p layout) {generation n s} (h : TableProgress generation n s)
    (i : Values Reactive.Input) (input : Table image i (BitVec.ofNat 4 n)) :
    TableProgress generation (n+1) (s.step i) := by
  have loader : LifecycleUpload.Input i := ⟨input.cold,by simp [input.command],by simp [input.command]⟩
  have reset := reset_zero s i input.cold loader.warm
  have writing := table_writing image s i _ input h.phase h.retained
  have commit := no_commit s i (by simp [input.command])
  have idle := LifecycleUpload.idle_step s i loader h.phase h.retained
  refine ⟨idle.1,idle.2,fun _ => write_pending s i reset writing.1 commit,?_,
    (no_commit_generation s i input.cold loader.warm commit).trans h.generation⟩
  intro k within
  by_cases same : k.val = n
  · apply table_here s i reset writing.1 writing.2 k
    rw [input.address,BitVec.extractLsb'_append_eq_right,same]
  · exact table_keep s i reset writing.1 (h.pending (by omega)) k (h.dictionary k (by omega))

theorem row_write (image : Image p layout) {generation n s} (h : RowProgress generation n s)
    (i : Values Reactive.Input) (input : Row image i (BitVec.ofNat 6 n)) :
    RowProgress generation (n+1) (s.step i) := by
  have loader : LifecycleUpload.Input i := ⟨input.cold,by simp [input.command],by simp [input.command]⟩
  have reset := reset_zero s i input.cold loader.warm
  have writing := row_writing image s i _ input h.phase h.retained
  have commit := no_commit s i (by simp [input.command])
  have idle := LifecycleUpload.idle_step s i loader h.phase h.retained
  refine ⟨idle.1,idle.2,write_pending s i reset writing.1 commit,
    fun k => table_keep s i reset writing.1 h.pending k (h.dictionary k),?_,
    (no_commit_generation s i input.cold loader.warm commit).trans h.generation⟩
  intro k within
  by_cases same : k.val = n
  · exact written_here s i reset writing.1 writing.2 k (input.address.trans (by rw [same]))
  · exact written_keep s i reset writing.1 h.pending k (h.covered k (by omega))

theorem commit_progress {generation s} (h : RowProgress generation layout.count.val s)
    (i : Values Reactive.Input) (input : Commit p layout i) (space : generation ≠ 65535) :
    Complete generation (s.step i) := by
  have loader : LifecycleUpload.Input i := ⟨input.cold,by simp [input.command],by simp [input.command]⟩
  have reset := reset_zero s i input.cold loader.warm
  have accepted := commit_accepted s i input h.phase h.retained h.pending
    (by rw [h.generation]; exact space) h.covered (dictionary_full s h.dictionary)
  have noWriting := SramCoverage.commit_no_writing (s.inputs i) s.registers accepted
  change SramCoverage.writing.eval (s.inputs i) s.registers = 0#1 at noWriting
  have idle := LifecycleUpload.idle_step s i loader h.phase h.retained
  refine ⟨idle.1,idle.2,?_,?_⟩
  · change Sram.circuit.step (s.inputs i) s.registers (.core .valid) = 1
    rw [SramCoverage.valid_step]
    simp [reset,noWriting,accepted]
  · rw [Lifecycle.commit_generation_sequence s i accepted,h.generation]

end Pinwheel.Hardware.Buffered.GenericUpload.Serial
