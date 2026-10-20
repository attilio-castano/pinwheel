import Pinwheel.Hardware.Buffered.GenericUploadProgress

namespace Pinwheel.Hardware.Buffered.GenericUpload.Serial
open Pinwheel.Hardware Pinwheel.Program
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}

private theorem no_row (s : SramState.State) (i : Values Reactive.Input)
    (command : i .command ≠ 1#3) : SramLoading.rowAccepted s i = false := by
  simp [SramLoading.rowAccepted,Sram.rowWriting,SramCoverage.control_correct,
    SharedBranches.rowWriting,SharedBranches.both,SharedBranches.cmd,Expr.eval,
    SramCoverage.baseInput,SramState.State.inputs,command]

private theorem no_table (s : SramState.State) (i : Values Reactive.Input)
    (command : i .command ≠ 6#3) : SramLoading.tableAccepted s i = false := by
  simp [SramLoading.tableAccepted,Sram.tableWriting,SramCoverage.control_correct,
    SharedBranches.tableWriting,SharedBranches.both,SharedBranches.cmd,Expr.eval,
    SramCoverage.baseInput,SramState.State.inputs,command]

theorem Table.source {image : Image p layout} (s : SramState.State) (h : Table image i k) :
    SourceInput image s i := by
  refine ⟨?_,?_,?_⟩
  · simp [no_row s i (by simp [h.command])]
  · intro _
    rw [h.branch,h.address,BitVec.extractLsb'_append_eq_right]
  · intro accepted
    have command := SramCoverage.commit_command (s.inputs i) s.registers accepted
    change i .command = 2 at command
    rw [h.command] at command
    contradiction

theorem Row.source {image : Image p layout} (s : SramState.State) (h : Row image i k) :
    SourceInput image s i := by
  refine ⟨?_,?_,?_⟩
  · intro _
    rw [h.address,h.word,h.control,h.branch,BitVec.extractLsb'_append_eq_right]
    exact ⟨rfl,rfl,rfl⟩
  · simp [no_table s i (by simp [h.command])]
  · intro accepted
    have command := SramCoverage.commit_command (s.inputs i) s.registers accepted
    change i .command = 2 at command
    rw [h.command] at command
    contradiction

theorem Commit.source (image : Image p layout) (s : SramState.State) (h : Commit p layout i) :
    SourceInput image s i := by
  refine ⟨?_,?_,fun _ => ⟨h.count,h.span,h.levels,h.enabled⟩⟩
  · simp [no_row s i (by simp [h.command])]
  · simp [no_table s i (by simp [h.command])]

theorem quiet_source (image : Image p layout) (s : SramState.State) (i : Values Reactive.Input)
    (quiet : Serial.Frames.Quiet i) : SourceInput image s i := by
  refine ⟨?_,?_,?_⟩
  · simp [no_row s i (by simp [quiet.2])]
  · simp [no_table s i (by simp [quiet.2])]
  · intro accepted
    have command := SramCoverage.commit_command (s.inputs i) s.registers accepted
    change i .command = 2 at command
    exact False.elim ((by decide : (0#3 : BitVec 3) ≠ 2) (quiet.2.symm.trans command))

theorem quiet_history (image : Image p layout) (s : SramState.State)
    (inputs : List (Values Reactive.Input)) (quiet : ∀ i ∈ inputs, Serial.Frames.Quiet i) :
    SourceHistory image s inputs := by
  induction inputs generalizing s with
  | nil => trivial
  | cons i rest ih => exact ⟨quiet_source image s i (quiet i (by simp)),
      ih (s.step i) (fun j member => quiet j (List.mem_cons_of_mem _ member))⟩

theorem history_append (image : Image p layout) (s : SramState.State)
    (first rest : List (Values Reactive.Input))
    (head : SourceHistory image s first) (tail : SourceHistory image (s.run first) rest) :
    SourceHistory image s (first ++ rest) := by
  induction first generalizing s with
  | nil => exact tail
  | cons i more ih => exact ⟨head.1,ih (s.step i) head.2 tail⟩

end Pinwheel.Hardware.Buffered.GenericUpload.Serial
