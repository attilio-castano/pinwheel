import Pinwheel.Hardware.Buffered.GenericUploadEncoding

namespace Pinwheel.Hardware.Buffered.GenericUpload.Serial
open Pinwheel.Hardware Pinwheel.Program SerialWire
open _root_.Pinwheel.Hardware.Buffered.SerialUpload (TableProgress RowProgress Complete)
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem transaction_history (image : Image p layout) {before : SerialPackage.State} (transaction : Transaction before)
    (source : SourceInput image transaction.framed.controller
      (transaction.framed.coreInputs transaction.dispatch)) :
    SourceHistory image before.controller (before.commands transaction.pins) := by
  rw [Buffered.SerialUpload.transaction_commands]
  apply history_append image before.controller
  · exact quiet_history image _ _ transaction.request.quiet
  · rw [← before.run_controller]
    exact ⟨source, quiet_source image _ _ transaction.capture_quiet,
      quiet_history image _ _ transaction.read_quiet⟩
  done

theorem table_transaction (image : Image p layout) {before : SerialPackage.State} (transaction : Transaction before)
    (sequence : BitVec 16) (n : Nat)
    (word : transaction.request.word = tableWord image sequence (BitVec.ofNat 4 n))
    {generation : BitVec 16} (progress : TableProgress generation n before.controller) :
    TableProgress generation (n+1) transaction.after.controller ∧
      SourceHistory image before.controller (before.commands transaction.pins) ∧
      (∀ i ∈ before.commands transaction.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available transaction.after.record := by
  have closed := transaction.request.closed
  rw [word] at closed
  have input := table_operands image transaction.framed transaction.dispatch sequence _ closed transaction.dispatchIdle.1
  refine ⟨?_, transaction_history image transaction (input.source _),
    Buffered.SerialUpload.transaction_loader transaction ⟨input.cold, by simp [input.command], by simp [input.command]⟩,
    transaction.exact.1⟩
  exact Buffered.SerialUpload.transaction_invariant transaction (TableProgress generation n) (TableProgress generation (n+1))
    progress (fun _ i h quiet => h.quiet i quiet) (fun h => table_write image h _ input)
    (fun _ i h quiet => h.quiet i quiet)
  done

theorem row_transaction (image : Image p layout) {before : SerialPackage.State} (transaction : Transaction before)
    (sequence : BitVec 16) (n : Nat)
    (word : transaction.request.word = rowWord image sequence (BitVec.ofNat 6 n))
    {generation : BitVec 16} (progress : RowProgress generation n before.controller) :
    RowProgress generation (n+1) transaction.after.controller ∧
      SourceHistory image before.controller (before.commands transaction.pins) ∧
      (∀ i ∈ before.commands transaction.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available transaction.after.record := by
  have closed := transaction.request.closed
  rw [word] at closed
  have input := row_operands image transaction.framed transaction.dispatch sequence _ closed transaction.dispatchIdle.1
  refine ⟨?_, transaction_history image transaction (input.source _),
    Buffered.SerialUpload.transaction_loader transaction ⟨input.cold, by simp [input.command], by simp [input.command]⟩,
    transaction.exact.1⟩
  exact Buffered.SerialUpload.transaction_invariant transaction (RowProgress generation n) (RowProgress generation (n+1))
    progress (fun _ i h quiet => h.quiet i quiet) (fun h => row_write image h _ input)
    (fun _ i h quiet => h.quiet i quiet)
  done

theorem commit_transaction (image : Image p layout) {before : SerialPackage.State} (transaction : Transaction before)
    (sequence : BitVec 16) (word : transaction.request.word = commitWord p layout sequence)
    {generation : BitVec 16} (progress : RowProgress generation layout.count.val before.controller)
    (space : generation ≠ 65535) :
    Complete generation transaction.after.controller ∧
      SourceHistory image before.controller (before.commands transaction.pins) ∧
      (∀ i ∈ before.commands transaction.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available transaction.after.record := by
  have closed := transaction.request.closed
  rw [word] at closed
  have input := commit_operands p layout transaction.framed transaction.dispatch sequence closed transaction.dispatchIdle.1
  refine ⟨?_, transaction_history image transaction (input.source image _),
    Buffered.SerialUpload.transaction_loader transaction ⟨input.cold, by simp [input.command], by simp [input.command]⟩,
    transaction.exact.1⟩
  exact Buffered.SerialUpload.transaction_invariant transaction (RowProgress generation layout.count.val) (Complete generation)
    progress (fun _ i h quiet => h.quiet i quiet) (fun h => commit_progress h _ input space)
    (fun _ i h quiet => h.quiet i quiet)
  done

end Pinwheel.Hardware.Buffered.GenericUpload.Serial
