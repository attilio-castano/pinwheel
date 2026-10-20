import Pinwheel.Hardware.Buffered.SerialUploadProgress
import Pinwheel.Hardware.Buffered.SerialUploadEncoding
import Pinwheel.Hardware.Buffered.SerialWireTransaction

namespace Pinwheel.Hardware.Buffered.SerialUpload
open Pinwheel.Hardware SerialWire
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem commands_append (s : SerialPackage.State) (a b : List SerialPackage.Pins) :
    s.commands (a ++ b) = s.commands a ++ (s.run a).commands b := by
  induction a generalizing s
  case nil => rfl
  case cons pin rest ih =>
    simp only [SerialPackage.State.commands, List.cons_append, ih,
      SerialPackage.State.run, List.foldl_cons]
  done

theorem quiet_invariant (P : SramState.State → Prop)
    (preserve : ∀ s i, P s → Serial.Frames.Quiet i → P (s.step i))
    (s : SramState.State) (inputs : List (Values Reactive.Input)) (initial : P s)
    (quiet : ∀ i ∈ inputs, Serial.Frames.Quiet i) : P (s.run inputs) := by
  induction inputs generalizing s
  case nil => exact initial
  case cons i rest ih =>
    exact ih (s.step i) (preserve s i initial (quiet i (by simp)))
      (fun j member => quiet j (List.mem_cons_of_mem _ member))
  done

theorem package_invariant (P : SramState.State → Prop)
    (preserve : ∀ s i, P s → Serial.Frames.Quiet i → P (s.step i))
    (s : SerialPackage.State) (pins : List SerialPackage.Pins) (initial : P s.controller)
    (quiet : ∀ i ∈ s.commands pins, Serial.Frames.Quiet i) : P (s.run pins).controller := by
  rw [s.run_controller]
  exact quiet_invariant P preserve s.controller _ initial quiet
  done

theorem transaction_invariant {before : SerialPackage.State} (transaction : Transaction before)
    (P Q : SramState.State → Prop) (initial : P before.controller)
    (beforeQuiet : ∀ s i, P s → Serial.Frames.Quiet i → P (s.step i))
    (dispatch : P transaction.framed.controller → Q transaction.delivered.controller)
    (afterQuiet : ∀ s i, Q s → Serial.Frames.Quiet i → Q (s.step i)) :
    Q transaction.after.controller := by
  have framed : P transaction.framed.controller :=
    package_invariant P beforeQuiet before transaction.request.pins initial transaction.request.quiet
  have captured : Q transaction.captured.controller :=
    afterQuiet transaction.delivered.controller _ (dispatch framed) transaction.capture_quiet
  exact package_invariant Q afterQuiet transaction.captured transaction.read.pins captured transaction.read_quiet
  done

theorem transaction_commands {before : SerialPackage.State} (transaction : Transaction before) :
    before.commands transaction.pins = before.commands transaction.request.pins ++
      (fun {w} (port : Reactive.Input w) => transaction.framed.coreInputs transaction.dispatch port) ::
      (fun {w} (port : Reactive.Input w) => transaction.delivered.coreInputs transaction.capture port) ::
      transaction.captured.commands transaction.read.pins := by
  simp only [Transaction.pins, commands_append, SerialPackage.State.commands]
  rfl
  done

theorem transaction_history {before : SerialPackage.State} (transaction : Transaction before)
    (source : I2cLoading.SourceInput transaction.framed.controller
      (transaction.framed.coreInputs transaction.dispatch)) :
    I2cLoading.SourceHistory before.controller (before.commands transaction.pins) := by
  rw [transaction_commands]
  apply history_append before.controller
  · exact quiet_history _ _ transaction.request.quiet
  · rw [← before.run_controller]
    exact ⟨source, quiet_source _ _ transaction.capture_quiet,
      quiet_history _ _ transaction.read_quiet⟩
  done

theorem transaction_loader {before : SerialPackage.State} (transaction : Transaction before)
    (loader : LifecycleUpload.Input (transaction.framed.coreInputs transaction.dispatch)) :
    ∀ i ∈ before.commands transaction.pins, LifecycleUpload.Input i := by
  rw [transaction_commands]
  intro i member
  simp only [List.mem_append, List.mem_cons] at member
  rcases member with request | dispatch | capture | read
  · have quiet := transaction.request.quiet i request
    exact ⟨quiet.1, by simp [quiet.2], by simp [quiet.2]⟩
  · subst i
    exact loader
  · subst i
    exact ⟨transaction.capture_quiet.1, by simp [transaction.capture_quiet.2],
      by simp [transaction.capture_quiet.2]⟩
  · have quiet := transaction.read_quiet i read
    exact ⟨quiet.1, by simp [quiet.2], by simp [quiet.2]⟩
  done

theorem table_transaction {before : SerialPackage.State} (transaction : Transaction before)
    (sequence : BitVec 16) (n : Nat)
    (word : transaction.request.word = tableWord sequence (BitVec.ofNat 4 n))
    {generation : BitVec 16} (progress : TableProgress generation n before.controller) :
    TableProgress generation (n+1) transaction.after.controller ∧
      I2cLoading.SourceHistory before.controller (before.commands transaction.pins) ∧
      (∀ i ∈ before.commands transaction.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available transaction.after.record := by
  have closed := transaction.request.closed
  rw [word] at closed
  have input := table_operands transaction.framed transaction.dispatch sequence _ closed transaction.dispatchIdle.1
  refine ⟨?_, transaction_history transaction (input.source _),
    transaction_loader transaction ⟨input.cold, by simp [input.command], by simp [input.command]⟩,
    transaction.exact.1⟩
  exact transaction_invariant transaction (TableProgress generation n) (TableProgress generation (n+1))
    progress (fun _ i h quiet => h.quiet i quiet) (fun h => h.write _ input)
    (fun _ i h quiet => h.quiet i quiet)
  done

theorem row_transaction {before : SerialPackage.State} (transaction : Transaction before)
    (sequence : BitVec 16) (n : Nat)
    (word : transaction.request.word = rowWord sequence (BitVec.ofNat 6 n))
    {generation : BitVec 16} (progress : RowProgress generation n before.controller) :
    RowProgress generation (n+1) transaction.after.controller ∧
      I2cLoading.SourceHistory before.controller (before.commands transaction.pins) ∧
      (∀ i ∈ before.commands transaction.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available transaction.after.record := by
  have closed := transaction.request.closed
  rw [word] at closed
  have input := row_operands transaction.framed transaction.dispatch sequence _ closed transaction.dispatchIdle.1
  refine ⟨?_, transaction_history transaction (input.source _),
    transaction_loader transaction ⟨input.cold, by simp [input.command], by simp [input.command]⟩,
    transaction.exact.1⟩
  exact transaction_invariant transaction (RowProgress generation n) (RowProgress generation (n+1))
    progress (fun _ i h quiet => h.quiet i quiet) (fun h => h.write _ input)
    (fun _ i h quiet => h.quiet i quiet)
  done

theorem commit_transaction {before : SerialPackage.State} (transaction : Transaction before)
    (sequence : BitVec 16) (word : transaction.request.word = commitWord sequence)
    {generation : BitVec 16} (progress : RowProgress generation 50 before.controller)
    (space : generation ≠ 65535) :
    Complete generation transaction.after.controller ∧
      I2cLoading.SourceHistory before.controller (before.commands transaction.pins) ∧
      (∀ i ∈ before.commands transaction.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available transaction.after.record := by
  have closed := transaction.request.closed
  rw [word] at closed
  have input := commit_operands transaction.framed transaction.dispatch sequence closed transaction.dispatchIdle.1
  refine ⟨?_, transaction_history transaction (input.source _),
    transaction_loader transaction ⟨input.cold, by simp [input.command], by simp [input.command]⟩,
    transaction.exact.1⟩
  exact transaction_invariant transaction (RowProgress generation 50) (Complete generation)
    progress (fun _ i h quiet => h.quiet i quiet) (fun h => h.commit _ input space)
    (fun _ i h quiet => h.quiet i quiet)
  done

end Pinwheel.Hardware.Buffered.SerialUpload
