import Pinwheel.Hardware.Buffered.I2cTimingSerialEncoding
import Pinwheel.Hardware.Buffered.SerialUploadConcrete

/-! Parameterized timing upload over actual framed serial transactions.  Every
request, dispatch, capture and full receipt read clocks the same SRAM state. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming.SerialUpload
open Pinwheel.Hardware SerialWire
open _root_.Pinwheel.Hardware.Buffered.SerialUpload (TableProgress RowProgress Complete)
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem transaction_history (duration budget : Fin 256)
    {before : SerialPackage.State} (transaction : Transaction before)
    (source : Loading.SourceInput duration budget transaction.framed.controller
      (transaction.framed.coreInputs transaction.dispatch)) :
    Loading.SourceHistory duration budget before.controller (before.commands transaction.pins) := by
  rw [Buffered.SerialUpload.transaction_commands]
  apply history_append duration budget before.controller
  · exact quiet_history duration budget _ _ transaction.request.quiet
  · rw [← before.run_controller]
    exact ⟨source,quiet_source duration budget _ _ transaction.capture_quiet,
      quiet_history duration budget _ _ transaction.read_quiet⟩

theorem combine_history (duration budget : Fin 256) (before middle : SerialPackage.State)
    (first rest : List SerialPackage.Pins) (run : before.run first = middle)
    (head : Loading.SourceHistory duration budget before.controller (before.commands first))
    (tail : Loading.SourceHistory duration budget middle.controller (middle.commands rest)) :
    Loading.SourceHistory duration budget before.controller (before.commands (first ++ rest)) := by
  rw [Buffered.SerialUpload.commands_append]
  apply history_append duration budget before.controller
  · exact head
  · rw [← before.run_controller,run]
    exact tail

theorem tables_history (duration budget : Fin 256)
    {n before after} (trace : Buffered.SerialUpload.Tables n before after) :
    Loading.SourceHistory duration budget before.controller (before.commands trace.pins) := by
  induction trace with
  | nil => trivial
  | snoc prior transaction sequence word ih =>
    have closed := transaction.request.closed
    rw [word] at closed
    have input := Buffered.SerialUpload.table_operands transaction.framed transaction.dispatch
      sequence _ closed transaction.dispatchIdle.1
    exact combine_history duration budget _ _ _ _ prior.run_pins ih
      (transaction_history duration budget transaction (table_source duration budget _ input))

theorem row_transaction (duration budget : Fin 256)
    {before : SerialPackage.State} (transaction : Transaction before)
    (sequence : BitVec 16) (n : Nat)
    (word : transaction.request.word = rowWord duration budget sequence (BitVec.ofNat 6 n))
    {generation : BitVec 16} (progress : RowProgress generation n before.controller) :
    RowProgress generation (n+1) transaction.after.controller ∧
      Loading.SourceHistory duration budget before.controller (before.commands transaction.pins) ∧
      (∀ i ∈ before.commands transaction.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available transaction.after.record := by
  have closed := transaction.request.closed
  rw [word] at closed
  have input := row_operands duration budget transaction.framed transaction.dispatch
    sequence _ closed transaction.dispatchIdle.1
  refine ⟨?_,transaction_history duration budget transaction (input.source _),
    Buffered.SerialUpload.transaction_loader transaction
      ⟨input.cold,by simp [input.command],by simp [input.command]⟩,transaction.exact.1⟩
  exact Buffered.SerialUpload.transaction_invariant transaction
    (RowProgress generation n) (RowProgress generation (n+1)) progress
    (fun _ i h quiet => h.quiet i quiet) (fun h => Row.write h _ input)
    (fun _ i h quiet => h.quiet i quiet)

inductive Rows (duration budget : Fin 256) : Nat → SerialPackage.State → SerialPackage.State → Type where
  | nil (s : SerialPackage.State) : Rows duration budget 0 s s
  | snoc {n before middle} (prior : Rows duration budget n before middle)
      (transaction : Transaction middle) (sequence : BitVec 16)
      (word : transaction.request.word = rowWord duration budget sequence (BitVec.ofNat 6 n)) :
      Rows duration budget (n+1) before transaction.after

def Rows.pins {duration budget n before after} : Rows duration budget n before after → List SerialPackage.Pins
  | .nil _ => []
  | .snoc prior transaction _ _ => prior.pins ++ transaction.pins

theorem Rows.run_pins {duration budget n before after} (trace : Rows duration budget n before after) :
    before.run trace.pins = after := by
  induction trace with
  | nil => rfl
  | snoc prior transaction sequence word ih =>
    simpa only [Rows.pins,SerialPackage.State.run,List.foldl_append] using
      (congrArg (fun s : SerialPackage.State => s.run transaction.pins) ih).trans transaction.run_pins

theorem Rows.result {duration budget n before after} (trace : Rows duration budget n before after)
    {generation : BitVec 16} (progress : RowProgress generation 0 before.controller)
    (available : Serial.Frames.Available before.record) :
    RowProgress generation n after.controller ∧
      I2cTiming.Loading.SourceHistory duration budget before.controller (before.commands trace.pins) ∧
      (∀ i ∈ before.commands trace.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available after.record := by
  induction trace with
  | nil => exact ⟨progress,True.intro,by simp [Rows.pins,SerialPackage.State.commands],available⟩
  | snoc prior transaction sequence word ih =>
    have previous := ih progress available
    have next := row_transaction duration budget transaction sequence _ word previous.1
    exact ⟨next.1,combine_history duration budget _ _ _ _ prior.run_pins previous.2.1 next.2.1,
      Buffered.SerialUpload.combine_loader _ _ _ _ prior.run_pins previous.2.2.1 next.2.2.1,next.2.2.2⟩

structure Loading (duration budget : Fin 256) (before : SerialPackage.State) where
  afterTables : SerialPackage.State
  tables : Buffered.SerialUpload.Tables 16 before afterTables
  afterRows : SerialPackage.State
  rows : Rows duration budget 50 afterTables afterRows
  commit : Transaction afterRows
  sequence : BitVec 16
  word : commit.request.word = Buffered.SerialUpload.commitWord sequence

def Loading.after {duration budget before} (loading : Loading duration budget before) : SerialPackage.State :=
  loading.commit.after

def Loading.pins {duration budget before} (loading : Loading duration budget before) : List SerialPackage.Pins :=
  loading.tables.pins ++ loading.rows.pins ++ loading.commit.pins

theorem Loading.run_pins {duration budget before} (loading : Loading duration budget before) :
    before.run loading.pins = loading.after := by
  simp only [Loading.pins,SerialPackage.State.run,List.foldl_append]
  change ((before.run loading.tables.pins).run loading.rows.pins).run loading.commit.pins = _
  rw [loading.tables.run_pins,loading.rows.run_pins,loading.commit.run_pins]
  rfl

theorem Loading.result {duration budget before} (loading : Loading duration budget before)
    {generation : BitVec 16} (progress : TableProgress generation 0 before.controller)
    (space : generation ≠ 65535) (available : Serial.Frames.Available before.record) :
    Complete generation loading.after.controller ∧
      I2cTiming.Loading.SourceHistory duration budget before.controller (before.commands loading.pins) ∧
      (∀ i ∈ before.commands loading.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available loading.after.record := by
  have tables := loading.tables.result progress available
  have rows := loading.rows.result tables.1.rows tables.2.2.2
  have committed := Buffered.SerialUpload.commit_transaction loading.commit loading.sequence loading.word rows.1 space
  have closed := loading.commit.request.closed
  rw [loading.word] at closed
  have input := Buffered.SerialUpload.commit_operands loading.commit.framed loading.commit.dispatch
    loading.sequence closed loading.commit.dispatchIdle.1
  have committedHistory := transaction_history duration budget loading.commit (commit_source duration budget _ input)
  have firstRun : before.run (loading.tables.pins ++ loading.rows.pins) = loading.afterRows := by
    simp only [SerialPackage.State.run,List.foldl_append]
    change (before.run loading.tables.pins).run loading.rows.pins = _
    rw [loading.tables.run_pins,loading.rows.run_pins]
  refine ⟨committed.1,?_,?_,committed.2.2.2⟩
  · exact combine_history duration budget _ _ _ _ firstRun
      (combine_history duration budget _ _ _ _ loading.tables.run_pins
        (tables_history duration budget loading.tables) rows.2.1) committedHistory
  · exact Buffered.SerialUpload.combine_loader _ _ _ _ firstRun
      (Buffered.SerialUpload.combine_loader _ _ _ _ loading.tables.run_pins tables.2.2.1 rows.2.2.1) committed.2.2.1

theorem Loading.controller_run {duration budget before} (loading : Loading duration budget before) :
    before.controller.run (before.commands loading.pins) = loading.after.controller := by
  rw [← before.run_controller,loading.run_pins]

end Pinwheel.Hardware.Buffered.I2cTiming.SerialUpload
