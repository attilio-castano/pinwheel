import Pinwheel.Hardware.Buffered.SerialUploadTransaction

/-! A 67-command wire upload. Each constructor carries sampled pins and its
physical framing proof, not a presumed decoded command. Receipt reads occur
between commands and preserve frontend availability. -/
namespace Pinwheel.Hardware.Buffered.SerialUpload
open Pinwheel.Hardware SerialWire
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Tables : Nat → SerialPackage.State → SerialPackage.State → Type where
  | nil (s : SerialPackage.State) : Tables 0 s s
  | snoc {n before middle} (priorTrace : Tables n before middle)
      (transaction : Transaction middle) (sequence : BitVec 16)
      (word : transaction.request.word = tableWord sequence (BitVec.ofNat 4 n)) :
      Tables (n+1) before transaction.after

def Tables.pins {n before after} : Tables n before after → List SerialPackage.Pins
  | .nil _ => []
  | .snoc priorTrace transaction _ _ => priorTrace.pins ++ transaction.pins

theorem Tables.run_pins {n before after} (trace : Tables n before after) :
    before.run trace.pins = after := by
  induction trace
  case nil => rfl
  case snoc priorTrace transaction sequence word ih =>
    simpa only [Tables.pins, SerialPackage.State.run, List.foldl_append] using
      (congrArg (fun s : SerialPackage.State => s.run transaction.pins) ih).trans transaction.run_pins
  done

theorem combine_history (before middle : SerialPackage.State)
    (priorTrace rest : List SerialPackage.Pins) (run : before.run priorTrace = middle)
    (first : I2cLoading.SourceHistory before.controller (before.commands priorTrace))
    (second : I2cLoading.SourceHistory middle.controller (middle.commands rest)) :
    I2cLoading.SourceHistory before.controller (before.commands (priorTrace ++ rest)) := by
  rw [commands_append]
  apply history_append before.controller
  · exact first
  · rw [← before.run_controller, run]
    exact second
  done

theorem combine_loader (before middle : SerialPackage.State)
    (priorTrace rest : List SerialPackage.Pins) (run : before.run priorTrace = middle)
    (first : ∀ i ∈ before.commands priorTrace, LifecycleUpload.Input i)
    (second : ∀ i ∈ middle.commands rest, LifecycleUpload.Input i) :
    ∀ i ∈ before.commands (priorTrace ++ rest), LifecycleUpload.Input i := by
  rw [commands_append, run]
  intro i member
  rcases List.mem_append.mp member with member | member
  · exact first i member
  · exact second i member
  done

theorem Tables.result {n before after} (trace : Tables n before after)
    {generation : BitVec 16} (progress : TableProgress generation 0 before.controller)
    (available : Serial.Frames.Available before.record) :
    TableProgress generation n after.controller ∧
      I2cLoading.SourceHistory before.controller (before.commands trace.pins) ∧
      (∀ i ∈ before.commands trace.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available after.record := by
  induction trace
  case nil => exact ⟨progress, True.intro, by simp [Tables.pins, SerialPackage.State.commands], available⟩
  case snoc priorTrace transaction sequence word ih =>
    have prior := ih progress available
    have next := table_transaction transaction sequence _ word prior.1
    exact ⟨next.1, combine_history _ _ _ _ priorTrace.run_pins prior.2.1 next.2.1,
      combine_loader _ _ _ _ priorTrace.run_pins prior.2.2.1 next.2.2.1, next.2.2.2⟩
  done

inductive Rows : Nat → SerialPackage.State → SerialPackage.State → Type where
  | nil (s : SerialPackage.State) : Rows 0 s s
  | snoc {n before middle} (priorTrace : Rows n before middle)
      (transaction : Transaction middle) (sequence : BitVec 16)
      (word : transaction.request.word = rowWord sequence (BitVec.ofNat 6 n)) :
      Rows (n+1) before transaction.after

def Rows.pins {n before after} : Rows n before after → List SerialPackage.Pins
  | .nil _ => []
  | .snoc priorTrace transaction _ _ => priorTrace.pins ++ transaction.pins

theorem Rows.run_pins {n before after} (trace : Rows n before after) :
    before.run trace.pins = after := by
  induction trace
  case nil => rfl
  case snoc priorTrace transaction sequence word ih =>
    simpa only [Rows.pins, SerialPackage.State.run, List.foldl_append] using
      (congrArg (fun s : SerialPackage.State => s.run transaction.pins) ih).trans transaction.run_pins
  done

theorem Rows.result {n before after} (trace : Rows n before after)
    {generation : BitVec 16} (progress : RowProgress generation 0 before.controller)
    (available : Serial.Frames.Available before.record) :
    RowProgress generation n after.controller ∧
      I2cLoading.SourceHistory before.controller (before.commands trace.pins) ∧
      (∀ i ∈ before.commands trace.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available after.record := by
  induction trace
  case nil => exact ⟨progress, True.intro, by simp [Rows.pins, SerialPackage.State.commands], available⟩
  case snoc priorTrace transaction sequence word ih =>
    have prior := ih progress available
    have next := row_transaction transaction sequence _ word prior.1
    exact ⟨next.1, combine_history _ _ _ _ priorTrace.run_pins prior.2.1 next.2.1,
      combine_loader _ _ _ _ priorTrace.run_pins prior.2.2.1 next.2.2.1, next.2.2.2⟩
  done

structure Loading (before : SerialPackage.State) where
  afterTables : SerialPackage.State
  tables : Tables 16 before afterTables
  afterRows : SerialPackage.State
  rows : Rows 50 afterTables afterRows
  commit : Transaction afterRows
  sequence : BitVec 16
  word : commit.request.word = commitWord sequence

def Loading.after (loading : Loading before) : SerialPackage.State := loading.commit.after
def Loading.pins (loading : Loading before) : List SerialPackage.Pins :=
  loading.tables.pins ++ loading.rows.pins ++ loading.commit.pins

theorem Loading.run_pins {before} (loading : Loading before) :
    before.run loading.pins = loading.after := by
  simp only [Loading.pins, SerialPackage.State.run, List.foldl_append]
  change ((before.run loading.tables.pins).run loading.rows.pins).run loading.commit.pins = _
  rw [loading.tables.run_pins, loading.rows.run_pins, loading.commit.run_pins]
  rfl
  done

theorem Loading.result {before} (loading : Loading before)
    {generation : BitVec 16} (progress : TableProgress generation 0 before.controller)
    (space : generation ≠ 65535) (available : Serial.Frames.Available before.record) :
    Complete generation loading.after.controller ∧
      I2cLoading.SourceHistory before.controller (before.commands loading.pins) ∧
      (∀ i ∈ before.commands loading.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available loading.after.record := by
  have tables := loading.tables.result progress available
  have rows := loading.rows.result tables.1.rows tables.2.2.2
  have committed := commit_transaction loading.commit loading.sequence loading.word rows.1 space
  have firstRun : before.run (loading.tables.pins ++ loading.rows.pins) = loading.afterRows := by
    simp only [SerialPackage.State.run, List.foldl_append]
    change (before.run loading.tables.pins).run loading.rows.pins = _
    rw [loading.tables.run_pins, loading.rows.run_pins]
  refine ⟨committed.1, ?_, ?_, committed.2.2.2⟩
  · exact combine_history _ _ _ _ firstRun
      (combine_history _ _ _ _ loading.tables.run_pins tables.2.1 rows.2.1) committed.2.1
  · exact combine_loader _ _ _ _ firstRun
      (combine_loader _ _ _ _ loading.tables.run_pins tables.2.2.1 rows.2.2.1) committed.2.2.1
  done

end Pinwheel.Hardware.Buffered.SerialUpload
