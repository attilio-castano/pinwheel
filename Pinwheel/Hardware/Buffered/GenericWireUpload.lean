import Pinwheel.Hardware.Buffered.GenericUploadTransaction
import Pinwheel.Hardware.Buffered.SerialUploadTrace

/-! A wire upload with 16 dictionary, count row and one COMMIT transaction.
Each constructor carries sampled pins and its
physical framing proof, not a presumed decoded command. Receipt reads occur
between commands and preserve frontend availability. -/
namespace Pinwheel.Hardware.Buffered.GenericUpload.Serial
open Pinwheel.Hardware Pinwheel.Program SerialWire
open _root_.Pinwheel.Hardware.Buffered.SerialUpload (TableProgress RowProgress Complete)
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Tables (image : Image p layout) : Nat → SerialPackage.State → SerialPackage.State → Type where
  | nil (s : SerialPackage.State) : Tables image 0 s s
  | snoc {n before middle} (priorTrace : Tables image n before middle)
      (transaction : Transaction middle) (sequence : BitVec 16)
      (word : transaction.request.word = tableWord image sequence (BitVec.ofNat 4 n)) :
      Tables image (n+1) before transaction.after

def Tables.pins {image : Image p layout} {n before after} : Tables image n before after → List SerialPackage.Pins
  | .nil _ => []
  | .snoc priorTrace transaction _ _ => priorTrace.pins ++ transaction.pins

theorem Tables.run_pins {image : Image p layout} {n before after} (trace : Tables image n before after) :
    before.run trace.pins = after := by
  induction trace
  case nil => rfl
  case snoc priorTrace transaction sequence word ih =>
    simpa only [Tables.pins, SerialPackage.State.run, List.foldl_append] using
      (congrArg (fun s : SerialPackage.State => s.run transaction.pins) ih).trans transaction.run_pins
  done

theorem combine_history (image : Image p layout) (before middle : SerialPackage.State)
    (priorTrace rest : List SerialPackage.Pins) (run : before.run priorTrace = middle)
    (first : SourceHistory image before.controller (before.commands priorTrace))
    (second : SourceHistory image middle.controller (middle.commands rest)) :
    SourceHistory image before.controller (before.commands (priorTrace ++ rest)) := by
  rw [Buffered.SerialUpload.commands_append]
  apply history_append image before.controller
  · exact first
  · rw [← before.run_controller, run]
    exact second
  done

theorem Tables.result {image : Image p layout} {n before after} (trace : Tables image n before after)
    {generation : BitVec 16} (progress : TableProgress generation 0 before.controller)
    (available : Serial.Frames.Available before.record) :
    TableProgress generation n after.controller ∧
      SourceHistory image before.controller (before.commands trace.pins) ∧
      (∀ i ∈ before.commands trace.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available after.record := by
  induction trace
  case nil => exact ⟨progress, True.intro, by simp [Tables.pins, SerialPackage.State.commands], available⟩
  case snoc priorTrace transaction sequence word ih =>
    have prior := ih progress available
    have next := table_transaction image transaction sequence _ word prior.1
    exact ⟨next.1, combine_history image _ _ _ _ priorTrace.run_pins prior.2.1 next.2.1,
      Buffered.SerialUpload.combine_loader _ _ _ _ priorTrace.run_pins prior.2.2.1 next.2.2.1, next.2.2.2⟩
  done

inductive Rows (image : Image p layout) : Nat → SerialPackage.State → SerialPackage.State → Type where
  | nil (s : SerialPackage.State) : Rows image 0 s s
  | snoc {n before middle} (priorTrace : Rows image n before middle)
      (transaction : Transaction middle) (sequence : BitVec 16)
      (word : transaction.request.word = rowWord image sequence (BitVec.ofNat 6 n)) :
      Rows image (n+1) before transaction.after

def Rows.pins {image : Image p layout} {n before after} : Rows image n before after → List SerialPackage.Pins
  | .nil _ => []
  | .snoc priorTrace transaction _ _ => priorTrace.pins ++ transaction.pins

theorem Rows.run_pins {image : Image p layout} {n before after} (trace : Rows image n before after) :
    before.run trace.pins = after := by
  induction trace
  case nil => rfl
  case snoc priorTrace transaction sequence word ih =>
    simpa only [Rows.pins, SerialPackage.State.run, List.foldl_append] using
      (congrArg (fun s : SerialPackage.State => s.run transaction.pins) ih).trans transaction.run_pins
  done

theorem Rows.result {image : Image p layout} {n before after} (trace : Rows image n before after)
    {generation : BitVec 16} (progress : RowProgress generation 0 before.controller)
    (available : Serial.Frames.Available before.record) :
    RowProgress generation n after.controller ∧
      SourceHistory image before.controller (before.commands trace.pins) ∧
      (∀ i ∈ before.commands trace.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available after.record := by
  induction trace
  case nil => exact ⟨progress, True.intro, by simp [Rows.pins, SerialPackage.State.commands], available⟩
  case snoc priorTrace transaction sequence word ih =>
    have prior := ih progress available
    have next := row_transaction image transaction sequence _ word prior.1
    exact ⟨next.1, combine_history image _ _ _ _ priorTrace.run_pins prior.2.1 next.2.1,
      Buffered.SerialUpload.combine_loader _ _ _ _ priorTrace.run_pins prior.2.2.1 next.2.2.1, next.2.2.2⟩
  done

structure Loading (image : Image p layout) (before : SerialPackage.State) where
  afterTables : SerialPackage.State
  tables : Tables image 16 before afterTables
  afterRows : SerialPackage.State
  rows : Rows image layout.count.val afterTables afterRows
  commit : Transaction afterRows
  sequence : BitVec 16
  word : commit.request.word = commitWord p layout sequence

def Loading.after {image : Image p layout} (loading : Loading image before) : SerialPackage.State := loading.commit.after
def Loading.pins {image : Image p layout} (loading : Loading image before) : List SerialPackage.Pins :=
  loading.tables.pins ++ loading.rows.pins ++ loading.commit.pins

theorem Loading.run_pins {image : Image p layout} {before} (loading : Loading image before) :
    before.run loading.pins = loading.after := by
  simp only [Loading.pins, SerialPackage.State.run, List.foldl_append]
  change ((before.run loading.tables.pins).run loading.rows.pins).run loading.commit.pins = _
  rw [loading.tables.run_pins, loading.rows.run_pins, loading.commit.run_pins]
  rfl
  done

theorem Loading.result {image : Image p layout} {before} (loading : Loading image before)
    {generation : BitVec 16} (progress : TableProgress generation 0 before.controller)
    (space : generation ≠ 65535) (available : Serial.Frames.Available before.record) :
    Complete generation loading.after.controller ∧
      SourceHistory image before.controller (before.commands loading.pins) ∧
      (∀ i ∈ before.commands loading.pins, LifecycleUpload.Input i) ∧
      Serial.Frames.Available loading.after.record := by
  have tables := loading.tables.result progress available
  have rows := loading.rows.result tables.1.rows tables.2.2.2
  have committed := commit_transaction image loading.commit loading.sequence loading.word rows.1 space
  have firstRun : before.run (loading.tables.pins ++ loading.rows.pins) = loading.afterRows := by
    simp only [SerialPackage.State.run, List.foldl_append]
    change (before.run loading.tables.pins).run loading.rows.pins = _
    rw [loading.tables.run_pins, loading.rows.run_pins]
  refine ⟨committed.1, ?_, ?_, committed.2.2.2⟩
  · exact combine_history image _ _ _ _ firstRun
      (combine_history image _ _ _ _ loading.tables.run_pins tables.2.1 rows.2.1) committed.2.1
  · exact Buffered.SerialUpload.combine_loader _ _ _ _ firstRun
      (Buffered.SerialUpload.combine_loader _ _ _ _ loading.tables.run_pins tables.2.2.1 rows.2.2.1) committed.2.2.1
  done

end Pinwheel.Hardware.Buffered.GenericUpload.Serial
