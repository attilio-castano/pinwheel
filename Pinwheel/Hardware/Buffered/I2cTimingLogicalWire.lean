import Pinwheel.Hardware.Buffered.GenericLogicalWireSession
import Pinwheel.Hardware.Buffered.I2cTimingSerialReset
import Pinwheel.Hardware.Buffered.SerialWirePrefix

/-! Repeated, padded and interrupted sampled-wire sessions for every symbolic
duration/budget pair.  Runtime events use one generic carried logical cursor;
all image installation facts come from actual 67-transaction uploads. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming.LogicalWire
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames
open SerialSourceSession (Frontend)
open GenericLogicalWire (Cursor)
open _root_.Pinwheel.Hardware.Buffered.SerialUpload (ResetKind resetGeneration)
set_option maxRecDepth 4096

abbrev Valid (duration budget : Fin 256) :=
  GenericLogicalWire.Valid (p := source duration budget) (layout := layout duration budget)

inductive Event (duration budget : Fin 256) :
    SerialPackage.State → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → Cursor → Frontend → Type where
  | segment (trace : GenericLogicalWire.Trace (source duration budget)
      before cursor frontend pins after next nextFrontend) :
      Event duration budget before cursor frontend pins after next nextFrontend
  | coldAbort (cursor : Cursor) (frontend : Frontend) (rawPrefix : List SerialPackage.Pins)
      (quiet : ∀ input ∈ before.commands rawPrefix, SpiCircuit.Quiet input)
      (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
      (loading : SerialUpload.Loading duration budget ((before.run rawPrefix).step coldPin)) :
      Event duration budget before cursor frontend (rawPrefix ++ coldPin :: loading.pins) loading.after
        (.free (LogicalSession.resetLogical (cursor.advance (p := source duration budget) rawPrefix).logical)
          (loading.after.controller.core .transfer).toNat) .available
  | reload (cursor : Cursor) (reset : SerialWire.Transaction before)
      (kind : ResetKind) (sequence : BitVec 16) (word : reset.request.word = kind.word sequence)
      (loading : SerialUpload.Loading duration budget reset.after)
      (space : resetGeneration kind (reset.framed.controller.core .generation) ≠ 65535) :
      Event duration budget before cursor .available (reset.pins ++ loading.pins) loading.after
        (.free (LogicalSession.resetLogical
          (cursor.advance (p := source duration budget) reset.request.pins).logical)
          (loading.after.controller.core .transfer).toNat) .available

theorem Event.run_pins {duration budget} (event : Event duration budget before cursor frontend pins after next nextFrontend) :
    before.run pins = after := by
  cases event with
  | segment trace => exact trace.run_pins
  | coldAbort frontend rawPrefix quiet coldPin cold idle loading =>
    have loaded := (SerialUpload.cold_install duration budget (before.run rawPrefix) coldPin cold idle loading).2.2.2.2.2.2
    change List.foldl SerialPackage.State.step before (rawPrefix ++ coldPin :: loading.pins) = _
    rw [List.foldl_append]
    exact loaded
  | reload reset kind sequence word loading space =>
    exact (SerialUpload.wire_install duration budget reset kind sequence word loading space).2.2.2.2

theorem Event.preserves {duration budget} (event : Event duration budget before cursor frontend pins after next nextFrontend)
    (initial : Valid duration budget before cursor frontend) : Valid duration budget after next nextFrontend := by
  cases event with
  | segment trace => exact trace.preserves initial
  | coldAbort frontend rawPrefix quiet coldPin cold idle loading =>
    obtain ⟨installed,phase,retained,_,_,available,_⟩ :=
      SerialUpload.cold_install duration budget (before.run rawPrefix) coldPin cold idle loading
    exact ⟨available,installed,⟨rfl,phase,retained,rfl⟩⟩
  | reload reset kind sequence word loading space =>
    have loaded := SerialUpload.wire_install duration budget reset kind sequence word loading space
    exact ⟨loaded.2.2.1,loaded.1,⟨rfl,loaded.2.1.phase,loaded.2.1.retained,rfl⟩⟩

def Event.Observed {duration budget} (event : Event duration budget before cursor frontend pins after next nextFrontend) : Prop :=
  match event with
  | .segment trace => trace.Observed
  | @Event.coldAbort _ _ _ cursor _ rawPrefix _ _ _ _ loading =>
    (cursor.advance (p := source duration budget) rawPrefix).Holds
      (p := source duration budget) (layout := layout duration budget) (before.run rawPrefix) ∧
      Transfer.step capacity (cursor.advance (p := source duration budget) rawPrefix).logical .reset =
        ⟨LogicalSession.resetLogical (cursor.advance (p := source duration budget) rawPrefix).logical,.reset⟩ ∧
      (LogicalSession.resetLogical (cursor.advance (p := source duration budget) rawPrefix).logical).epoch =
        (cursor.advance (p := source duration budget) rawPrefix).logical.epoch + 1 ∧
      (LogicalSession.resetLogical (cursor.advance (p := source duration budget) rawPrefix).logical).nextSequence = 1 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0
  | @Event.reload _ _ _ cursor reset kind _ _ loading _ =>
    (cursor.advance (p := source duration budget) reset.request.pins).Holds
      (p := source duration budget) (layout := layout duration budget) reset.framed ∧
      Transfer.step capacity (cursor.advance (p := source duration budget) reset.request.pins).logical .reset =
        ⟨LogicalSession.resetLogical (cursor.advance (p := source duration budget) reset.request.pins).logical,.reset⟩ ∧
      (LogicalSession.resetLogical (cursor.advance (p := source duration budget) reset.request.pins).logical).epoch =
        (cursor.advance (p := source duration budget) reset.request.pins).logical.epoch + 1 ∧
      (LogicalSession.resetLogical (cursor.advance (p := source duration budget) reset.request.pins).logical).nextSequence = 1 ∧
      Buffered.SerialUpload.Complete
        (resetGeneration kind (reset.framed.controller.core .generation)) loading.after.controller ∧
      loading.after.controller.core .transfer =
        (match kind with | .cold => 0 | .warm => before.controller.core .transfer)

theorem Event.observed {duration budget} (event : Event duration budget before cursor frontend pins after next nextFrontend)
    (initial : Valid duration budget before cursor frontend) : event.Observed := by
  cases event with
  | segment trace => exact trace.observed initial
  | coldAbort frontend rawPrefix quiet coldPin cold idle loading =>
    obtain ⟨_,_,_,generation,transfer,_,_⟩ :=
      SerialUpload.cold_install duration budget (before.run rawPrefix) coldPin cold idle loading
    exact ⟨GenericLogicalWire.Cursor.quiet_run initial.2 rawPrefix quiet,rfl,rfl,rfl,generation,transfer⟩
  | reload reset kind sequence word loading space =>
    have loaded := SerialUpload.wire_install duration budget reset kind sequence word loading space
    exact ⟨GenericLogicalWire.Cursor.quiet_run initial.2 _ reset.request.quiet,rfl,rfl,rfl,
      loaded.2.1,loaded.2.2.2.1⟩

inductive Trace (duration budget : Fin 256) :
    SerialPackage.State → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → Cursor → Frontend → Type where
  | nil : Trace duration budget before cursor frontend [] before cursor frontend
  | cons (event : Event duration budget before cursor frontend first middle next nextFrontend)
      (rest : Trace duration budget middle next nextFrontend more after final finalFrontend) :
      Trace duration budget before cursor frontend (first ++ more) after final finalFrontend

theorem Trace.run_pins {duration budget}
    (trace : Trace duration budget before cursor frontend pins after final finalFrontend) :
    before.run pins = after := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
    simp only [SerialPackage.State.run,List.foldl_append]
    change SerialPackage.State.run (SerialPackage.State.run _ _) _ = _
    rw [event.run_pins]
    exact ih

theorem Trace.preserves {duration budget}
    (trace : Trace duration budget before cursor frontend pins after final finalFrontend)
    (initial : Valid duration budget before cursor frontend) : Valid duration budget after final finalFrontend := by
  induction trace with
  | nil => exact initial
  | cons event rest ih => exact ih (event.preserves initial)

def Trace.Observed {duration budget} : Trace duration budget before cursor frontend pins after final finalFrontend → Prop
  | .nil => True
  | .cons event rest => event.Observed ∧ rest.Observed

theorem Trace.observed {duration budget}
    (trace : Trace duration budget before cursor frontend pins after final finalFrontend)
    (initial : Valid duration budget before cursor frontend) : trace.Observed := by
  induction trace with
  | nil => trivial
  | cons event rest ih => exact ⟨event.observed initial,ih (event.preserves initial)⟩

theorem Trace.session {duration budget}
    (trace : Trace duration budget before cursor frontend pins after final finalFrontend)
    (initial : Valid duration budget before cursor frontend) :
    before.run pins = after ∧ Valid duration budget after final finalFrontend ∧ trace.Observed :=
  ⟨trace.run_pins,trace.preserves initial,trace.observed initial⟩

end Pinwheel.Hardware.Buffered.I2cTiming.LogicalWire
