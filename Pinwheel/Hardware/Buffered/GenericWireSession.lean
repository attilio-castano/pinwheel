import Pinwheel.Hardware.Buffered.GenericLogicalWireSession
import Pinwheel.Hardware.Buffered.GenericWireUploadReset
import Pinwheel.Hardware.Buffered.SerialWirePrefix

/-! Heterogeneous sampled-wire sessions.  A program identity changes only at
an actual reset/reload. The old program clocks the request prefix first, then
ordinary Transfer.reset acts on those exact carried buffers and the next
static image is installed by real wire transactions. -/
namespace Pinwheel.Hardware.Buffered.GenericWireSession
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames
open GenericLogicalWire (Cursor)
open SerialSourceSession (Frontend)
open _root_.Pinwheel.Hardware.Buffered.SerialUpload (ResetKind resetGeneration)
set_option maxRecDepth 4096

structure ProgramImage where
  program : Program.Buffered.Program
  layout : GenericCertificate.Layout program
  image : GenericUpload.Image program layout

def Valid (image : ProgramImage) :=
  GenericLogicalWire.Valid (p := image.program) (layout := image.layout)

inductive Event :
    SerialPackage.State → ProgramImage → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → ProgramImage → Cursor → Frontend → Type where
  | segment (image : ProgramImage)
      (trace : GenericLogicalWire.Trace image.program before cursor frontend pins after next nextFrontend) :
      Event before image cursor frontend pins after image next nextFrontend
  | coldAbort (image nextImage : ProgramImage) (cursor : Cursor) (frontend : Frontend)
      (rawPrefix : List SerialPackage.Pins)
      (quiet : ∀ input ∈ before.commands rawPrefix, SpiCircuit.Quiet input)
      (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
      (loading : GenericUpload.Serial.Loading nextImage.image ((before.run rawPrefix).step coldPin)) :
      Event before image cursor frontend (rawPrefix ++ coldPin :: loading.pins) loading.after nextImage
        (.free (LogicalSession.resetLogical (cursor.advance (p := image.program) rawPrefix).logical)
          (loading.after.controller.core .transfer).toNat) .available
  | reload (image nextImage : ProgramImage) (cursor : Cursor) (reset : SerialWire.Transaction before)
      (kind : ResetKind) (sequence : BitVec 16) (word : reset.request.word = kind.word sequence)
      (loading : GenericUpload.Serial.Loading nextImage.image reset.after)
      (space : resetGeneration kind (reset.framed.controller.core .generation) ≠ 65535) :
      Event before image cursor .available (reset.pins ++ loading.pins) loading.after nextImage
        (.free (LogicalSession.resetLogical (cursor.advance (p := image.program) reset.request.pins).logical)
          (loading.after.controller.core .transfer).toNat) .available

theorem Event.run_pins (event : Event before image cursor frontend pins after nextImage next nextFrontend) :
    before.run pins = after := by
  cases event with
  | segment image trace => exact trace.run_pins
  | coldAbort image nextImage cursor frontend rawPrefix quiet coldPin cold idle loading =>
    have loaded := (GenericUpload.Serial.cold_install nextImage.image (before.run rawPrefix)
      coldPin cold idle loading).2.2.2.2.2.2
    change List.foldl SerialPackage.State.step before (rawPrefix ++ coldPin :: loading.pins) = _
    rw [List.foldl_append]
    exact loaded
  | reload image nextImage cursor reset kind sequence word loading space =>
    exact (GenericUpload.Serial.wire_install nextImage.image reset kind sequence word loading space).2.2.2.2

theorem Event.preserves (event : Event before image cursor frontend pins after nextImage next nextFrontend)
    (initial : Valid image before cursor frontend) : Valid nextImage after next nextFrontend := by
  cases event with
  | segment image trace => exact trace.preserves initial
  | coldAbort image nextImage cursor frontend rawPrefix quiet coldPin cold idle loading =>
    obtain ⟨installed,phase,retained,_,_,available,_⟩ := GenericUpload.Serial.cold_install
      nextImage.image (before.run rawPrefix) coldPin cold idle loading
    exact ⟨available,installed,⟨rfl,phase,retained,rfl⟩⟩
  | reload image nextImage cursor reset kind sequence word loading space =>
    have loaded := GenericUpload.Serial.wire_install nextImage.image reset kind sequence word loading space
    exact ⟨loaded.2.2.1,loaded.1,⟨rfl,loaded.2.1.phase,loaded.2.1.retained,rfl⟩⟩

def Event.Observed (event : Event before image cursor frontend pins after nextImage next nextFrontend) : Prop :=
  match event with
  | .segment _ trace => trace.Observed
  | .coldAbort image nextImage cursor _ rawPrefix _ _ _ _ loading =>
    (cursor.advance (p := image.program) rawPrefix).Holds
      (p := image.program) (layout := image.layout) (before.run rawPrefix) ∧
      Transfer.step capacity (cursor.advance (p := image.program) rawPrefix).logical .reset =
        ⟨LogicalSession.resetLogical (cursor.advance (p := image.program) rawPrefix).logical,.reset⟩ ∧
      (LogicalSession.resetLogical (cursor.advance (p := image.program) rawPrefix).logical).epoch =
        (cursor.advance (p := image.program) rawPrefix).logical.epoch + 1 ∧
      (LogicalSession.resetLogical (cursor.advance (p := image.program) rawPrefix).logical).nextSequence = 1 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0 ∧
      InstalledSram nextImage.program nextImage.layout loading.after.controller
  | .reload image nextImage cursor reset kind _ _ loading _ =>
    (cursor.advance (p := image.program) reset.request.pins).Holds
      (p := image.program) (layout := image.layout) reset.framed ∧
      Transfer.step capacity (cursor.advance (p := image.program) reset.request.pins).logical .reset =
        ⟨LogicalSession.resetLogical (cursor.advance (p := image.program) reset.request.pins).logical,.reset⟩ ∧
      (LogicalSession.resetLogical (cursor.advance (p := image.program) reset.request.pins).logical).epoch =
        (cursor.advance (p := image.program) reset.request.pins).logical.epoch + 1 ∧
      (LogicalSession.resetLogical (cursor.advance (p := image.program) reset.request.pins).logical).nextSequence = 1 ∧
      Buffered.SerialUpload.Complete
        (resetGeneration kind (reset.framed.controller.core .generation)) loading.after.controller ∧
      loading.after.controller.core .transfer =
        (match kind with | .cold => 0 | .warm => before.controller.core .transfer) ∧
      InstalledSram nextImage.program nextImage.layout loading.after.controller

theorem Event.observed (event : Event before image cursor frontend pins after nextImage next nextFrontend)
    (initial : Valid image before cursor frontend) : event.Observed := by
  cases event with
  | segment image trace => exact trace.observed initial
  | coldAbort image nextImage cursor frontend rawPrefix quiet coldPin cold idle loading =>
    obtain ⟨installed,_,_,generation,transfer,_,_⟩ := GenericUpload.Serial.cold_install
      nextImage.image (before.run rawPrefix) coldPin cold idle loading
    exact ⟨GenericLogicalWire.Cursor.quiet_run initial.2 rawPrefix quiet,rfl,rfl,rfl,generation,transfer,installed⟩
  | reload image nextImage cursor reset kind sequence word loading space =>
    have loaded := GenericUpload.Serial.wire_install nextImage.image reset kind sequence word loading space
    exact ⟨GenericLogicalWire.Cursor.quiet_run initial.2 _ reset.request.quiet,rfl,rfl,rfl,
      loaded.2.1,loaded.2.2.2.1,loaded.1⟩

inductive Trace :
    SerialPackage.State → ProgramImage → Cursor → Frontend → List SerialPackage.Pins →
      SerialPackage.State → ProgramImage → Cursor → Frontend → Type where
  | nil : Trace before image cursor frontend [] before image cursor frontend
  | cons (event : Event before image cursor frontend first middle nextImage next nextFrontend)
      (rest : Trace middle nextImage next nextFrontend more after finalImage final finalFrontend) :
      Trace before image cursor frontend (first ++ more) after finalImage final finalFrontend

theorem Trace.run_pins (trace : Trace before image cursor frontend pins after finalImage final finalFrontend) :
    before.run pins = after := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
    simp only [SerialPackage.State.run,List.foldl_append]
    change SerialPackage.State.run (SerialPackage.State.run _ _) _ = _
    rw [event.run_pins]
    exact ih

theorem Trace.preserves (trace : Trace before image cursor frontend pins after finalImage final finalFrontend)
    (initial : Valid image before cursor frontend) : Valid finalImage after final finalFrontend := by
  induction trace with
  | nil => exact initial
  | cons event rest ih => exact ih (event.preserves initial)

def Trace.Observed : Trace before image cursor frontend pins after finalImage final finalFrontend → Prop
  | .nil => True
  | .cons event rest => event.Observed ∧ rest.Observed

theorem Trace.observed (trace : Trace before image cursor frontend pins after finalImage final finalFrontend)
    (initial : Valid image before cursor frontend) : trace.Observed := by
  induction trace with
  | nil => trivial
  | cons event rest ih => exact ⟨event.observed initial,ih (event.preserves initial)⟩

theorem Trace.session (trace : Trace before image cursor frontend pins after finalImage final finalFrontend)
    (initial : Valid image before cursor frontend) :
    before.run pins = after ∧ Valid finalImage after final finalFrontend ∧ trace.Observed :=
  ⟨trace.run_pins,trace.preserves initial,trace.observed initial⟩

end Pinwheel.Hardware.Buffered.GenericWireSession
