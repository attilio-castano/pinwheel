import Pinwheel.Hardware.Buffered.GenericWireSessionInitialized
import Pinwheel.Hardware.Buffered.GenericLogicalWireDiagnostic

namespace Pinwheel.Hardware.Buffered.GenericWireSession
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames SerialWire
open GenericLogicalWire (Cursor)
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable def appendTrace
    (head : Trace before image cursor frontend first middle nextImage next nextFrontend)
    (tail : Trace middle nextImage next nextFrontend more after finalImage final finalFrontend) :
    Trace before image cursor frontend (first ++ more) after finalImage final finalFrontend := by
  induction head with
  | nil => exact tail
  | cons event rest ih => simpa only [List.append_assoc] using Trace.cons event (ih tail)

def runtimeTrace (image : ProgramImage)
    (trace : GenericLogicalWire.Trace image.program before cursor frontend pins after next nextFrontend) :
    Trace before image cursor frontend pins after image next nextFrontend := by
  simpa only [List.append_nil] using Trace.cons (Event.segment image trace) .nil

structure WarmReload (image nextImage : ProgramImage) (before : SerialPackage.State)
    (logical : Transfer.State) (offset : Nat) where
  reset : Transaction before
  loading : GenericUpload.Serial.Loading nextImage.image reset.after
  trace : Trace before image (.free logical offset) .available (reset.pins ++ loading.pins) loading.after nextImage
    (.free (LogicalSession.resetLogical logical) (loading.after.controller.core .transfer).toNat) .available
  post : Valid nextImage loading.after
    (.free (LogicalSession.resetLogical logical) (loading.after.controller.core .transfer).toNat) .available
  generation : (loading.after.controller.core .generation).toNat = (before.controller.core .generation).toNat+2
  transfer : loading.after.controller.core .transfer = before.controller.core .transfer

def WarmReload.after (reload : WarmReload image nextImage before logical offset) : SerialPackage.State :=
  reload.loading.after

def WarmReload.pins (reload : WarmReload image nextImage before logical offset) : List SerialPackage.Pins :=
  reload.reset.pins ++ reload.loading.pins

def WarmReload.offset {offset : Nat} (reload : WarmReload image nextImage before logical offset) : Nat :=
  (reload.after.controller.core .transfer).toNat

noncomputable opaque makeWarmReload (image nextImage : ProgramImage) (before : SerialPackage.State)
    (logical : Transfer.State) (offset : Nat) (initial : Valid image before (.free logical offset) .available)
    (space : (before.controller.core .generation).toNat ≤ 65533)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    WarmReload image nextImage before logical offset := by
  let reset := concrete before initial.1 (Buffered.SerialUpload.ResetKind.warm.word (sequence 0)) raw
  let loading := GenericUpload.Serial.concreteLoading nextImage.image reset.after reset.exact.1
    (fun n => sequence (n+1)) raw
  have word : reset.request.word = Buffered.SerialUpload.ResetKind.warm.word (sequence 0) := concrete_word ..
  have room := Buffered.SerialUpload.warm_space reset (sequence 0) word space
  let event := Event.reload image nextImage (.free logical offset) reset .warm (sequence 0) word loading room
  let trace : Trace before image (.free logical offset) .available (reset.pins ++ loading.pins)
      loading.after nextImage
      (.free (LogicalSession.resetLogical logical) (loading.after.controller.core .transfer).toNat) .available := by
    simpa only [Cursor.advance,Cursor.logical,List.append_nil] using Trace.cons event .nil
  have result := GenericUpload.Serial.warm_install nextImage.image reset (sequence 0) word loading space
  exact ⟨reset,loading,trace,trace.preserves initial,result.2.2.2.1,result.2.2.2.2.1⟩

end Pinwheel.Hardware.Buffered.GenericWireSession
