import Pinwheel.Hardware.Buffered.GenericWireSession

/-! From arbitrary digital preboot state to an arbitrary heterogeneous source
session, including frame-interior aborts and concrete image replacement. -/
namespace Pinwheel.Hardware.Buffered.GenericWireSession
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames
open GenericLogicalWire (Cursor)
set_option maxRecDepth 4096

def Event.abortRequest (image nextImage : ProgramImage) (request : SerialWire.Request before)
    (cursor : Cursor) (count : Nat) (coldPin : SerialPackage.Pins)
    (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    let rawPrefix := request.pins.take count
    let loading := GenericUpload.Serial.concreteLoading nextImage.image ((before.run rawPrefix).step coldPin)
      (Buffered.SerialUpload.cold_available _ coldPin cold idle) sequence raw
    Event before image cursor .available (rawPrefix ++ coldPin :: loading.pins) loading.after nextImage
      (.free (LogicalSession.resetLogical (cursor.advance (p := image.program) rawPrefix).logical)
        (loading.after.controller.core .transfer).toNat) .available :=
  .coldAbort image nextImage cursor .available (request.pins.take count) (request.quiet_prefix count)
    coldPin cold idle _

def Event.abortRead (image nextImage : ProgramImage) (attempt : SerialSourceSession.Attempt before)
    (cursor : Cursor) (count : Nat) (coldPin : SerialPackage.Pins)
    (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    let rawPrefix := attempt.pins.take count
    let loading := GenericUpload.Serial.concreteLoading nextImage.image ((before.run rawPrefix).step coldPin)
      (Buffered.SerialUpload.cold_available _ coldPin cold idle) sequence raw
    Event before image cursor .ready (rawPrefix ++ coldPin :: loading.pins) loading.after nextImage
      (.free (LogicalSession.resetLogical (cursor.advance (p := image.program) rawPrefix).logical)
        (loading.after.controller.core .transfer).toNat) .available :=
  .coldAbort image nextImage cursor .ready (attempt.pins.take count) (attempt.quiet_prefix count)
    coldPin cold idle _

theorem initialized_session (image : ProgramImage) (before : SerialPackage.State)
    (previous : Transfer.State) (coldPin : SerialPackage.Pins)
    (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : GenericUpload.Serial.Loading image.image (before.step coldPin))
    (trace : Trace loading.after image
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after finalImage final finalFrontend) :
    before.run ((coldPin :: loading.pins) ++ pins) = after ∧
      Transfer.step capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      Valid finalImage after final finalFrontend ∧ trace.Observed := by
  obtain ⟨installed,phase,retained,_,_,available,run⟩ :=
    GenericUpload.Serial.cold_install image.image before coldPin cold idle loading
  have aligned : LogicalSession.Aligned loading.after.controller
      (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat :=
    ⟨rfl,phase,retained,rfl⟩
  have result := trace.session ⟨available,installed,aligned⟩
  refine ⟨?_,rfl,result.2⟩
  change List.foldl SerialPackage.State.step before ((coldPin :: loading.pins) ++ pins) = after
  rw [List.foldl_append]
  exact (congrArg (fun current => current.run pins) run).trans result.1

theorem initialized_exists (image : ProgramImage) (before : SerialPackage.State)
    (previous : Transfer.State) (coldPin : SerialPackage.Pins)
    (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    ∃ loading : GenericUpload.Serial.Loading image.image (before.step coldPin),
      before.run (coldPin :: loading.pins) = loading.after ∧
      Valid image loading.after
        (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat) .available := by
  obtain ⟨loading,installed,phase,retained,_,_,available,run⟩ :=
    GenericUpload.Serial.initialized_exists image.image before coldPin cold idle sequence raw
  exact ⟨loading,run,available,installed,⟨rfl,phase,retained,rfl⟩⟩

theorem Trace.reusable (trace : Trace before image (.free logical offset) .available pins
      after finalImage (.free finalLogical finalOffset) .available)
    (available : Available before.record)
    (installed : InstalledSram image.program image.layout before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset) :
    before.run pins = after ∧ Available after.record ∧
      InstalledSram finalImage.program finalImage.layout after.controller ∧
      LogicalSession.Aligned after.controller finalLogical finalOffset ∧ trace.Observed := by
  have result := trace.session ⟨available,installed,aligned⟩
  exact ⟨result.1,result.2.1.1,result.2.1.2.1,result.2.1.2.2,result.2.2⟩

end Pinwheel.Hardware.Buffered.GenericWireSession
