import Pinwheel.Hardware.Buffered.I2cTimingLogicalWire

/-! Full cold/upload/runtime composition for every Fin 256 timing field,
including actual request/read cuts, reloads, retries and deselected padding. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming.LogicalWire
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames
open GenericLogicalWire (Cursor)
set_option maxRecDepth 4096

def Event.abortRequest (duration budget : Fin 256) (request : SerialWire.Request before)
    (cursor : Cursor) (count : Nat) (coldPin : SerialPackage.Pins)
    (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    let rawPrefix := request.pins.take count
    let loading := SerialUpload.concreteLoading duration budget ((before.run rawPrefix).step coldPin)
      (Buffered.SerialUpload.cold_available _ coldPin cold idle) sequence raw
    Event duration budget before cursor .available (rawPrefix ++ coldPin :: loading.pins) loading.after
      (.free (LogicalSession.resetLogical (cursor.advance (p := source duration budget) rawPrefix).logical)
        (loading.after.controller.core .transfer).toNat) .available :=
  .coldAbort cursor .available (request.pins.take count) (request.quiet_prefix count)
    coldPin cold idle _

def Event.abortRead (duration budget : Fin 256) (attempt : SerialSourceSession.Attempt before)
    (cursor : Cursor) (count : Nat) (coldPin : SerialPackage.Pins)
    (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    let rawPrefix := attempt.pins.take count
    let loading := SerialUpload.concreteLoading duration budget ((before.run rawPrefix).step coldPin)
      (Buffered.SerialUpload.cold_available _ coldPin cold idle) sequence raw
    Event duration budget before cursor .ready (rawPrefix ++ coldPin :: loading.pins) loading.after
      (.free (LogicalSession.resetLogical (cursor.advance (p := source duration budget) rawPrefix).logical)
        (loading.after.controller.core .transfer).toNat) .available :=
  .coldAbort cursor .ready (attempt.pins.take count) (attempt.quiet_prefix count)
    coldPin cold idle _

theorem initialized_session (duration budget : Fin 256) (before : SerialPackage.State)
    (previous : Transfer.State) (coldPin : SerialPackage.Pins)
    (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : SerialUpload.Loading duration budget (before.step coldPin))
    (trace : Trace duration budget loading.after
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after final finalFrontend) :
    before.run ((coldPin :: loading.pins) ++ pins) = after ∧
      Transfer.step capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      Valid duration budget after final finalFrontend ∧ trace.Observed := by
  obtain ⟨installed,phase,retained,_,_,available,run⟩ :=
    SerialUpload.cold_install duration budget before coldPin cold idle loading
  have aligned : LogicalSession.Aligned loading.after.controller
      (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat :=
    ⟨rfl,phase,retained,rfl⟩
  have result := trace.session ⟨available,installed,aligned⟩
  refine ⟨?_,rfl,result.2⟩
  change List.foldl SerialPackage.State.step before ((coldPin :: loading.pins) ++ pins) = after
  rw [List.foldl_append]
  exact (congrArg (fun current => current.run pins) run).trans result.1

theorem initialized_exists (duration budget : Fin 256) (before : SerialPackage.State)
    (previous : Transfer.State) (coldPin : SerialPackage.Pins)
    (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    ∃ loading : SerialUpload.Loading duration budget (before.step coldPin),
      before.run (coldPin :: loading.pins) = loading.after ∧
      Valid duration budget loading.after
        (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat) .available := by
  obtain ⟨loading,installed,phase,retained,_,_,available,run⟩ :=
    SerialUpload.initialized_exists duration budget before coldPin cold idle sequence raw
  exact ⟨loading,run,available,installed,⟨rfl,phase,retained,rfl⟩⟩

theorem Trace.reusable {duration budget}
    (trace : Trace duration budget before (.free logical offset) .available pins
      after (.free finalLogical finalOffset) .available)
    (available : Available before.record)
    (installed : InstalledSram (source duration budget) (layout duration budget) before.controller)
    (aligned : LogicalSession.Aligned before.controller logical offset) :
    before.run pins = after ∧ Available after.record ∧
      InstalledSram (source duration budget) (layout duration budget) after.controller ∧
      LogicalSession.Aligned after.controller finalLogical finalOffset ∧ trace.Observed := by
  have result := trace.session ⟨available,installed,aligned⟩
  exact ⟨result.1,result.2.1.1,result.2.1.2.1,result.2.1.2.2,result.2.2⟩

end Pinwheel.Hardware.Buffered.I2cTiming.LogicalWire
