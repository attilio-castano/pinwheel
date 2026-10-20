import Pinwheel.Hardware.Buffered.LogicalWireSession

/-! The fused logical/wire session starts after an actual cold edge and all
67 source-derived wire uploads, with no supplied VALID, image equality, or
initial SRAM/Q premise. Indexed receipt data are public diagnostics; wire
OBSERVE has no identity authorization gate. Matching RELEASE is guarded. -/
namespace Pinwheel.Hardware.Buffered.LogicalWire
open Pinwheel.Hardware Pinwheel.Program Refinement Serial.Frames

private theorem append_run (before middle after : SerialPackage.State)
    (first rest : List SerialPackage.Pins) (firstRun : before.run first = middle)
    (restRun : middle.run rest = after) : before.run (first ++ rest) = after := by
  change List.foldl SerialPackage.State.step before (first ++ rest) = after
  rw [List.foldl_append]
  exact (congrArg (fun current => current.run rest) firstRun).trans restRun

theorem initialized_session (before : SerialPackage.State) (previous : Transfer.State)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : SerialUpload.Loading (before.step coldPin))
    (trace : Trace loading.after
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after final finalFrontend) :
    before.run ((coldPin :: loading.pins) ++ pins) = after ∧
      Transfer.step capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      Valid after final finalFrontend ∧ trace.Observed := by
  obtain ⟨installed,phase,retained,_,_,available,run⟩ :=
    SerialUpload.cold_install before coldPin cold idle loading
  have aligned : LogicalSession.Aligned loading.after.controller
      (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat :=
    ⟨rfl,phase,retained,rfl⟩
  have session := trace.session ⟨available,installed,aligned⟩
  exact ⟨append_run before loading.after after _ _ run session.1,rfl,session.2⟩

/-- The upload witness exists for every arbitrary digital preboot state. -/
theorem initialized_exists (before : SerialPackage.State) (previous : Transfer.State)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (sequence : Nat → BitVec 16 := BitVec.ofNat 16) (raw : BitVec 2 := 0) :
    ∃ loading : SerialUpload.Loading (before.step coldPin),
      before.run (coldPin :: loading.pins) = loading.after ∧
      Valid loading.after
        (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat) .available := by
  obtain ⟨loading,installed,phase,retained,_,_,available,run⟩ :=
    SerialUpload.initialized_exists before coldPin cold idle sequence raw
  exact ⟨loading,run,available,installed,⟨rfl,phase,retained,rfl⟩⟩

end Pinwheel.Hardware.Buffered.LogicalWire
