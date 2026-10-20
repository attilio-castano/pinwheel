import Pinwheel.Hardware.Buffered.SerialSourceSession
import Pinwheel.Hardware.Buffered.SerialUploadReset

/-! One actual sampled-pin recurrence from cold initialization or a wire reset,
through all 67 source-derived loader transactions, into arbitrary source wire
sessions. Initial SRAM cells and Q remain arbitrary. -/
namespace Pinwheel.Hardware.Buffered.SerialInitializedSession
open Pinwheel.Hardware Serial.Frames SerialSourceSession

private theorem append_run (before middle after : SerialPackage.State)
    (first rest : List SerialPackage.Pins) (prefixRun : before.run first = middle)
    (suffix : middle.run rest = after) : before.run (first ++ rest) = after := by
  change List.foldl SerialPackage.State.step before (first ++ rest) = after
  rw [List.foldl_append]
  exact (congrArg (fun current => current.run rest) prefixRun).trans suffix

theorem initialized_session (before : SerialPackage.State) (coldPin : SerialPackage.Pins)
    (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : SerialUpload.Loading (before.step coldPin))
    (trace : Trace I2cSource.source loading.after .free .available pins after .free .available) :
    before.run ((coldPin :: loading.pins) ++ pins) = after ∧
      Available after.record ∧
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout after.controller ∧
      SerialSourceRelease.Free after.controller ∧ trace.Observed := by
  obtain ⟨installed,phase,retained,_,_,available,run⟩ :=
    SerialUpload.cold_install before coldPin cold idle loading
  have session := trace.session available installed ⟨phase,retained⟩
  exact ⟨append_run before loading.after after _ _ run session.1,session.2⟩

theorem wire_cold_session (reset : SerialWire.Transaction before) (sequence : BitVec 16)
    (word : reset.request.word = SerialUpload.ResetKind.cold.word sequence)
    (loading : SerialUpload.Loading reset.after)
    (trace : Trace I2cSource.source loading.after .free .available pins after .free .available) :
    before.run ((reset.pins ++ loading.pins) ++ pins) = after ∧
      Available after.record ∧
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout after.controller ∧
      SerialSourceRelease.Free after.controller ∧ trace.Observed := by
  obtain ⟨installed,phase,retained,_,_,available,run⟩ :=
    SerialUpload.wire_cold_install reset sequence word loading
  have session := trace.session available installed ⟨phase,retained⟩
  exact ⟨append_run before loading.after after _ _ run session.1,session.2⟩

theorem wire_warm_session (reset : SerialWire.Transaction before) (sequence : BitVec 16)
    (word : reset.request.word = SerialUpload.ResetKind.warm.word sequence)
    (loading : SerialUpload.Loading reset.after)
    (space : (before.controller.core .generation).toNat ≤ 65533)
    (trace : Trace I2cSource.source loading.after .free .available pins after .free .available) :
    before.run ((reset.pins ++ loading.pins) ++ pins) = after ∧
      Available after.record ∧
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout after.controller ∧
      SerialSourceRelease.Free after.controller ∧ trace.Observed := by
  obtain ⟨installed,phase,retained,_,_,available,run⟩ :=
    SerialUpload.warm_install reset sequence word loading space
  have session := trace.session available installed ⟨phase,retained⟩
  exact ⟨append_run before loading.after after _ _ run session.1,session.2⟩

end Pinwheel.Hardware.Buffered.SerialInitializedSession
