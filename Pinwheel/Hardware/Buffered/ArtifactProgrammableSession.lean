import Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutWiringSession
import Pinwheel.Hardware.Buffered.GenericWireSessionInitialized

/-! Data-independent artifact transport for arbitrary statically certified
shared-dictionary source images and heterogeneous reset/reload sessions. -/
namespace Pinwheel.Hardware.Buffered.ArtifactPackageWiringSession
open Pinwheel.Hardware Pinwheel.Program

theorem Certified.programmable_initialized_session {M : Type} (wrapper : Certified)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (image : GenericWireSession.ProgramImage)
    (before : ArtifactPackage.State M) (previous : Transfer.State)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : GenericUpload.Serial.Loading image.image ((before.view memory).step coldPin))
    (trace : GenericWireSession.Trace loading.after image
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after finalImage final finalFrontend) :
    (wrapper.run components memory before ((coldPin :: loading.pins) ++ pins)).view memory = after ∧
      Transfer.step Refinement.capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      GenericWireSession.Valid finalImage after final finalFrontend ∧ trace.Observed := by
  have result := GenericWireSession.initialized_session image (before.view memory) previous
    coldPin cold idle loading trace
  exact ⟨(wrapper.view_run correct memory before _).trans result.1,result.2⟩

end Pinwheel.Hardware.Buffered.ArtifactPackageWiringSession

namespace Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutWiringSession
open Pinwheel.Hardware Pinwheel.Program

theorem Certified.programmable_initialized_session {M : Type} (wrapper : Certified)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (image : GenericWireSession.ProgramImage)
    (before : ArtifactPackage.State M) (previous : Transfer.State)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : GenericUpload.Serial.Loading image.image ((before.view memory).step coldPin))
    (trace : GenericWireSession.Trace loading.after image
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after finalImage final finalFrontend) :
    (wrapper.run components memory before
      (((coldPin :: loading.pins) ++ pins).map ArtifactTinyTapeout.encode)).view memory = after ∧
      Transfer.step Refinement.capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      GenericWireSession.Valid finalImage after final finalFrontend ∧ trace.Observed := by
  have result := GenericWireSession.initialized_session image (before.view memory) previous
    coldPin cold idle loading trace
  exact ⟨(wrapper.encoded_view_run correct memory before _).trans result.1,result.2⟩

end Pinwheel.Hardware.Buffered.ArtifactTinyTapeoutWiringSession
