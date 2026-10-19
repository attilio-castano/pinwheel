import Pinwheel.Hardware.Buffered.ArtifactPackageWiringSession
import Pinwheel.Hardware.Buffered.I2cTimingSerialWitness

/-! Timing-independent artifact transport.  Exact interpreted wrapper and
component certificates plus the explicit digital SRAM law lift every timing
pair's initialized carried wire session; no runtime testing premise is used. -/
namespace Pinwheel.Hardware.Buffered.ArtifactPackageWiringSession
open Pinwheel.Hardware Pinwheel.Program

theorem Certified.timing_initialized_session {M : Type} (wrapper : Certified)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (duration budget : Fin 256)
    (before : ArtifactPackage.State M) (previous : Transfer.State)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : I2cTiming.SerialUpload.Loading duration budget ((before.view memory).step coldPin))
    (trace : I2cTiming.LogicalWire.Trace duration budget loading.after
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after final finalFrontend) :
    (wrapper.run components memory before ((coldPin :: loading.pins) ++ pins)).view memory = after ∧
      Transfer.step Refinement.capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      I2cTiming.LogicalWire.Valid duration budget after final finalFrontend ∧ trace.Observed := by
  have result := I2cTiming.LogicalWire.initialized_session duration budget (before.view memory)
    previous coldPin cold idle loading trace
  exact ⟨(wrapper.view_run correct memory before _).trans result.1,result.2⟩

theorem Certified.timing_two_fused_rounds {M : Type} (wrapper : Certified)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (duration budget : Fin 256)
    (before : ArtifactPackage.State M) (previous : Transfer.State)
    (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ loading : I2cTiming.SerialUpload.Loading duration budget ((before.view memory).step pin),
      ∃ first : GenericLogicalWire.Witness.LogicalRound
        (p := I2cTiming.source duration budget) (layout := I2cTiming.layout duration budget)
        loading.after (LogicalSession.resetLogical previous) 0,
      ∃ second : GenericLogicalWire.Witness.LogicalRound
        (p := I2cTiming.source duration budget) (layout := I2cTiming.layout duration budget)
        first.after first.finalLogical 0,
      ∃ trace : I2cTiming.LogicalWire.Trace duration budget loading.after
        (.free (LogicalSession.resetLogical previous) 0) .available
        (first.pins ++ second.pins) second.after (.free second.finalLogical 0) .available,
      (wrapper.run components memory before ((pin :: loading.pins) ++ (first.pins ++ second.pins))).view memory =
        second.after ∧
      I2cTiming.LogicalWire.Valid duration budget second.after (.free second.finalLogical 0) .available ∧
      second.finalLogical.epoch = previous.epoch + 1 ∧ second.finalLogical.nextSequence = 3 ∧
      second.after.controller.core .generation = 1 ∧ second.after.controller.core .transfer = 2 ∧ trace.Observed := by
  obtain ⟨loading,first,second,trace,run,valid,epoch,sequence,generation,transfer,observed⟩ :=
    I2cTiming.SerialWitness.initialized_two_fused_rounds duration budget (before.view memory) previous pin cold idle
  exact ⟨loading,first,second,trace,(wrapper.view_run correct memory before _).trans run,
    valid,epoch,sequence,generation,transfer,observed⟩

end Pinwheel.Hardware.Buffered.ArtifactPackageWiringSession
