import Pinwheel.Hardware.Buffered.ArtifactPackageMemory
import Pinwheel.Hardware.Buffered.ArtifactPackageSession

/-! A wrapper session requires both the interpreted connection certificate and
the complete memory-wrapper inventory. Exact emitted component equations and
the caller's digital SRAM law remain explicit independent inputs. -/
namespace Pinwheel.Hardware.Buffered.ArtifactPackageWiringSession
open Pinwheel.Hardware Pinwheel.Program

structure Certified where
  wiring : ArtifactPackageWiring.Wiring
  correct : ArtifactPackageWiring.Certificate wiring
  memoryInventory : ArtifactPackageMemory.Inventory
  memoryCorrect : ArtifactPackageMemory.Certificate memoryInventory

def Certified.run {M : Type} (wrapper : Certified) (components : ArtifactPackage.Components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M)
    (pins : List SerialPackage.Pins) : ArtifactPackage.State M :=
  wrapper.wiring.run components memory s pins

theorem Certified.view_run {M : Type} (wrapper : Certified)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (s : ArtifactPackage.State M)
    (pins : List SerialPackage.Pins) :
    (wrapper.run components memory s pins).view memory = (s.view memory).run pins :=
  wrapper.correct.view_run correct memory s pins

theorem Certified.initialized_session {M : Type} (wrapper : Certified)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (before : ArtifactPackage.State M) (previous : Transfer.State)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : SerialUpload.Loading ((before.view memory).step coldPin))
    (trace : LogicalWire.Interrupted.Trace loading.after
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after final finalFrontend) :
    (wrapper.run components memory before ((coldPin :: loading.pins) ++ pins)).view memory = after ∧
      Transfer.step Refinement.capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      LogicalWire.Valid after final finalFrontend ∧ trace.Observed := by
  have result := LogicalWire.Interrupted.initialized_session (before.view memory) previous
    coldPin cold idle loading trace
  exact ⟨(wrapper.view_run correct memory before _).trans result.1, result.2⟩
  done

theorem Certified.initialized_two_logical_rounds {M : Type} (wrapper : Certified)
    {components : ArtifactPackage.Components} (correct : ArtifactPackage.Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (before : ArtifactPackage.State M) (previous : Transfer.State)
    (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ loading : SerialUpload.Loading ((before.view memory).step pin),
      ∃ first : SerialSessionWitness.LogicalRound loading.after (LogicalSession.resetLogical previous) 0,
      ∃ second : SerialSessionWitness.LogicalRound first.after first.finalLogical 0,
      ∃ trace : LogicalWire.Trace loading.after (.free (LogicalSession.resetLogical previous) 0) .available
        (first.pins ++ second.pins) second.after (.free second.finalLogical 0) .available,
      (wrapper.run components memory before ((pin :: loading.pins) ++ (first.pins ++ second.pins))).view memory =
          second.after ∧
      LogicalWire.Valid second.after (.free second.finalLogical 0) .available ∧
      second.finalLogical.epoch = previous.epoch + 1 ∧ second.finalLogical.nextSequence = 3 ∧
      second.after.controller.core .generation = 1 ∧ second.after.controller.core .transfer = 2 ∧
      trace.Observed := by
  obtain ⟨loading,first,second,trace,run,valid,epoch,sequence,generation,transfer,observed⟩ :=
    SerialSessionWitness.initialized_two_logical_rounds (before.view memory) previous pin cold idle
  exact ⟨loading,first,second,trace,(wrapper.view_run correct memory before _).trans run,
    valid,epoch,sequence,generation,transfer,observed⟩
  done

end Pinwheel.Hardware.Buffered.ArtifactPackageWiringSession
