import Pinwheel.Hardware.Buffered.ArtifactPackage
import Pinwheel.Hardware.Buffered.LogicalWireAbort
import Pinwheel.Hardware.Buffered.SerialSessionWitnessLogical

/-! Session substitution for independently interpreted components and explicit
digital memory laws. These theorems are conditional until the exact Verilog
frontend, controller and wrapper interpretation certificates are attached. -/
namespace Pinwheel.Hardware.Buffered.ArtifactPackage
open Pinwheel.Hardware Pinwheel.Program

theorem State.observe_run {M : Type} {components : Components} (correct : Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (before : State M)
    (pins : List SerialPackage.Pins) (pin : SerialPackage.Pins) (output : SerialPackage.Output w) :
    (before.run components memory pins).observe components memory pin output =
      ((before.view memory).run pins).observe pin output := by
  rw [State.view_observe correct, State.view_run correct]
  done

theorem initialized_session {M : Type} {components : Components} (correct : Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (before : State M) (previous : Transfer.State)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : SerialUpload.Loading ((before.view memory).step coldPin))
    (trace : LogicalWire.Interrupted.Trace loading.after
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after final finalFrontend) :
    (before.run components memory ((coldPin :: loading.pins) ++ pins)).view memory = after ∧
      Transfer.step Refinement.capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      LogicalWire.Valid after final finalFrontend ∧ trace.Observed := by
  have result := LogicalWire.Interrupted.initialized_session (before.view memory) previous
    coldPin cold idle loading trace
  exact ⟨(before.view_run correct memory _).trans result.1, result.2⟩
  done

theorem initialized_two_logical_rounds {M : Type} {components : Components} (correct : Correct components)
    (memory : Memory.SinglePort.Contract M 6 64) (before : State M) (previous : Transfer.State)
    (pin : SerialPackage.Pins) (cold : pin.cold = true) (idle : pin.csn = true) :
    ∃ loading : SerialUpload.Loading ((before.view memory).step pin),
      ∃ first : SerialSessionWitness.LogicalRound loading.after (LogicalSession.resetLogical previous) 0,
      ∃ second : SerialSessionWitness.LogicalRound first.after first.finalLogical 0,
      ∃ trace : LogicalWire.Trace loading.after (.free (LogicalSession.resetLogical previous) 0) .available
        (first.pins ++ second.pins) second.after (.free second.finalLogical 0) .available,
      (before.run components memory ((pin :: loading.pins) ++ (first.pins ++ second.pins))).view memory =
          second.after ∧
      LogicalWire.Valid second.after (.free second.finalLogical 0) .available ∧
      second.finalLogical.epoch = previous.epoch + 1 ∧ second.finalLogical.nextSequence = 3 ∧
      second.after.controller.core .generation = 1 ∧ second.after.controller.core .transfer = 2 ∧
      trace.Observed := by
  obtain ⟨loading,first,second,trace,run,valid,epoch,sequence,generation,transfer,observed⟩ :=
    SerialSessionWitness.initialized_two_logical_rounds (before.view memory) previous pin cold idle
  exact ⟨loading,first,second,trace,(before.view_run correct memory _).trans run,
    valid,epoch,sequence,generation,transfer,observed⟩
  done

end Pinwheel.Hardware.Buffered.ArtifactPackage
