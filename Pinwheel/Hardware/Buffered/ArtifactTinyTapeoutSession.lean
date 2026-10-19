import Pinwheel.Hardware.Buffered.ArtifactTinyTapeout

/-! Conditional transport of initialized wire sessions through the TinyTapeout
digital pin adapter. The encoded histories use no electrical timing premise;
each sample denotes one positive clock edge of the unchanged engine. -/
namespace Pinwheel.Hardware.Buffered.ArtifactTinyTapeout
open Pinwheel.Hardware Pinwheel.Program

theorem encoded_view_run {M : Type} {components : ArtifactPackage.Components}
    (correct : ArtifactPackage.Correct components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (pins : List SerialPackage.Pins) :
    (run components memory s (pins.map encode)).view memory = (s.view memory).run pins :=
  (congrArg (ArtifactPackage.State.view memory) (encoded_run components memory s pins)).trans
    (s.view_run correct memory pins)

theorem inactive_cold (p : Pins) (inactive : p.active = false) : p.enginePins.cold = true := by
  simp [Pins.enginePins, inactive]
  done

theorem inactive_edge_invalidates {M : Type} {components : ArtifactPackage.Components}
    (correct : ArtifactPackage.Correct components) (memory : Memory.SinglePort.Contract M 6 64)
    (s : ArtifactPackage.State M) (p : Pins) (inactive : p.active = false) :
    ((step components memory s p).view memory).controller.core .valid = 0 ∧
      ((step components memory s p).view memory).controller.core .retained = 0 ∧
      ((step components memory s p).view memory).controller.core .phase = 0 := by
  have cold := SerialUpload.cold_input (s.view memory) p.enginePins (inactive_cold p inactive)
  have resetting : Reactive.resetting.eval ((s.view memory).coreInputs p.enginePins)
      (s.view memory).controller.core = 1 := by
    simp [Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, cold]
  simpa only [view_step correct, SerialPackage.State.step] using
    Lifecycle.reset_ownership (s.view memory).controller ((s.view memory).coreInputs p.enginePins) resetting
  done

theorem initialized_session {M : Type} {components : ArtifactPackage.Components}
    (correct : ArtifactPackage.Correct components) (memory : Memory.SinglePort.Contract M 6 64)
    (before : ArtifactPackage.State M) (previous : Transfer.State)
    (coldPin : SerialPackage.Pins) (cold : coldPin.cold = true) (idle : coldPin.csn = true)
    (loading : SerialUpload.Loading ((before.view memory).step coldPin))
    (trace : LogicalWire.Interrupted.Trace loading.after
      (.free (LogicalSession.resetLogical previous) (loading.after.controller.core .transfer).toNat)
      .available pins after final finalFrontend) :
    (run components memory before (((coldPin :: loading.pins) ++ pins).map encode)).view memory = after ∧
      Transfer.step Refinement.capacity previous .reset = ⟨LogicalSession.resetLogical previous,.reset⟩ ∧
      LogicalWire.Valid after final finalFrontend ∧ trace.Observed := by
  have result := LogicalWire.Interrupted.initialized_session (before.view memory) previous
    coldPin cold idle loading trace
  exact ⟨(encoded_view_run correct memory before _).trans result.1, result.2⟩
  done

end Pinwheel.Hardware.Buffered.ArtifactTinyTapeout
