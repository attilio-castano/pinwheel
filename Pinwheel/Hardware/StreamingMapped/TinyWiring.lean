import Pinwheel.Hardware.StreamingReady.TinyWiring
import Pinwheel.Hardware.StreamingMapped.Word

namespace Pinwheel.Hardware.StreamingMapped.TinyWiring
open Pinwheel.Hardware.StreamingReady

/-- Functions reconstructed from actual mapped pad and package-boundary gates.
The event clock is a separate direct-wire obligation in the artifact reader. -/
structure Backend where
  enginePins : StreamingReady.TinyWiring.Pins → Package.Pins
  pads : StreamingReady.TinyWiring.Pins → Values Package.Output →
    StreamingReady.TinyWiring.Pad → BitVec 8

structure Backend.Correct (a : Nat) (backend : Backend) : Prop where
  enginePins : ∀ p, backend.enginePins p =
    StreamingReady.TinyWiring.Description.enginePins (StreamingReady.TinyWiring.canonical a) p
  pads : ∀ p engine pad, backend.pads p engine pad =
    StreamingReady.TinyWiring.Description.pads (StreamingReady.TinyWiring.canonical a) p engine pad

def Backend.step (backend : Backend) (wiring : Wiring.Description) (components : Package.Components a)
    (state : Package.State a) (pins : StreamingReady.TinyWiring.Pins) : Package.State a :=
  wiring.step components state (backend.enginePins pins)

def Backend.observe (backend : Backend) (wiring : Wiring.Description) (components : Package.Components a)
    (state : Package.State a) (pins : StreamingReady.TinyWiring.Pins) :
    StreamingReady.TinyWiring.Pad → BitVec 8 :=
  backend.pads pins (wiring.observe components state (backend.enginePins pins))

theorem Backend.Correct.step_eq {backend : Backend} (proof : backend.Correct a)
    {wiring : Wiring.Description} (wireProof : Wiring.Certificate a wiring)
    (components : Package.Components a) (state : Package.State a)
    (pins : StreamingReady.TinyWiring.Pins) :
    backend.step wiring components state pins = state.step components
      (StreamingReady.TinyWiring.Description.enginePins (StreamingReady.TinyWiring.canonical a) pins) := by
  simp only [Backend.step,proof.enginePins,wireProof.step_eq]

theorem Backend.Correct.observe_eq {backend : Backend} (proof : backend.Correct a)
    {wiring : Wiring.Description} (wireProof : Wiring.Certificate a wiring)
    (components : Package.Components a) (state : Package.State a)
    (pins : StreamingReady.TinyWiring.Pins) (pad : StreamingReady.TinyWiring.Pad) :
    backend.observe wiring components state pins pad =
      StreamingReady.TinyWiring.Description.pads (StreamingReady.TinyWiring.canonical a) pins
        (state.observe components
          (StreamingReady.TinyWiring.Description.enginePins (StreamingReady.TinyWiring.canonical a) pins)) pad := by
  simp only [Backend.observe,proof.enginePins,proof.pads]
  have ports : (wiring.observe components state
      (StreamingReady.TinyWiring.Description.enginePins (StreamingReady.TinyWiring.canonical a) pins) :
      Values Package.Output) = (state.observe components
      (StreamingReady.TinyWiring.Description.enginePins (StreamingReady.TinyWiring.canonical a) pins) :
      Values Package.Output) :=
    funext fun _ => funext fun port => wireProof.observe_eq components state _ port
  rw [ports]

end Pinwheel.Hardware.StreamingMapped.TinyWiring
