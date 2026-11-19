import Pinwheel.Hardware.StreamingReady.SessionCorrespondence

namespace Pinwheel.Hardware.StreamingReady
open Pinwheel.Hardware Pinwheel.Hardware.Streaming Pinwheel.Program.StreamingReady

/-- A delivered START for an older generation is rejected at the actual
    package. The owner stays free and the installed protocol keeps its drive. -/
theorem stale_start_rejected (rep : SourceRefinement.Image p) (actual : Package.State a)
    (s : Session.State a) (pin : Session.Pins) (ha : a ≤ 3)
    (represented : actual = SessionCorrespondence.values rep s) (structural : s.core.Structural)
    (free : s.core.phase = .free) (runtime : Session.RuntimeInput s pin)
    (start : (s.command pin).runtime.command = 3#4)
    (stale : (s.command pin).runtime.expectedGeneration ≠ s.core.generation) :
    let pins := SessionCorrespondence.pins pin
    let after := actual.step (Package.Components.typed a) pins
    actual.status (Package.Components.typed a) pins .rejected = 1#1 ∧
    after.core .phase = 0#3 ∧ after.core .generation = s.core.generation ∧
    after.core .transfer = s.core.transfer ∧
    after.core .levels = s.core.pins.levels ∧ after.core .enabled = s.core.pins.enabled := by
  dsimp only
  subst actual
  have disallowed : s.core.canStart (s.command pin).runtime = false := by
    simp [State.canStart, stale]
  refine ⟨?_, ?_⟩
  · have bridge := congrArg (fun status : Values Core.Output => status .rejected)
      (SessionCorrespondence.core_status rep s pin ha runtime structural)
    rw [bridge]
    simp [HostCorrespondence.statusValues, State.status, start, disallowed]
  · rw [SessionCorrespondence.step_correct rep s pin ha runtime structural]
    simp [SessionCorrespondence.values, SourceRefinement.values, Session.State.step,
      step, runtime.1, start, disallowed, clock, engine, free, Phase.code]

end Pinwheel.Hardware.StreamingReady
