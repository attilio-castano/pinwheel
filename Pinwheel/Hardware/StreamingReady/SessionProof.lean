import Pinwheel.Hardware.StreamingReady.InitializedCustody
import Pinwheel.Hardware.StreamingReady.PublicPins

/-! Session facts shared by protocols over the sampled-ready engine. A client
can advance the reached state one segment at a time and discharge RELEASE
with the same custody proof. -/
namespace Pinwheel.Hardware.StreamingReady.SessionProof
open Pinwheel.Program.StreamingReady
open InitializedCustody

/-- An admitted START gives the initial custody state and the engine start state. -/
structure Started (image : Compiled source idle) (actual : Package.State a)
    (s : Session.State a) (pin : Session.Pins) : Prop where
  reached : Reached image
    (actual.step (Package.Components.typed a) (SessionCorrespondence.pins pin))
    (s.step image.program false pin) {}
  coreStart : (s.step image.program false pin).core =
    s.core.start image.program (s.command pin).runtime

theorem start (image : Compiled source idle) (actualBoot : Package.State a)
    (boot : Session.State a) (initialized : BootCorrespondence.Initialized image actualBoot boot)
    (before : List Session.Pins) (pin : Session.Pins) (ha : a ≤ 3)
    (beforeRuntime : Session.RuntimeTrace image.program false boot before)
    (runtime : Session.RuntimeInput (boot.run image.program false before) pin)
    (admitted : ActualStart
      (actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)) pin) :
    Started image (actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins))
      (boot.run image.program false before) pin := by
  have initial := started_run image actualBoot boot initialized before pin [] ha
    beforeRuntime runtime admitted trivial
  refine ⟨initial, ?_⟩
  rw [initialized_run_eq image actualBoot boot initialized before ha beforeRuntime] at admitted
  exact (boot.run image.program false before).core_admitted_start image.program false pin runtime
    (start_source (Initialization.compiledImage image) _ pin runtime admitted)

/-- The end state retains custody, and the wire observations are given by the
    source execution of this segment. -/
structure Segment (image : Compiled source idle) (actual : Package.State a)
    (s : Session.State a) (trace : BitTrace) (pins : List Session.Pins) : Prop where
  reached : Reached image
    (actual.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins))
    (s.run image.program false pins) (s.traceRun image.program false trace pins)
  wire : PublicPins.driveTrace actual pins =
    pinTrace image.program s.core (s.runtimeInputs image.program false pins)

theorem advance {a : Nat} {actual : Package.State a} {s : Session.State a}
    (reached : Reached image actual s trace) (pins : List Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace image.program false s pins) :
    Segment image actual s trace pins := by
  refine ⟨reached.run pins ha runtime, ?_⟩
  rw [reached.package]
  simpa only [compiled_pending] using PublicPins.driveTrace_eq (Initialization.compiledImage image)
    s pins ha (by simpa only [compiled_pending] using runtime) reached.custody.structural

/-- The accepted and captured bits are fully accounted for at an admitted
    RELEASE. The retained phase allows callers to distinguish success and fault. -/
structure Released (s : Session.State a) (trace : BitTrace) : Prop where
  accepted : trace.accepted = trace.consumed
  exported : trace.captured = trace.exported
  ackOffset : trace.exported.length = s.host.ackOffset.toNat
  emptyExport : s.host.exportBits.toNat = 0
  retained : s.core.phase.retained = true

theorem release {a : Nat} {actual : Package.State a} {s : Session.State a}
    (reached : Reached image actual s trace) (pin : Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeInput s pin) (admitted : ActualRelease actual pin) :
    Released s trace := by
  rw [reached.package] at admitted
  have accepted := release_source (Initialization.compiledImage image) s pin ha runtime admitted
  obtain ⟨tx, rx, ack, empty⟩ := reached.custody.release_all_bits s pin trace accepted.1 accepted.2
  have ready := accepted.2
  simp only [State.canRelease, Bool.and_eq_true] at ready
  exact ⟨tx, rx, ack, empty, ready.1.1⟩

end Pinwheel.Hardware.StreamingReady.SessionProof
