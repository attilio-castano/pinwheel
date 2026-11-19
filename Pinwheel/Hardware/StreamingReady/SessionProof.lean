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
    (s : Session.State a) (pin : Session.Pins)
    (rep : SourceRefinement.Image image.program := Initialization.compiledImage image) : Prop where
  reached : Reached image
    (actual.step (Package.Components.typed a) (SessionCorrespondence.pins pin))
    (s.step image.program false pin) {} rep
  coreStart : (s.step image.program false pin).core =
    s.core.start image.program (s.command pin).runtime

theorem start_from (image : Compiled source idle) (rep : SourceRefinement.Image image.program)
    (actualBoot : Package.State a) (boot : Session.State a)
    (initialized : BootCorrespondence.Ready image rep actualBoot boot)
    (before : List Session.Pins) (pin : Session.Pins) (ha : a ≤ 3)
    (beforeRuntime : Session.RuntimeTrace image.program false boot before)
    (runtime : Session.RuntimeInput (boot.run image.program false before) pin)
    (admitted : ActualStart
      (actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)) pin) :
    Started image (actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins))
      (boot.run image.program false before) pin rep := by
  have initial := started_run_from image rep actualBoot boot initialized.package initialized.pending
    initialized.structural initialized.phase before pin [] ha beforeRuntime runtime admitted trivial
  refine ⟨initial, ?_⟩
  rw [ready_run_eq image.program rep actualBoot boot initialized.package initialized.pending
    initialized.structural before ha beforeRuntime] at admitted
  exact (boot.run image.program false before).core_admitted_start image.program false pin runtime
    (start_source rep _ pin runtime admitted)

theorem start (image : Compiled source idle) (actualBoot : Package.State a)
    (boot : Session.State a) (initialized : BootCorrespondence.Initialized image actualBoot boot)
    (before : List Session.Pins) (pin : Session.Pins) (ha : a ≤ 3)
    (beforeRuntime : Session.RuntimeTrace image.program false boot before)
    (runtime : Session.RuntimeInput (boot.run image.program false before) pin)
    (admitted : ActualStart
      (actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)) pin) :
    Started image (actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins))
      (boot.run image.program false before) pin :=
  start_from image (Initialization.compiledImage image) actualBoot boot initialized.asReady
    before pin ha beforeRuntime runtime admitted

/-- The end state retains custody, and the wire observations are given by the
    source execution of this segment. -/
structure Segment (image : Compiled source idle) (actual : Package.State a)
    (s : Session.State a) (trace : BitTrace) (pins : List Session.Pins)
    (rep : SourceRefinement.Image image.program := Initialization.compiledImage image) : Prop where
  reached : Reached image
    (actual.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins))
    (s.run image.program false pins) (s.traceRun image.program false trace pins) rep
  wire : PublicPins.driveTrace actual pins =
    pinTrace image.program s.core (s.runtimeInputs image.program false pins)

variable {rows : List Instruction} {idle : Pins} {image : Compiled rows idle}
  {rep : SourceRefinement.Image image.program}

theorem advance {a : Nat} {actual : Package.State a} {s : Session.State a}
    (reached : Reached image actual s trace rep) (pins : List Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace image.program false s pins) :
    Segment image actual s trace pins rep := by
  have pending : rep.pending.getLsbD 0 = false := by rw [reached.installed]; rfl
  refine ⟨reached.run pins ha runtime, ?_⟩
  rw [reached.package]
  simpa only [pending] using PublicPins.driveTrace_eq rep s pins ha
    (by simpa only [pending] using runtime) reached.custody.structural

/-- The accepted and captured bits are fully accounted for at an admitted
    RELEASE. The retained phase allows callers to distinguish success and fault. -/
structure Released (s : Session.State a) (trace : BitTrace) : Prop where
  accepted : trace.accepted = trace.consumed
  exported : trace.captured = trace.exported
  ackOffset : trace.exported.length = s.host.ackOffset.toNat
  emptyExport : s.host.exportBits.toNat = 0
  retained : s.core.phase.retained = true

theorem release {a : Nat} {actual : Package.State a} {s : Session.State a}
    (reached : Reached image actual s trace rep) (pin : Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeInput s pin) (admitted : ActualRelease actual pin) :
    Released s trace := by
  rw [reached.package] at admitted
  have accepted := release_source rep s pin ha runtime admitted
  obtain ⟨tx, rx, ack, empty⟩ := reached.custody.release_all_bits s pin trace accepted.1 accepted.2
  have ready := accepted.2
  simp only [State.canRelease, Bool.and_eq_true] at ready
  exact ⟨tx, rx, ack, empty, ready.1.1⟩

/-- The delivery edge of RELEASE preserves the installed image and owner
    counters and clears the old transfer. The host may still be sending the
    RELEASE reply, which a subsequent upload certificate can consume. -/
structure ReleasedCut (image : Compiled source idle) (actual : Package.State a)
    (s : Session.State a) (trace : BitTrace) (pin : Session.Pins)
    (rep : SourceRefinement.Image image.program := Initialization.compiledImage image) : Prop where
  accounted : Released s trace
  package : actual.step (Package.Components.typed a) (SessionCorrespondence.pins pin) =
    SessionCorrespondence.values rep (s.step image.program false pin)
  core : (s.step image.program false pin).core = s.core.release image.program (s.command pin).runtime
  free : (s.step image.program false pin).core.phase = .free
  drained : (s.step image.program false pin).core.drained = true
  structural : (s.step image.program false pin).core.Structural
  generation : (s.step image.program false pin).core.generation = s.core.generation
  transfer : (s.step image.program false pin).core.transfer = s.core.transfer
  exportData : (s.step image.program false pin).host.exportData = 0
  exportStart : (s.step image.program false pin).host.exportStart = 0
  exportBits : (s.step image.program false pin).host.exportBits = 0
  ackOffset : (s.step image.program false pin).host.ackOffset = 0

theorem release_to_free {a : Nat} {actual : Package.State a} {s : Session.State a}
    (reached : Reached image actual s trace rep) (pin : Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeInput s pin) (admitted : ActualRelease actual pin) :
    ReleasedCut image actual s trace pin rep := by
  have accepted := release_source rep s pin ha runtime (reached.package ▸ admitted)
  have core : (s.step image.program false pin).core = s.core.release image.program (s.command pin).runtime := by
    simp [Session.State.step, step, runtime.1, accepted.1, accepted.2]
  have next := reached.run [pin] ha ⟨runtime, trivial⟩
  have clear := s.accepted_clears false pin (Or.inr (by simp [accepted.1, accepted.2]))
  refine ⟨release reached pin ha runtime admitted, next.package, core, ?_, ?_, next.custody.structural,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [core]; rfl
  · rw [core]; rfl
  · rw [core]; rfl
  · rw [core]; rfl
  all_goals simp [Session.State.step, Pinwheel.Program.Streaming.Host.step,
    show (s.hostInput false pin).initialize = false from runtime.1, clear]

end Pinwheel.Hardware.StreamingReady.SessionProof
