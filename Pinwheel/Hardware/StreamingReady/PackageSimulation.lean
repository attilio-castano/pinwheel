import Pinwheel.Hardware.StreamingReady.PublicPins

/-! Lift a core state relation through status feedback, the frontend, and
the certified stateless wrappers. -/
namespace Pinwheel.Hardware.StreamingReady.PackageSimulation
open Pinwheel.Hardware

abbrev CoreRelation (a : Nat) := Values (Core.Register a) → Values (Core.Register a) → Prop

structure Simulates (left right : Package.Components a) (R : CoreRelation a) : Prop where
  frontend : left.frontend = right.frontend
  step : ∀ i l r, R l r → R (left.core.step i l) (right.core.step i r)
  observe : ∀ i l r, R l r → @left.core.observe i l = @right.core.observe i r

def Related (R : CoreRelation a) (l r : Package.State a) : Prop :=
  (@l.frontend : Values Streaming.Frontend.Register) = @r.frontend ∧ R l.core r.core

variable {a : Nat} {left right : Package.Components a} {R : CoreRelation a}
  {l r : Package.State a} {tiny : TinyWiring.Description} {wiring : Wiring.Description}

theorem Simulates.coreInputs_eq (h : Simulates left right R) (p : Package.Pins)
    (rel : Related R l r) :
    @Streaming.Package.State.coreInputs a l left p = @Streaming.Package.State.coreInputs a r right p := by
  funext w port
  simp only [Streaming.Package.State.coreInputs, h.frontend, rel.1]

theorem Simulates.status_eq (h : Simulates left right R) (p : Package.Pins)
    (rel : Related R l r) :
    @Streaming.Package.State.status a l left p = @Streaming.Package.State.status a r right p := by
  unfold Streaming.Package.State.status
  rw [h.coreInputs_eq p rel]
  exact h.observe _ _ _ rel.2

theorem Simulates.package_step (h : Simulates left right R) (p : Package.Pins)
    (rel : Related R l r) : Related R (l.step left p) (r.step right p) := by
  refine ⟨?_, ?_⟩
  · simp only [Streaming.Package.State.step, Streaming.Package.State.frontendInputs,
      h.frontend, rel.1, h.status_eq p rel]
  · simp only [Streaming.Package.State.step, h.coreInputs_eq p rel]
    exact h.step _ _ _ rel.2

theorem Simulates.package_observe (h : Simulates left right R) (p : Package.Pins)
    (rel : Related R l r) :
    @Streaming.Package.State.observe a l left p = @Streaming.Package.State.observe a r right p := by
  funext w port
  cases port <;> simp only [Streaming.Package.State.observe, Streaming.Package.State.frontendInputs,
    h.frontend, rel.1, h.status_eq p rel]

theorem Simulates.physical_step (h : Simulates left right R)
    (ht : TinyWiring.Certificate a tiny) (hw : Wiring.Certificate a wiring)
    (p : TinyWiring.Pins) (rel : Related R l r) :
    Related R (tiny.step wiring left l p) (tiny.step wiring right r p) := by
  simp only [ht.step_eq hw]
  exact h.package_step _ rel

theorem Simulates.physical_observe (h : Simulates left right R)
    (ht : TinyWiring.Certificate a tiny) (hw : Wiring.Certificate a wiring)
    (p : TinyWiring.Pins) (rel : Related R l r) :
    tiny.observe wiring left l p = tiny.observe wiring right r p := by
  funext pad
  simp only [ht.observe_eq hw]
  exact congrArg (fun values => (TinyWiring.canonical a).pads p values pad) (h.package_observe _ rel)

theorem Simulates.physical_run (h : Simulates left right R)
    (ht : TinyWiring.Certificate a tiny) (hw : Wiring.Certificate a wiring)
    (pins : List TinyWiring.Pins) (rel : Related R l r) :
    Related R (pins.foldl (tiny.step wiring left) l) (pins.foldl (tiny.step wiring right) r) := by
  induction pins generalizing l r with
  | nil => exact rel
  | cons pin rest ih => exact ih (h.physical_step ht hw pin rel)

def drive (tiny : TinyWiring.Description) (wiring : Wiring.Description) (c : Package.Components a)
    (s : Package.State a) : Pinwheel.Program.StreamingReady.Pins :=
  let out := tiny.observe wiring c s (PublicPins.embed {})
  ⟨(out .uio).extractLsb' 0 3, (out .oe).extractLsb' 0 3⟩

def driveTrace (tiny : TinyWiring.Description) (wiring : Wiring.Description)
    (c : Package.Components a) (s : Package.State a) :
    List Pinwheel.Program.StreamingReady.Session.Pins → List Pinwheel.Program.StreamingReady.Pins
  | [] => [drive tiny wiring c s]
  | p :: rest => drive tiny wiring c s ::
      driveTrace tiny wiring c (tiny.step wiring c s (PublicPins.embed p)) rest

theorem Simulates.driveTrace_eq (h : Simulates left right R)
    (ht : TinyWiring.Certificate a tiny) (hw : Wiring.Certificate a wiring)
    (pins : List Pinwheel.Program.StreamingReady.Session.Pins) (rel : Related R l r) :
    driveTrace tiny wiring left l pins = driveTrace tiny wiring right r pins := by
  induction pins generalizing l r with
  | nil => simp only [driveTrace, drive, h.physical_observe ht hw _ rel]
  | cons p rest ih =>
    simp only [driveTrace, drive, h.physical_observe ht hw _ rel,
      ih (h.physical_step ht hw (PublicPins.embed p) rel)]

theorem driveTrace_typed (ht : TinyWiring.Certificate a tiny) (hw : Wiring.Certificate a wiring)
    (s : Package.State a) (pins : List Pinwheel.Program.StreamingReady.Session.Pins) :
    driveTrace tiny wiring (Package.Components.typed a) s pins = PublicPins.driveTrace s pins := by
  have canonical : Wiring.Certificate a (Wiring.canonical a) := by
    constructor <;> intros <;> rfl
  have observed (s : Package.State a) :
      drive tiny wiring (Package.Components.typed a) s = PublicPins.drive s := by
    unfold drive PublicPins.drive
    have tinyCanonical : TinyWiring.Certificate a (TinyWiring.canonical a) := by
      constructor <;> intros <;> rfl
    simp only [ht.observe_eq hw, tinyCanonical.observe_eq canonical]
  induction pins generalizing s with
  | nil => simp only [driveTrace, PublicPins.driveTrace, observed]
  | cons p rest ih =>
    simp only [driveTrace, PublicPins.driveTrace, observed, ht.step_eq hw, PublicPins.engine_embed,
      PublicPins.step_eq, ih]

end Pinwheel.Hardware.StreamingReady.PackageSimulation
