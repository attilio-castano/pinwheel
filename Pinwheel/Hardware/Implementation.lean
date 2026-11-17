import Pinwheel.Hardware.Circuit
import Pinwheel.Hardware.Timed

namespace Pinwheel.Hardware

/-- The synchronous semantics shared by simulation and structural proofs. -/
def Circuit.component (c : Circuit I R O) :
    Timed.Component (Values I) (Values R) (Values O) :=
  ⟨c.step, c.observe⟩

/-- An implementation certificate leaves protocol contracts in the specification.
It works for any typed interface, including independently handshaken channels.
The encoding need not be injective: logical provenance can be erased in hardware.
The equations quantify over arbitrary physical input bits. -/
structure Implementation (c : Circuit I R O)
    (spec : Timed.Component (Values I) S (Values O)) where
  Valid : S → Prop
  encode : S → Values R
  preserved : ∀ i s, Valid s → Valid (spec.step i s)
  step_eq : ∀ i s, Valid s → ∀ {w} (r : R w),
    c.step i (encode s) r = encode (spec.step i s) r
  output_eq : ∀ i s, Valid s → ∀ {w} (o : O w),
    c.observe i (encode s) o = spec.observe i s o

variable {I R O : Nat → Type} {S : Type} {c : Circuit I R O}
  {spec : Timed.Component (Values I) S (Values O)}

def Implementation.refinement (p : Implementation c spec) :
    Timed.Refinement c.component spec where
  Rel := fun r s => p.Valid s ∧ @r = @p.encode s
  step := by
    intro i r s h
    rcases h with ⟨hv, rfl⟩
    exact ⟨p.preserved i s hv, funext fun w => funext fun r => p.step_eq i s hv r⟩
  observe := by
    intro i r s h
    rcases h with ⟨hv, rfl⟩
    exact funext fun w => funext fun o => p.output_eq i s hv o

theorem Implementation.trace_eq (p : Implementation c spec)
    (s : S) (h : p.Valid s) (inputs : List (Values I)) :
    c.component.trace (p.encode s) inputs = spec.trace s inputs :=
  p.refinement.trace_eq _ _ ⟨h, rfl⟩ inputs

/-- Recovery is a separate obligation: simulation from an encoded initial state
does not by itself prove that reset initializes arbitrary physical bits. -/
structure Implementation.Reset (p : Implementation c spec) (reset : I 1) where
  initial : S
  initial_valid : p.Valid initial
  reset_eq : ∀ (i : Values I) (r : Values R), i reset = 1 → ∀ {w} (q : R w),
    c.step i r q = p.encode initial q

theorem Implementation.Reset.trace_after_reset (p : Implementation c spec)
    (reset : I 1) (recovery : p.Reset reset) (i : Values I) (r : Values R)
    (h : i reset = 1) (inputs : List (Values I)) :
    c.component.trace (c.step i r) inputs = spec.trace recovery.initial inputs := by
  have he : (fun {w} (q : R w) => c.step i r q) = @p.encode recovery.initial :=
    funext fun w => funext fun q => recovery.reset_eq i r h q
  rw [he]
  exact p.trace_eq recovery.initial recovery.initial_valid inputs

end Pinwheel.Hardware
