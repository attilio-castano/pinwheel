import Pinwheel.Hardware.RunRefinement

/-! Implementation by a state projection. Several physical states may represent
the same logical state, for example when inactive request metadata is retained.
This complements `Implementation`'s canonical encoding without requiring an
inverse encoding or artificial clearing of unused registers.
-/
namespace Pinwheel.Hardware

structure DecodedImplementation (c : Circuit I R O)
    (spec : Timed.Component (Values I) S (Values O)) where
  Valid : Values R → Prop
  view : Values R → S
  preserved : ∀ i r, Valid r → Valid (c.step i r)
  step_eq : ∀ i r, Valid r → view (c.step i r) = spec.step i (view r)
  output_eq : ∀ i r, Valid r → ∀ {b} (o : O b), c.observe i r o = spec.observe i (view r) o

namespace DecodedImplementation

variable {c : Circuit I R O} {spec : Timed.Component (Values I) S (Values O)}

def refinement (p : DecodedImplementation c spec) : Timed.Refinement c.component spec where
  Rel := fun r s => p.Valid r ∧ p.view r = s
  step := by
    intro i r s h
    rcases h with ⟨hv, rfl⟩
    exact ⟨p.preserved i r hv, p.step_eq i r hv⟩
  observe := by
    intro i r s h
    rcases h with ⟨hv, rfl⟩
    exact funext fun b => funext fun o => p.output_eq i r hv (b := b) o

theorem trace_eq (p : DecodedImplementation c spec) (r : Values R) (h : p.Valid r)
    (inputs : List (Values I)) : c.component.trace r inputs = spec.trace (p.view r) inputs :=
  p.refinement.trace_eq _ _ ⟨h, rfl⟩ inputs

theorem run_valid (p : DecodedImplementation c spec) (r : Values R) (h : p.Valid r)
    (inputs : List (Values I)) : p.Valid (c.component.run r inputs) :=
  (p.refinement.run_related _ _ ⟨h, rfl⟩ inputs).1

theorem run_eq (p : DecodedImplementation c spec) (r : Values R) (h : p.Valid r)
    (inputs : List (Values I)) : p.view (c.component.run r inputs) = spec.run (p.view r) inputs :=
  (p.refinement.run_related _ _ ⟨h, rfl⟩ inputs).2

variable {rtl : Timed.Component (Values I) (Values R) (Values O)}

def toArtifact (p : DecodedImplementation c spec) (a : Artifact.Correspondence c rtl) :
    Timed.Refinement rtl spec := a.refinement.trans p.refinement

theorem artifact_trace_eq (p : DecodedImplementation c spec) (a : Artifact.Correspondence c rtl)
    (r : Values R) (h : p.Valid r) (inputs : List (Values I)) :
    rtl.trace r inputs = spec.trace (p.view r) inputs :=
  (a.refinement.trace_eq _ _ rfl inputs).trans (p.trace_eq r h inputs)

theorem artifact_run_eq (p : DecodedImplementation c spec) (a : Artifact.Correspondence c rtl)
    (r : Values R) (h : p.Valid r) (inputs : List (Values I)) :
    p.view (rtl.run r inputs) = spec.run (p.view r) inputs := by
  rw [a.run_eq]
  exact p.run_eq r h inputs

/-- Reset may recover a different logical state for each physical memory image.
The initial state depends only on the pre-reset registers, not inactive input
fields. No surjectivity or fixed initialization of retained storage is assumed. -/
structure Reset (p : DecodedImplementation c spec) (reset : I 1) where
  initial : Values R → S
  reset_valid : ∀ i r, i reset = 1 → p.Valid (c.step i r)
  reset_view : ∀ i r, i reset = 1 → p.view (c.step i r) = initial r

theorem Reset.trace_after_reset (p : DecodedImplementation c spec) (reset : I 1)
    (recovery : p.Reset reset) (i : Values I) (r : Values R) (h : i reset = 1)
    (inputs : List (Values I)) :
    c.component.trace (c.step i r) inputs = spec.trace (recovery.initial r) inputs := by
  rw [p.trace_eq _ (recovery.reset_valid i r h), recovery.reset_view i r h]

theorem Reset.run_after_reset (p : DecodedImplementation c spec) (reset : I 1)
    (recovery : p.Reset reset) (i : Values I) (r : Values R) (h : i reset = 1)
    (inputs : List (Values I)) :
    p.view (c.component.run (c.step i r) inputs) = spec.run (recovery.initial r) inputs := by
  rw [p.run_eq _ (recovery.reset_valid i r h), recovery.reset_view i r h]

theorem Reset.artifact_trace_after_reset (p : DecodedImplementation c spec) (reset : I 1)
    (recovery : p.Reset reset) (a : Artifact.Correspondence c rtl)
    (i : Values I) (r : Values R) (h : i reset = 1) (inputs : List (Values I)) :
    rtl.trace (rtl.step i r) inputs = spec.trace (recovery.initial r) inputs := by
  rw [a.refinement.trace_eq _ _ rfl, a.step_eq]
  exact recovery.trace_after_reset p reset i r h inputs

theorem Reset.artifact_run_after_reset (p : DecodedImplementation c spec) (reset : I 1)
    (recovery : p.Reset reset) (a : Artifact.Correspondence c rtl)
    (i : Values I) (r : Values R) (h : i reset = 1) (inputs : List (Values I)) :
    p.view (rtl.run (rtl.step i r) inputs) = spec.run (recovery.initial r) inputs := by
  rw [a.run_eq, a.step_eq]
  exact recovery.run_after_reset p reset i r h inputs

end DecodedImplementation
end Pinwheel.Hardware
