import Pinwheel.Hardware.Artifact
import Pinwheel.Hardware.TimedPairs

/-! Final-state correspondence complements observable trace correspondence.
It transfers memory contents and other represented state through arbitrary
finite histories, even when that state is not exposed on a current output.
-/
namespace Pinwheel.Hardware

theorem Timed.Refinement.run_related {impl : Timed.Component I S O}
    {spec : Timed.Component I T O} (r : Timed.Refinement impl spec)
    (s : S) (t : T) (h : r.Rel s t) (inputs : List I) :
    r.Rel (impl.run s inputs) (spec.run t inputs) := by
  induction inputs generalizing s t with
  | nil => exact h
  | cons i rest ih => exact ih _ _ (r.step i s t h)

theorem Implementation.run_eq {c : Circuit I R O}
    {spec : Timed.Component (Values I) S (Values O)} (p : Implementation c spec)
    (s : S) (h : p.Valid s) (inputs : List (Values I)) :
    @Eq (Values R) (c.component.run (p.encode s) inputs) (p.encode (spec.run s inputs)) :=
  (p.refinement.run_related _ _ ⟨h, rfl⟩ inputs).2

theorem Artifact.Correspondence.run_eq {c : Circuit I R O}
    {rtl : Timed.Component (Values I) (Values R) (Values O)} (a : Correspondence c rtl)
    (s : Values R) (inputs : List (Values I)) :
    @Eq (Values R) (rtl.run s inputs) (c.component.run s inputs) :=
  a.refinement.run_related _ _ rfl inputs

theorem Artifact.Correspondence.encoded_run {c : Circuit I R O}
    {rtl : Timed.Component (Values I) (Values R) (Values O)} (a : Correspondence c rtl)
    {spec : Timed.Component (Values I) S (Values O)} (p : Implementation c spec)
    (s : S) (h : p.Valid s) (inputs : List (Values I)) :
    @Eq (Values R) (rtl.run (p.encode s) inputs) (p.encode (spec.run s inputs)) :=
  (a.run_eq _ inputs).trans (p.run_eq s h inputs)

end Pinwheel.Hardware
