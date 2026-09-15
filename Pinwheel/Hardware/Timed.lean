import Std

namespace Pinwheel.Hardware.Timed

/-- One synchronous transition. Observations may depend on the current input. -/
structure Component (Input State Output : Type) where
  step : Input → State → State
  observe : Input → State → Output

/-- Both observations use the same input, on either side of the register update. -/
def Component.edge (c : Component I S O) (i : I) (s : S) : O × O :=
  (c.observe i s, c.observe i (c.step i s))

def Component.trace (c : Component I S O) (s : S) : List I → List (O × O)
  | [] => []
  | i :: rest => c.edge i s :: c.trace (c.step i s) rest

/-- Every implementation edge matches one specification edge; no stuttering. -/
structure Refinement (impl : Component I S O) (spec : Component I T O) where
  Rel : S → T → Prop
  step : ∀ i s t, Rel s t → Rel (impl.step i s) (spec.step i t)
  observe : ∀ i s t, Rel s t → impl.observe i s = spec.observe i t

variable {I S T U O : Type} {impl : Component I S O} {spec : Component I T O}

def Refinement.refl (c : Component I S O) : Refinement c c where
  Rel := Eq
  step := fun _ _ _ h => congrArg _ h
  observe := fun _ _ _ h => congrArg _ h

/-- Internal representation changes compose without adding or removing clock edges. -/
def Refinement.trans {last : Component I U O}
    (a : Refinement impl spec) (b : Refinement spec last) : Refinement impl last where
  Rel := fun s u => ∃ t, a.Rel s t ∧ b.Rel t u
  step := fun i s u ⟨t, hs, ht⟩ => ⟨spec.step i t, a.step i s t hs, b.step i t u ht⟩
  observe := fun i s u ⟨t, hs, ht⟩ => (a.observe i s t hs).trans (b.observe i t u ht)

theorem Refinement.edge_eq (r : Refinement impl spec) (s : S) (t : T)
    (h : r.Rel s t) (i : I) : impl.edge i s = spec.edge i t :=
  Prod.ext (r.observe i s t h) (r.observe i _ _ (r.step i s t h))

theorem Refinement.trace_eq (r : Refinement impl spec) (s : S) (t : T)
    (h : r.Rel s t) (inputs : List I) : impl.trace s inputs = spec.trace t inputs := by
  induction inputs generalizing s t with
  | nil => rfl
  | cons i rest ih =>
    simpa only [Component.trace, Component.edge, List.cons.injEq, Prod.mk.injEq] using
      And.intro (And.intro (r.observe i s t h)
        (r.observe i (impl.step i s) (spec.step i t) (r.step i s t h)))
        (ih _ _ (r.step i s t h))

end Pinwheel.Hardware.Timed
