import Pinwheel.Hardware.Timed

/-! Traces whose post-edge observation may use a different input than the
pre-edge one. A wrapper with input registers changes the engine-side input at
the clock edge, so combinational outputs see the new value after the edge. -/
namespace Pinwheel.Hardware.Timed

/-- Each pair is (input consumed by the edge, input present after the edge). -/
def Component.pairTrace (c : Component I S O) (s : S) : List (I × I) → List (O × O)
  | [] => []
  | (i, after) :: rest => (c.observe i s, c.observe after (c.step i s)) :: c.pairTrace (c.step i s) rest

/-- The ordinary trace holds each input across its edge. -/
theorem Component.pairTrace_same (c : Component I S O) (s : S) (inputs : List I) :
    c.pairTrace s (inputs.map fun i => (i, i)) = c.trace s inputs := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih => simp only [List.map, pairTrace, trace, edge, ih]

variable {I S T O : Type} {impl : Component I S O} {spec : Component I T O}

/-- A refinement preserves both observations for every choice of post-edge input. -/
theorem Refinement.pairTrace_eq (r : Refinement impl spec) (s : S) (t : T)
    (h : r.Rel s t) (inputs : List (I × I)) : impl.pairTrace s inputs = spec.pairTrace t inputs := by
  induction inputs generalizing s t with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨i, after⟩ := pair
    simp only [Component.pairTrace, r.observe i s t h,
      r.observe after _ _ (r.step i s t h), ih _ _ (r.step i s t h)]

end Pinwheel.Hardware.Timed
