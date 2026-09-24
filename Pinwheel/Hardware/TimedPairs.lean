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

/-- The state after a history of consumed inputs. -/
def Component.run (c : Component I S O) (s : S) : List I → S
  | [] => s
  | i :: rest => c.run (c.step i s) rest

/-- A pair trace splits at any point; the second part starts from the state the
first part's consumed inputs leave. -/
theorem Component.pairTrace_append (c : Component I S O) (s : S) (a b : List (I × I)) :
    c.pairTrace s (a ++ b) = c.pairTrace s a ++ c.pairTrace (c.run s (a.map Prod.fst)) b := by
  induction a generalizing s with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨i, after⟩ := pair
    simp only [List.cons_append, pairTrace, List.map, run, ih]

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

/-- Observations through a function: the same edges, each observation mapped. -/
theorem Component.pairTrace_map {I S O O' : Type} (c : Timed.Component I S O)
    (c' : Timed.Component I S O') (g : O → O') (hstep : ∀ i s, c'.step i s = c.step i s)
    (hobserve : ∀ i s, c'.observe i s = g (c.observe i s)) (s : S) (inputs : List (I × I)) :
    c'.pairTrace s inputs = (c.pairTrace s inputs).map (fun e => (g e.1, g e.2)) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨i, after⟩ := pair
    simp only [Timed.Component.pairTrace, List.map, hstep, hobserve, ih]


end Pinwheel.Hardware.Timed
