import Pinwheel.Hardware.TimedPairs

/-! Refinement under a rule on inputs. Some implementations match their
specification only on histories whose inputs satisfy a condition — a fetch
organization that needs something of the programs it is given, for instance.
Observations agree whenever the states are related; only the step needs the
rule. Edges are still matched one for one. -/
namespace Pinwheel.Hardware.Timed

structure RuleRefinement (impl : Component I S O) (spec : Component I T O) (Rule : I → Prop) where
  Rel : S → T → Prop
  step : ∀ i s t, Rule i → Rel s t → Rel (impl.step i s) (spec.step i t)
  observe : ∀ i s t, Rel s t → impl.observe i s = spec.observe i t

variable {I S T U O : Type} {impl : Component I S O} {spec : Component I T O} {Rule : I → Prop}

/-- An unconditional refinement holds under every rule. -/
def Refinement.underRule (r : Refinement impl spec) (Rule : I → Prop) : RuleRefinement impl spec Rule where
  Rel := r.Rel
  step := fun i s t _ h => r.step i s t h
  observe := r.observe

/-- A representation change below a conditional refinement. -/
def Refinement.transRule {last : Component I U O} (a : Refinement impl spec)
    (b : RuleRefinement spec last Rule) : RuleRefinement impl last Rule where
  Rel := fun s u => ∃ t, a.Rel s t ∧ b.Rel t u
  step := fun i s u hr ⟨t, hs, ht⟩ => ⟨spec.step i t, a.step i s t hs, b.step i t u hr ht⟩
  observe := fun i s u ⟨t, hs, ht⟩ => (a.observe i s t hs).trans (b.observe i t u ht)

theorem RuleRefinement.trace_eq (r : RuleRefinement impl spec Rule) (s : S) (t : T) (h : r.Rel s t)
    (inputs : List I) (hr : ∀ i ∈ inputs, Rule i) : impl.trace s inputs = spec.trace t inputs := by
  induction inputs generalizing s t with
  | nil => rfl
  | cons i rest ih =>
    have hs := r.step i s t (hr i (List.mem_cons_self ..)) h
    simpa only [Component.trace, Component.edge, List.cons.injEq, Prod.mk.injEq] using
      And.intro (And.intro (r.observe i s t h) (r.observe i _ _ hs))
        (ih _ _ hs (fun j hj => hr j (List.mem_cons_of_mem i hj)))

/-- With post-edge inputs that differ, the rule is asked of the input each edge consumes. -/
theorem RuleRefinement.pairTrace_eq (r : RuleRefinement impl spec Rule) (s : S) (t : T) (h : r.Rel s t)
    (inputs : List (I × I)) (hr : ∀ e ∈ inputs, Rule e.1) :
    impl.pairTrace s inputs = spec.pairTrace t inputs := by
  induction inputs generalizing s t with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨i, after⟩ := pair
    have hs := r.step i s t (hr (i, after) (List.mem_cons_self ..)) h
    simp only [Component.pairTrace, r.observe i s t h, r.observe after _ _ hs,
      ih _ _ hs (fun e he => hr e (List.mem_cons_of_mem _ he))]

/-- The same component behind a combinational filter on its inputs. -/
def Component.precompose (c : Component I S O) (f : I → I) : Component I S O :=
  ⟨fun i s => c.step (f i) s, fun i s => c.observe (f i) s⟩

/-- A filter that establishes the rule discharges it: behind the filter, the
implementation refines the specification behind the same filter, unconditionally. -/
def RuleRefinement.precompose (r : RuleRefinement impl spec Rule) (f : I → I) (h : ∀ i, Rule (f i)) :
    Refinement (impl.precompose f) (spec.precompose f) where
  Rel := r.Rel
  step := fun i s t hrel => r.step (f i) s t (h i) hrel
  observe := fun i s t hrel => r.observe (f i) s t hrel

end Pinwheel.Hardware.Timed
