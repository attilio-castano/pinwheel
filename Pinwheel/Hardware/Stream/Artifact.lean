import Pinwheel.Hardware.Stream.Design

namespace Pinwheel.Hardware.Stream

theorem cast_value (q : Sigma P) (p : P w) (h : q = ⟨w, p⟩) (v : Values P) :
    Eq.mp (congrArg BitVec (congrArg Sigma.fst h)) (v q.2) = v p := by
  cases h
  rfl

/-- Reassemble a completely enumerated imported state/output table. Width
transports are justified by the existing checked interface descriptor. -/
def assemble (d : Interface P) (v : (k : Fin d.size) → BitVec (d.signal k).1) : Values P :=
  fun p => Eq.mp (congrArg BitVec (congrArg Sigma.fst (d.signal_position p))) (v (d.position p))

theorem assemble_eq (d : Interface P) (v : (k : Fin d.size) → BitVec (d.signal k).1)
    (reference : Values P) (h : ∀ k, v k = reference (d.signal k).2) :
    @assemble P d v = @reference := by
  funext w p
  simp only [assemble, h]
  exact cast_value _ p (d.signal_position p) reference

theorem history_refinement {a : Timed.Component (Input α) S (Output β)}
    {b : Timed.Component (Input α) T (Output β)} (r : Timed.Refinement a b)
    (s : S) (t : T) (h : r.Rel s t) (history : History α β) (inputs : List (Input α)) :
    r.Rel (runHistory a s history inputs).1 (runHistory b t history inputs).1 ∧
      (runHistory a s history inputs).2 = (runHistory b t history inputs).2 := by
  induction inputs generalizing s t history with
  | nil => exact ⟨h, rfl⟩
  | cons i rest ih =>
    simp only [runHistory, r.observe i s t h]
    exact ih _ _ (r.step i s t h) _

theorem Certified.simulator_transactions (c : Certified wi wo) (inputs : List (Input (BitVec wi))) :
    let actual := runHistory c.simulator (c.encode c.initial) {} inputs
    let model := runHistory c.machine.component c.initial {} inputs
    actual.2.inputs.map c.function = actual.2.outputs ++ c.contract.pending model.1 := by
  have h := (history_refinement c.refinement _ _ ⟨c.initial_valid, rfl⟩ {} inputs).2
  simpa only [h] using c.transactions inputs

end Pinwheel.Hardware.Stream
