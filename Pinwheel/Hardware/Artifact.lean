import Pinwheel.Hardware.Interface
import Pinwheel.Hardware.Implementation

namespace Pinwheel.Hardware

private theorem castValue (q : Sigma P) (p : P w) (h : q = ⟨w, p⟩) (v : Values P) :
    Eq.mp (congrArg BitVec (congrArg Sigma.fst h)) (v q.2) = v p := by
  cases h
  rfl

/-- Reassemble every imported endpoint through a complete typed descriptor.
The widths are transported using its checked enumeration, never a port name. -/
def Interface.assemble (d : Interface P)
    (v : (k : Fin d.size) → BitVec (d.signal k).1) : Values P :=
  fun p => Eq.mp (congrArg BitVec (congrArg Sigma.fst (d.signal_position p))) (v (d.position p))

theorem Interface.assemble_eq (d : Interface P)
    (v : (k : Fin d.size) → BitVec (d.signal k).1)
    (reference : Values P) (h : ∀ k, v k = reference (d.signal k).2) :
    @Interface.assemble P d v = @reference := by
  funext w p
  simp only [assemble, h]
  exact castValue _ p (d.signal_position p) reference

namespace Artifact

/-- The imported two-state RTL interpretation agrees at every register and
output, for arbitrary input and state bits. This certificate does not prove
the external parser, synthesizer, timing model, or physical implementation. -/
structure Correspondence (c : Circuit I R O)
    (rtl : Timed.Component (Values I) (Values R) (Values O)) where
  step_eq : ∀ i s, @Eq (Values R) (rtl.step i s) (c.step i s)
  output_eq : ∀ i s, @Eq (Values O) (rtl.observe i s) (c.observe i s)

variable {I R O : Nat → Type} {S : Type} {c : Circuit I R O}
  {rtl : Timed.Component (Values I) (Values R) (Values O)}
  {spec : Timed.Component (Values I) S (Values O)}

def Correspondence.refinement (a : Correspondence c rtl) :
    Timed.Refinement rtl c.component where
  Rel := Eq
  step := by intro i s t h; cases h; exact a.step_eq i s
  observe := by intro i s t h; cases h; exact a.output_eq i s

/-- Structural component proofs carry through a separately checked artifact. -/
def Correspondence.toSpec (a : Correspondence c rtl) (p : Implementation c spec) :
    Timed.Refinement rtl spec := a.refinement.trans p.refinement

theorem Correspondence.initialized_trace (a : Correspondence c rtl)
    (p : Implementation c spec) (reset : I 1) (recovery : p.Reset reset)
    (i : Values I) (r : Values R) (h : i reset = 1) (inputs : List (Values I)) :
    rtl.trace (rtl.step i r) inputs = spec.trace recovery.initial inputs := by
  rw [a.refinement.trace_eq _ _ rfl, a.step_eq]
  exact recovery.trace_after_reset p reset i r h inputs

end Artifact
end Pinwheel.Hardware
