import Pinwheel.Hardware.Bank
import Pinwheel.Hardware.Implementation

namespace Pinwheel.Hardware

/-- A bank of independent synchronous machines, addressed through typed lanes. -/
def Bank.model (count : Nat) (spec : Timed.Component (Values I) S (Values O)) :
    Timed.Component (Values (Bank count I)) (Fin count → S) (Values (Bank count O)) :=
  ⟨fun i s k => spec.step (fun p => i (.at k p)) (s k),
   fun i s => Bank.values (fun k => spec.observe (fun p => i (.at k p)) (s k))⟩

variable {I R O : Nat → Type} {S : Type} {c : Circuit I R O}
  {spec : Timed.Component (Values I) S (Values O)}

/-- Replication preserves each instance's implementation relation. No proof of
the component's internal register representation is reopened. -/
def Implementation.bank (p : Implementation c spec) (count : Nat) :
    Implementation (Bank.circuit count c) (Bank.model count spec) where
  Valid := fun s => ∀ k, p.Valid (s k)
  encode := fun s => Bank.values (fun k => p.encode (s k))
  preserved := fun i s h k => p.preserved (fun q => i (.at k q)) (s k) (h k)
  step_eq := by
    intro i s h w r
    cases r with
    | «at» k r =>
      simp only [Bank.circuit, Circuit.step, Expr.eval_bind, Expr.eval, Bank.values, Bank.model]
      exact p.step_eq (fun q => i (.at k q)) (s k) (h k) r
  output_eq := by
    intro i s h w o
    cases o with
    | «at» k o =>
      simp only [Bank.circuit, Circuit.observe, Expr.eval_bind, Expr.eval, Bank.values, Bank.model]
      exact p.output_eq (fun q => i (.at k q)) (s k) (h k) o

end Pinwheel.Hardware
