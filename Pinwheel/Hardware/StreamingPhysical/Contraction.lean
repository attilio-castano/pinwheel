import Pinwheel.Hardware.StreamingPhysical.Network

namespace Pinwheel.Hardware.StreamingPhysical

inductive Atom where
  | constant : Bool → Atom
  | wire : Nat → Bool → Atom
  deriving Repr, DecidableEq

def Atom.eval (values : Nat → Bool) : Atom → Bool
  | .constant value => value
  | .wire index negative => if negative then !(values index) else values index

def Atom.complement : Atom → Atom
  | .constant value => .constant (!value)
  | .wire index negative => .wire index (!negative)

def Atom.rename (image : Nat → Atom) : Atom → Atom
  | .constant value => .constant value
  | .wire index negative => if negative then (image index).complement else image index

def Atom.Bounded (limit : Nat) : Atom → Prop
  | .constant _ => True
  | .wire index _ => index < limit

instance (limit : Nat) (atom : Atom) : Decidable (atom.Bounded limit) := by
  cases atom with
  | constant _ => exact isTrue True.intro
  | wire index _ => exact inferInstanceAs (Decidable (index < limit))

theorem Atom.eval_complement (values : Nat → Bool) (atom : Atom) :
    atom.complement.eval values = !(atom.eval values) := by
  cases atom with
  | constant value => rfl
  | wire index negative => cases negative <;> simp [Atom.complement, Atom.eval]

/-- A local rule compares only interpreted cell functions and named source
atoms. It contains no final-output or execution agreement premise. -/
inductive NodeRule (reference actual : Network) (image : Nat → Atom)
    (index : Fin actual.nodes) : Prop where
  | transport
      (identity : ∀ values,
        (actual.node index).expression.eval
          (fun pin => (image ((actual.node index).source pin)).eval values) =
        (image (actual.inputs + index.val)).eval values)
  | cell (selected : Fin reference.nodes)
      (output : image (actual.inputs + index.val) =
        .wire (reference.inputs + selected.val) false)
      (function : ∀ values,
        (actual.node index).expression.eval
          (fun pin => (image ((actual.node index).source pin)).eval values) =
        (reference.node selected).expression.eval
          (fun pin => values ((reference.node selected).source pin)))

structure Contraction (reference actual : Network) where
  sameInputs : actual.inputs = reference.inputs
  image : Nat → Atom
  input : ∀ wire, wire < actual.inputs → image wire = .wire wire false
  node : ∀ index, NodeRule reference actual image index

theorem Contraction.realizes {reference actual : Network}
    (certificate : Contraction reference actual) (inputs : Nat → Bool) :
    actual.Realizes inputs
      (fun wire => (certificate.image wire).eval (reference.value inputs)) := by
  constructor
  · intro wire bound
    simpa [certificate.input wire bound, Atom.eval] using
      reference.value_input inputs wire (certificate.sameInputs ▸ bound)
  · intro index
    cases certificate.node index with
    | transport identity => exact (identity (reference.value inputs)).symm
    | cell selected output function =>
      rw [output]
      exact (reference.value_node inputs selected).trans (function (reference.value inputs)).symm

theorem Contraction.value {reference actual : Network}
    (certificate : Contraction reference actual) (inputs : Nat → Bool) (wire : Nat)
    (bound : wire < actual.inputs + actual.nodes) :
    actual.value inputs wire = (certificate.image wire).eval (reference.value inputs) :=
  (Network.Realizes.unique actual inputs _ (certificate.realizes inputs) wire bound).symm

theorem Contraction.atom {reference actual : Network}
    (certificate : Contraction reference actual) (inputs : Nat → Bool) (root : Atom)
    (bound : root.Bounded (actual.inputs + actual.nodes)) :
    root.eval (actual.value inputs) = (root.rename certificate.image).eval (reference.value inputs) := by
  cases root with
  | constant value => rfl
  | wire index negative =>
    cases negative with
    | false => exact certificate.value inputs index bound
    | true =>
      exact Eq.trans (congrArg Bool.not (certificate.value inputs index bound)) (Atom.eval_complement (reference.value inputs) (certificate.image index)).symm

end Pinwheel.Hardware.StreamingPhysical
