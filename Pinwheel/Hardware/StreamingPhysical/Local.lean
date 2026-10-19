import Pinwheel.Hardware.StreamingPhysical.Contraction

/-! Reify the finite connected cell before interpreting it. Static wire lookup
is kernel checked separately from the small Boolean identity; this keeps large
network tables out of elaboration of universal function equalities. -/
namespace Pinwheel.Hardware.StreamingPhysical
open Pinwheel.Hardware.StreamingMapped

inductive Term where
  | constant : Bool → Term
  | variable : Nat → Term
  | inv : Term → Term
  | conj : Term → Term → Term
  | disj : Term → Term → Term
  | xor : Term → Term → Term
  deriving DecidableEq

def Term.eval (values : Nat → Bool) : Term → Bool
  | .constant value => value
  | .variable index => values index
  | .inv child => !(child.eval values)
  | .conj left right => left.eval values && right.eval values
  | .disj left right => left.eval values || right.eval values
  | .xor left right => left.eval values ^^ right.eval values

def Atom.term : Atom → Term
  | .constant value => .constant value
  | .wire index negative => if negative then .inv (.variable index) else .variable index

theorem Atom.eval_term (atom : Atom) (values : Nat → Bool) :
    atom.term.eval values = atom.eval values := by
  cases atom with
  | constant value => rfl
  | wire index negative => cases negative <;> rfl

def expressionTerm (expression : Expr count) (wires : Fin count → Term) : Term :=
  match expression with
  | .constant value => .constant value
  | .var pin => wires pin
  | .inv child => .inv (expressionTerm child wires)
  | .conj left right => .conj (expressionTerm left wires) (expressionTerm right wires)
  | .disj left right => .disj (expressionTerm left wires) (expressionTerm right wires)
  | .xor left right => .xor (expressionTerm left wires) (expressionTerm right wires)

theorem expressionTerm_eval (expression : Expr count) (wires : Fin count → Term)
    (values : Nat → Bool) :
    (expressionTerm expression wires).eval values = expression.eval (fun pin => (wires pin).eval values) := by
  induction expression with
  | constant value => rfl
  | var pin => rfl
  | inv child ih => exact congrArg Bool.not ih
  | conj left right il ir => exact congrArg (fun value => value && _) il |>.trans (congrArg (fun value => _ && value) ir)
  | disj left right il ir => exact congrArg (fun value => value || _) il |>.trans (congrArg (fun value => _ || value) ir)
  | xor left right il ir => exact congrArg (fun value => value ^^ _) il |>.trans (congrArg (fun value => _ ^^ value) ir)

def Node.term (node : Node) (image : Nat → Atom) : Term :=
  expressionTerm node.expression (fun pin => (image (node.source pin)).term)

theorem Node.eval_term (node : Node) (image : Nat → Atom) (values : Nat → Bool) :
    (node.term image).eval values =
      node.expression.eval (fun pin => (image (node.source pin)).eval values) := by
  exact (expressionTerm_eval _ _ _).trans
    (congrArg (Expr.eval · node.expression) (funext (fun pin => Atom.eval_term _ values)))

theorem Node.connected_value (node : Node) (term : Term) (values : Nat → Bool)
    (result : Bool) (connected : node.term (fun wire => .wire wire false) = term)
    (equation : result = term.eval values) :
    result = node.expression.eval (fun pin => values (node.source pin)) :=
  equation.trans ((congrArg (Term.eval values) connected).symm.trans
    (node.eval_term (fun wire => .wire wire false) values))

theorem NodeRule.transport_local {reference actual : Network} {image : Nat → Atom}
    {index : Fin actual.nodes} (left : Term) (right : Atom)
    (connected : (actual.node index).term image = left)
    (output : image (actual.inputs + index.val) = right)
    (identity : ∀ values, left.eval values = right.eval values) :
    NodeRule reference actual image index := by
  apply NodeRule.transport
  intro values
  rw [← Node.eval_term, connected, output]
  exact identity values

theorem NodeRule.cell_local {reference actual : Network} {image : Nat → Atom}
    {index : Fin actual.nodes} (selected : Fin reference.nodes) (left right : Term)
    (connected : (actual.node index).term image = left)
    (referenceCell : (reference.node selected).term (fun wire => .wire wire false) = right)
    (output : image (actual.inputs + index.val) = .wire (reference.inputs + selected.val) false)
    (identity : ∀ values, left.eval values = right.eval values) :
    NodeRule reference actual image index := by
  apply NodeRule.cell selected output
  intro values
  rw [← Node.eval_term, connected]
  have rightValue := Node.eval_term (reference.node selected) (fun wire => .wire wire false) values
  rw [referenceCell] at rightValue
  exact (identity values).trans rightValue

end Pinwheel.Hardware.StreamingPhysical
