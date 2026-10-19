import Pinwheel.Hardware.StreamingMapped.Boolean

/-! Acyclic scalar cell networks with independently meaningful Boolean
evaluation. Inputs include every logical FF Q; register updates and public
outputs are selected separately by a sequential read-back certificate. -/
namespace Pinwheel.Hardware.StreamingPhysical

open Pinwheel.Hardware.StreamingMapped

structure Node where
  arity : Nat
  source : Fin arity → Nat
  expression : Expr arity

def Node.Safe (node : Node) (known : Nat) : Prop :=
  ∀ pin : Fin node.arity, node.source pin < known

structure Network where
  inputs : Nat
  nodes : Nat
  node : Fin nodes → Node
  ordered : ∀ (index : Fin nodes) (pin : Fin (node index).arity),
    (node index).source pin < inputs + index.val

def Network.value (network : Network) (inputs : Nat → Bool) (wire : Nat) : Bool :=
  if _first : wire < network.inputs then inputs wire
  else if present : wire - network.inputs < network.nodes then
    let node := network.node ⟨wire - network.inputs, present⟩
    node.expression.eval (fun pin => network.value inputs (node.source pin))
  else false
termination_by wire
decreasing_by
  exact Nat.lt_of_lt_of_eq (network.ordered ⟨wire - network.inputs, present⟩ pin)
    (Nat.add_sub_of_le (Nat.le_of_not_gt _first))

theorem Network.value_input (network : Network) (inputs : Nat → Bool) (wire : Nat)
    (bound : wire < network.inputs) : network.value inputs wire = inputs wire := by
  rw [Network.value, dif_pos bound]

theorem Network.value_node (network : Network) (inputs : Nat → Bool)
    (index : Fin network.nodes) :
    network.value inputs (network.inputs + index.val) =
      (network.node index).expression.eval
        (fun pin => network.value inputs ((network.node index).source pin)) := by
  rw [Network.value, dif_neg (by omega), Nat.add_sub_cancel_left, dif_pos index.isLt]

/-- Local equations of every actual connected cell, without any output or
reference-circuit agreement in the predicate. -/
structure Network.Realizes (network : Network) (inputs values : Nat → Bool) : Prop where
  input : ∀ wire, wire < network.inputs → values wire = inputs wire
  node : ∀ index : Fin network.nodes,
    values (network.inputs + index.val) = (network.node index).expression.eval
      (fun pin => values ((network.node index).source pin))

theorem Network.value_realizes (network : Network) (inputs : Nat → Bool) :
    network.Realizes inputs (network.value inputs) :=
  ⟨network.value_input inputs, network.value_node inputs⟩

theorem Network.Realizes.unique (network : Network) (inputs values : Nat → Bool)
    (realizes : network.Realizes inputs values) (wire : Nat)
    (bound : wire < network.inputs + network.nodes) :
    values wire = network.value inputs wire := by
  induction wire using Nat.strongRecOn with
  | ind wire earlier =>
    by_cases first : wire < network.inputs
    · exact (realizes.input wire first).trans (network.value_input inputs wire first).symm
    · let index : Fin network.nodes := ⟨wire - network.inputs, by omega⟩
      have split : wire = network.inputs + index.val :=
        (Nat.add_sub_of_le (Nat.le_of_not_gt first)).symm
      rw [split, realizes.node index, network.value_node]
      congr 1
      funext pin
      exact earlier _ (Nat.lt_of_lt_of_eq (network.ordered index pin) split.symm)
        (Nat.lt_trans (Nat.lt_of_lt_of_eq (network.ordered index pin) split.symm) bound)

end Pinwheel.Hardware.StreamingPhysical
