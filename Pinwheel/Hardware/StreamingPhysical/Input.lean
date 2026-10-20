import Pinwheel.Hardware.StreamingPhysical.Embedding

/-! Only the declared input prefix affects a finite acyclic network. This
lets connected subgraphs use their actual parent-wire environment without
requiring agreement at irrelevant out-of-range input indices. -/
namespace Pinwheel.Hardware.StreamingPhysical

theorem Network.value_congr (network : Network) (left right : Nat → Bool)
    (agreement : ∀ wire, wire < network.inputs → left wire = right wire)
    (wire : Nat) (bound : wire < network.inputs + network.nodes) :
    network.value left wire = network.value right wire := by
  apply Network.Realizes.unique network right (network.value left)
  · constructor
    · intro index present
      exact (network.value_input left index present).trans (agreement index present)
    · exact network.value_node left
  · exact bound

theorem Network.atom_congr (network : Network) (left right : Nat → Bool)
    (agreement : ∀ wire, wire < network.inputs → left wire = right wire)
    (root : Atom) (bound : root.Bounded (network.inputs + network.nodes)) :
    root.eval (network.value left) = root.eval (network.value right) := by
  cases root with
  | constant value => rfl
  | wire index negative =>
    cases negative with
    | false => exact network.value_congr left right agreement index bound
    | true => exact congrArg Bool.not (network.value_congr left right agreement index bound)

theorem Embedding.atom_input_congr {parent child : Network} (embedding : Embedding parent child)
    (incoming expected : Nat → Bool)
    (agreement : ∀ wire, wire < child.inputs → embedding.inputs incoming wire = expected wire)
    (root : Atom) (bound : root.Bounded (child.inputs + child.nodes)) :
    (root.rename embedding.image).eval (parent.value incoming) = root.eval (child.value expected) :=
  (embedding.atom incoming root bound).symm.trans
    (child.atom_congr (embedding.inputs incoming) expected agreement root bound)

end Pinwheel.Hardware.StreamingPhysical
