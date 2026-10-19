import Pinwheel.Hardware.StreamingPhysical.Local

/-! A connected physical subgraph may receive arbitrary signals from its
parent. Every internal cell is matched by an actual local gate rule; its input
values are then derived from those parent wires, not assumed word results. -/
namespace Pinwheel.Hardware.StreamingPhysical

structure Embedding (parent child : Network) where
  image : Nat → Atom
  node : ∀ index, NodeRule parent child image index

def Embedding.inputs {parent child : Network} (embedding : Embedding parent child)
    (incoming : Nat → Bool) (wire : Nat) : Bool :=
  (embedding.image wire).eval (parent.value incoming)

theorem Embedding.realizes {parent child : Network} (embedding : Embedding parent child)
    (incoming : Nat → Bool) :
    child.Realizes (embedding.inputs incoming) (embedding.inputs incoming) := by
  constructor
  · intro wire _
    rfl
  · intro index
    cases embedding.node index with
    | transport identity => exact (identity (parent.value incoming)).symm
    | cell selected output function =>
      change (embedding.image (child.inputs + index.val)).eval (parent.value incoming) = _
      rw [output]
      exact (parent.value_node incoming selected).trans (function (parent.value incoming)).symm

theorem Embedding.value {parent child : Network} (embedding : Embedding parent child)
    (incoming : Nat → Bool) (wire : Nat) (bound : wire < child.inputs + child.nodes) :
    child.value (embedding.inputs incoming) wire =
      (embedding.image wire).eval (parent.value incoming) :=
  (Network.Realizes.unique child _ _ (embedding.realizes incoming) wire bound).symm

theorem Embedding.atom {parent child : Network} (embedding : Embedding parent child)
    (incoming : Nat → Bool) (root : Atom) (bound : root.Bounded (child.inputs + child.nodes)) :
    root.eval (child.value (embedding.inputs incoming)) =
      (root.rename embedding.image).eval (parent.value incoming) := by
  cases root with
  | constant value => rfl
  | wire index negative =>
    cases negative with
    | false => exact embedding.value incoming index bound
    | true =>
      exact Eq.trans (congrArg Bool.not (embedding.value incoming index bound))
        (Atom.eval_complement (parent.value incoming) (embedding.image index)).symm

end Pinwheel.Hardware.StreamingPhysical
