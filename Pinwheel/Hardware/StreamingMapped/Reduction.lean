import Pinwheel.Hardware.StreamingMapped.Word

/-! Wide reductions are proved through actual Boolean trees and static leaf
coverage, avoiding exponential truth tables over whole word inputs. -/
namespace Pinwheel.Hardware.StreamingMapped.Reduction

inductive Tree (inputs : Nat) where
  | empty : Tree inputs
  | leaf : Fin inputs → Tree inputs
  | join : Tree inputs → Tree inputs → Tree inputs
  deriving Repr,DecidableEq

def Tree.leaves : Tree inputs → List (Fin inputs)
  | .empty => []
  | .leaf input => [input]
  | .join left right => left.leaves ++ right.leaves

def Tree.eval (values : Fin inputs → Bool) : Tree inputs → Bool
  | .empty => false
  | .leaf input => values input
  | .join left right => left.eval values || right.eval values

/-- Duplicate leaves are harmless; every word bit must occur, and the Fin type
excludes unrelated inputs. Generated coverage proofs are finite kernel checks. -/
def Tree.Complete (tree : Tree inputs) : Prop := ∀ input, input ∈ tree.leaves

theorem Tree.eval_false (tree : Tree inputs) (values : Fin inputs → Bool) :
    tree.eval values = false ↔ ∀ input ∈ tree.leaves,values input = false := by
  induction tree with
  | empty => simp [eval,leaves]
  | leaf input => simp [eval,leaves]
  | join left right ihLeft ihRight =>
    simp [eval,leaves,ihLeft,ihRight,List.mem_append,or_imp,forall_and]

theorem Tree.zero_iff (tree : Tree width) (complete : tree.Complete) (word : BitVec width) :
    tree.eval (fun i => word.getLsbD i.val) = false ↔ word = 0#width := by
  rw [tree.eval_false]
  constructor
  · intro zero
    apply BitVec.eq_of_getLsbD_eq
    intro i within
    simpa only [BitVec.getLsbD_zero] using zero ⟨i,within⟩ (complete _)
  · intro zero input _
    simp only [zero,BitVec.getLsbD_zero]

theorem Tree.reduce_or (tree : Tree width) (complete : tree.Complete) (word : BitVec width) :
    tree.eval (fun i => word.getLsbD i.val) = decide (word ≠ 0#width) := by
  have zero := tree.zero_iff complete word
  cases value : tree.eval (fun i => word.getLsbD i.val) with
  | false => simp [zero.mp value]
  | true =>
    have nonzero : word ≠ 0#width := by
      intro equal
      have contradiction := zero.mpr equal
      rw [value] at contradiction
      cases contradiction
    exact (decide_eq_true nonzero).symm

/-- Equality is the negated OR of the certified per-bit XOR functions. -/
theorem Tree.word_eq (tree : Tree width) (complete : tree.Complete) (left right : BitVec width) :
    (!tree.eval (fun i => left.getLsbD i.val ^^ right.getLsbD i.val)) = decide (left = right) := by
  have reduction := tree.reduce_or complete (left ^^^ right)
  have negated := congrArg (fun bit => !bit) reduction
  simpa only [BitVec.getLsbD_xor,← decide_not,Decidable.not_not,BitVec.xor_eq_zero_iff] using negated

/-- An AND tree may be reconstructed as an inverted OR of inverted leaves;
this handles NAND/NOR implementations with explicit checked inversion phases. -/
def Tree.evalAnd (values : Fin inputs → Bool) (tree : Tree inputs) : Bool :=
  !tree.eval (fun i => !values i)

theorem Tree.evalAnd_empty (values : Fin inputs → Bool) : Tree.empty.evalAnd values = true := rfl

theorem Tree.evalAnd_leaf (values : Fin inputs → Bool) (input : Fin inputs) :
    (Tree.leaf input).evalAnd values = values input := by simp [evalAnd,eval]

theorem Tree.evalAnd_join (values : Fin inputs → Bool) (left right : Tree inputs) :
    (Tree.join left right).evalAnd values = (left.evalAnd values && right.evalAnd values) := by
  simp only [evalAnd,eval,Bool.not_or]

theorem Tree.word_eq_and (tree : Tree width) (complete : tree.Complete) (left right : BitVec width) :
    tree.evalAnd (fun i => !(left.getLsbD i.val ^^ right.getLsbD i.val)) = decide (left = right) := by
  simpa only [evalAnd,Bool.not_not] using tree.word_eq complete left right

end Pinwheel.Hardware.StreamingMapped.Reduction
