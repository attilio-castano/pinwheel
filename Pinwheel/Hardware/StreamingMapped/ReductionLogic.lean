import Pinwheel.Hardware.StreamingMapped.Comparison

namespace Pinwheel.Hardware.StreamingMapped.Reduction

theorem Tree.word_ne (tree : Tree width) (complete : tree.Complete) (left right : BitVec width) :
    tree.eval (fun i => left.getLsbD i.val ^^ right.getLsbD i.val) = decide (left ≠ right) := by
  have negated := congrArg (fun bit => !bit) (tree.word_eq complete left right)
  simpa only [Bool.not_not,← decide_not] using negated

theorem Tree.logic_not (tree : Tree width) (complete : tree.Complete) (word : BitVec width) :
    (!tree.eval (fun i => word.getLsbD i.val)) = decide (word = 0#width) := by
  have negated := congrArg (fun bit => !bit) (tree.reduce_or complete word)
  simpa only [← decide_not,Decidable.not_not] using negated

theorem Tree.logic_not_word (tree : Tree width) (complete : tree.Complete) (word : BitVec width) :
    BitVec.ofBool (!tree.eval (fun i => word.getLsbD i.val)) = BitVec.ofBool (decide (word = 0#width)) := by
  rw [tree.logic_not complete word]

/-- XNOR's implication clauses permit purely structural associative/commutative
normalization of ABC's merged equality networks. -/
theorem xnor_clause (a b : Bool) : (!(a ^^ b)) = ((a || !b) && (!a || b)) := by
  cases a <;> cases b <;> rfl

end Pinwheel.Hardware.StreamingMapped.Reduction
