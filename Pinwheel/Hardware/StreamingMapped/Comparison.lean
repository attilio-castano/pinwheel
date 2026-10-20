import Pinwheel.Hardware.StreamingMapped.Reduction

namespace Pinwheel.Hardware.StreamingMapped

/-- Yosys comparison ports carry one literal Boolean bit. -/
theorem Ripple.Linked.lt_word (leaf : FullAdderLeaf) (correct : leaf.Correct)
    (x y : BitVec width) (wire : Nat → Bool) (output : BitVec width)
    (linked : Ripple.Linked leaf x (~~~y) true wire output) :
    BitVec.ofBool (!wire width) = BitVec.ofBool (decide (x.toNat < y.toNat)) := by
  rw [linked.ult_correct leaf correct x y wire output]
  rfl

theorem Ripple.Linked.le_word (leaf : FullAdderLeaf) (correct : leaf.Correct)
    (x y : BitVec width) (wire : Nat → Bool) (output : BitVec width)
    (linked : Ripple.Linked leaf y (~~~x) true wire output) :
    BitVec.ofBool (wire width) = BitVec.ofBool (decide (x.toNat ≤ y.toNat)) := by
  rw [linked.ule_correct leaf correct x y wire output]
  rfl

theorem Ripple.Linked.gt_word (leaf : FullAdderLeaf) (correct : leaf.Correct)
    (x y : BitVec width) (wire : Nat → Bool) (output : BitVec width)
    (linked : Ripple.Linked leaf y (~~~x) true wire output) :
    BitVec.ofBool (!wire width) = BitVec.ofBool (decide (y.toNat < x.toNat)) :=
  linked.lt_word leaf correct y x wire output

theorem Ripple.Linked.ge_word (leaf : FullAdderLeaf) (correct : leaf.Correct)
    (x y : BitVec width) (wire : Nat → Bool) (output : BitVec width)
    (linked : Ripple.Linked leaf x (~~~y) true wire output) :
    BitVec.ofBool (wire width) = BitVec.ofBool (decide (y.toNat ≤ x.toNat)) :=
  linked.le_word leaf correct y x wire output

theorem Reduction.Tree.eq_word (tree : Reduction.Tree width) (complete : tree.Complete)
    (left right : BitVec width) :
    BitVec.ofBool (!tree.eval (fun i => left.getLsbD i.val ^^ right.getLsbD i.val)) =
      BitVec.ofBool (decide (left = right)) := by
  rw [tree.word_eq complete left right]

theorem Reduction.Tree.ne_word (tree : Reduction.Tree width) (complete : tree.Complete)
    (left right : BitVec width) :
    BitVec.ofBool (tree.eval (fun i => left.getLsbD i.val ^^ right.getLsbD i.val)) =
      BitVec.ofBool (decide (left ≠ right)) := by
  have negated := congrArg (fun bit => !bit) (tree.word_eq complete left right)
  simpa only [Bool.not_not,← decide_not] using congrArg BitVec.ofBool negated

theorem Reduction.Tree.or_word (tree : Reduction.Tree width) (complete : tree.Complete)
    (word : BitVec width) : BitVec.ofBool (tree.eval (fun i => word.getLsbD i.val)) =
      BitVec.ofBool (decide (word ≠ 0#width)) := by
  rw [tree.reduce_or complete word]

end Pinwheel.Hardware.StreamingMapped
