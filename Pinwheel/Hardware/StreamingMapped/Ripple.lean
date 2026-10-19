import Pinwheel.Hardware.StreamingMapped.Boolean

/-! A physical ripple certificate contains wire connections, not a word-level
result equation. Its arithmetic meaning follows from the certified leaf. -/
namespace Pinwheel.Hardware.StreamingMapped.Ripple

structure Linked (leaf : FullAdderLeaf) (x y : BitVec width) (carryIn : Bool)
    (wire : Nat → Bool) (output : BitVec width) : Prop where
  initial : wire 0 = carryIn
  carry : ∀ i, i < width → wire (i+1) = leaf.carry (x.getLsbD i) (y.getLsbD i) (wire i)
  sum : ∀ i, i < width → output.getLsbD i = leaf.sum (x.getLsbD i) (y.getLsbD i) (wire i)

theorem Linked.carry_correct (leaf : FullAdderLeaf) (correct : leaf.Correct)
    (x y : BitVec width) (carryIn : Bool) (wire : Nat → Bool) (output : BitVec width)
    (linked : Linked leaf x y carryIn wire output) (i : Nat) (within : i ≤ width) :
    wire i = BitVec.carry i x y carryIn := by
  induction i with
  | zero => simpa only [BitVec.carry_zero] using linked.initial
  | succ i ih =>
    rw [linked.carry i (by omega),correct.carry,ih (by omega),BitVec.carry_succ]

theorem Linked.word_correct (leaf : FullAdderLeaf) (correct : leaf.Correct)
    (x y : BitVec width) (carryIn : Bool) (wire : Nat → Bool) (output : BitVec width)
    (linked : Linked leaf x y carryIn wire output) :
    output = x+y+(BitVec.ofBool carryIn).setWidth width := by
  apply BitVec.eq_of_getLsbD_eq
  intro i within
  rw [linked.sum i within,correct.sum,
    linked.carry_correct leaf correct x y carryIn wire output i (Nat.le_of_lt within),
    BitVec.getLsbD_add_add_bool within]

theorem Linked.add_correct (leaf : FullAdderLeaf) (correct : leaf.Correct)
    (x y : BitVec width) (wire : Nat → Bool) (output : BitVec width)
    (linked : Linked leaf x y false wire output) : output = x+y := by
  simpa using linked.word_correct leaf correct x y false wire output

theorem Linked.sub_correct (leaf : FullAdderLeaf) (correct : leaf.Correct)
    (x y : BitVec width) (wire : Nat → Bool) (output : BitVec width)
    (linked : Linked leaf x (~~~y) true wire output) : output = x-y := by
  have result := linked.word_correct leaf correct x (~~~y) true wire output
  change output = x + (~~~y) + (1#1).setWidth width at result
  rw [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide)] at result
  simpa only [BitVec.sub_eq_add_neg,BitVec.neg_eq_not_add,BitVec.add_assoc] using result

theorem Linked.ult_correct (leaf : FullAdderLeaf) (correct : leaf.Correct)
    (x y : BitVec width) (wire : Nat → Bool) (output : BitVec width)
    (linked : Linked leaf x (~~~y) true wire output) : (!wire width) = x.ult y := by
  rw [linked.carry_correct leaf correct x (~~~y) true wire output width (Nat.le_refl _),
    BitVec.ult_eq_not_carry]

theorem Linked.ule_correct (leaf : FullAdderLeaf) (correct : leaf.Correct)
    (x y : BitVec width) (wire : Nat → Bool) (output : BitVec width)
    (linked : Linked leaf y (~~~x) true wire output) : wire width = x.ule y := by
  rw [linked.carry_correct leaf correct y (~~~x) true wire output width (Nat.le_refl _),
    BitVec.ule_eq_carry]

end Pinwheel.Hardware.StreamingMapped.Ripple
