import Pinwheel.Hardware.StreamingMapped.Ripple

/-! Little-endian port packing and word semantics. Local premises are scalar
wire equations established from actual mapped gates; no word-result equation
is supplied to these bridges. -/
namespace Pinwheel.Hardware.StreamingMapped.Word

def pack (values : Fin width → Bool) : BitVec width :=
  (BitVec.ofBoolListLE (List.ofFn values)).setWidth width

theorem pack_bit (values : Fin width → Bool) (i : Nat) (within : i < width) :
    (pack values).getLsbD i = values ⟨i,within⟩ := by
  simp only [pack,BitVec.getLsbD_setWidth,within,decide_true,Bool.true_and,
    BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos True.intro,Option.getD_some]

theorem pack_word (word : BitVec width) : pack (fun i => word.getLsbD i.val) = word := by
  apply BitVec.eq_of_getLsbD_eq
  intro i within
  exact pack_bit _ i within

theorem from_bits (left right : BitVec width)
    (bits : ∀ i, i < width → left.getLsbD i = right.getLsbD i) : left = right :=
  BitVec.eq_of_getLsbD_eq bits

theorem and_correct (x y output : BitVec width)
    (bits : ∀ i, i < width → output.getLsbD i = (x.getLsbD i && y.getLsbD i)) :
    output = x &&& y := by
  apply from_bits
  intro i within
  rw [bits i within,BitVec.getLsbD_and]

theorem or_correct (x y output : BitVec width)
    (bits : ∀ i, i < width → output.getLsbD i = (x.getLsbD i || y.getLsbD i)) :
    output = x ||| y := by
  apply from_bits
  intro i within
  rw [bits i within,BitVec.getLsbD_or]

theorem xor_correct (x y output : BitVec width)
    (bits : ∀ i, i < width → output.getLsbD i = (x.getLsbD i ^^ y.getLsbD i)) :
    output = x ^^^ y := by
  apply from_bits
  intro i within
  rw [bits i within,BitVec.getLsbD_xor]

theorem not_correct (x output : BitVec width)
    (bits : ∀ i, i < width → output.getLsbD i = !x.getLsbD i) : output = ~~~x := by
  apply from_bits
  intro i within
  rw [bits i within,BitVec.getLsbD_not]
  simp only [within,decide_true,Bool.true_and]

theorem mux_correct (select : Bool) (yes no output : BitVec width)
    (bits : ∀ i, i < width → output.getLsbD i =
      (if select then yes.getLsbD i else no.getLsbD i)) :
    output = if select then yes else no := by
  cases select <;> apply from_bits <;> intro i within <;> exact bits i within

theorem slice_correct (x : BitVec sourceWidth) (offset : Nat) (output : BitVec width)
    (bits : ∀ i, i < width → output.getLsbD i = x.getLsbD (offset+i)) :
    output = x.extractLsb' offset width := by
  apply from_bits
  intro i within
  rw [bits i within,BitVec.getLsbD_extractLsb']
  simp only [within,decide_true,Bool.true_and]

theorem concat_correct (high : BitVec highWidth) (low : BitVec lowWidth)
    (output : BitVec (highWidth+lowWidth))
    (bits : ∀ i, i < highWidth+lowWidth → output.getLsbD i =
      (if i < lowWidth then low.getLsbD i else high.getLsbD (i-lowWidth))) :
    output = high ++ low := by
  apply from_bits
  intro i within
  rw [bits i within,BitVec.getLsbD_append]

end Pinwheel.Hardware.StreamingMapped.Word
