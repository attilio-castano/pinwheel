import Pinwheel.Program.StreamingQueue

/-! Bit-order specifications. Lists here are proof traces, never runtime storage. -/
namespace Pinwheel.Program.Streaming.Packing

def txBits (word : BitVec 32) (length : Nat) : List Bool :=
  List.ofFn fun k : Fin length => word.getMsbD k.val

def rxBits (word : BitVec 32) (length : Nat) : List Bool :=
  List.ofFn fun k : Fin length => word.getLsbD (length - 1 - k.val)

def rxWord (bits : List Bool) : BitVec 32 := (BitVec.ofBoolListBE bits).setWidth 32

@[simp] theorem txBits_length (word : BitVec 32) (length : Nat) : (txBits word length).length = length := by
  simp [txBits]

@[simp] theorem rxBits_length (word : BitVec 32) (length : Nat) : (rxBits word length).length = length := by
  simp [rxBits]

@[simp] theorem txBits_zero (word : BitVec 32) : txBits word 0 = [] := by
  simp [txBits]

@[simp] theorem rxBits_zero (word : BitVec 32) : rxBits word 0 = [] := by
  simp [rxBits]

@[simp] theorem txBits_getElem? (word : BitVec 32) (length index : Nat) :
    (txBits word length)[index]? = if index < length then some (word.getMsbD index) else none := by
  simp [txBits]

@[simp] theorem rxBits_getElem? (word : BitVec 32) (length index : Nat) :
    (rxBits word length)[index]? =
      if index < length then some (word.getLsbD (length - 1 - index)) else none := by
  simp [rxBits]

theorem txBits_drop (word : BitVec 32) (length consumed : Nat) :
    (txBits word length).drop consumed = txBits (word <<< consumed) (length - consumed) := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_drop, txBits_getElem?, BitVec.getMsbD_shiftLeft]
  simp [show consumed + index < length ↔ index < length - consumed by omega, Nat.add_comm]

theorem txBits_first (word : BitVec 32) (length : Nat) (nonempty : 0 < length) :
    (txBits word length).head? = some word[31] := by
  simp [txBits, List.head?_eq_getElem?, nonempty, BitVec.getMsbD_eq_getLsbD]

theorem txBits_cons (word : BitVec 32) (length : Nat) (nonempty : 0 < length) :
    txBits word length = word[31] :: txBits (word <<< 1) (length - 1) := by
  rw [← txBits_drop word length 1]
  obtain ⟨tail, same⟩ := List.head?_eq_some_iff.mp (txBits_first word length nonempty)
  rw [same]
  rfl

@[simp] theorem rxWord_empty : rxWord [] = 0 := by
  rfl

theorem rxWord_roundtrip (bits : List Bool) (bounded : bits.length ≤ 32) :
    rxBits (rxWord bits) bits.length = bits := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < bits.length
  · have address : bits.length - 1 - index < bits.length := by omega
    have reflect : bits.length - 1 - (bits.length - 1 - index) = index := by omega
    rw [rxBits_getElem?, if_pos inside]
    simp [inside, rxWord, Nat.lt_of_lt_of_le address bounded, address, reflect]
  · simp [rxBits, inside]

theorem rxWord_append (bits : List Bool) (bit : Bool) :
    rxWord (bits ++ [bit]) = (rxWord bits <<< 1) ||| BitVec.ofNat 32 (if bit then 1 else 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  cases index with
  | zero => cases bit <;> simp [rxWord, List.getD_eq_getElem?_getD]
  | succ index =>
    simp [rxWord, within, List.getD_eq_getElem?_getD]
    by_cases inside : index < bits.length
    · rw [List.getElem?_append_left (by omega)]
      have address : bits.length - (index + 1) = bits.length - 1 - index := by omega
      cases bit <;> simp [inside, address, BitVec.getElem_eq_testBit_toNat,
        Nat.testBit_one_eq_true_iff_self_eq_zero]
    · have high : Nat.testBit 1 (index + 1) = false := by
        apply Bool.eq_false_iff.mpr
        intro truth
        exact Nat.succ_ne_zero index (Nat.testBit_one_eq_true_iff_self_eq_zero.mp truth)
      cases bit <;> simp [inside, BitVec.getElem_eq_testBit_toNat, high]

theorem rxBits_capture (word : BitVec 32) (length : Nat) (bit : Bool)
    (bounded : length < 32) :
    rxBits ((word <<< 1) ||| BitVec.ofNat 32 (if bit then 1 else 0)) (length + 1) =
      rxBits word length ++ [bit] := by
  apply List.ext_getElem?
  intro index
  by_cases before : index < length
  · rw [rxBits_getElem?, if_pos (by omega), List.getElem?_append_left (by simpa), rxBits_getElem?, if_pos before]
    have address : length - index - 1 = length - 1 - index := by omega
    cases bit <;> simp [show length - index < 32 by omega,
      show ¬length - index < 1 by omega, show length - index ≠ 0 by omega, address]
    all_goals rw [BitVec.getLsbD_eq_getElem]
  · by_cases last : index = length
    · subst index
      rw [rxBits_getElem?, if_pos (by omega), List.getElem?_append_right (by simp)]
      cases bit <;> simp
    · have beyond : length + 1 ≤ index := by omega
      simp_all

end Pinwheel.Program.Streaming.Packing
