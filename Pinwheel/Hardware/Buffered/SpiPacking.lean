import Init

/-! The finite SPI datapath representation, independently of either execution
semantics. TX lists use least-significant-bit-first consumption order. RX lists
are packed in arrival order, and bits above the retained prefix are zero. -/
namespace Pinwheel.Hardware.Buffered.SpiPacking

/-- A bounded prefix of a packed word in engine-consumption order. -/
def txBits (word : BitVec 32) (length : Nat) : List Bool :=
  List.ofFn fun k : Fin length => word.getLsbD k.val

/-- Canonical packed RX prefix. The 32-bit representation truncates only when
the caller exceeds the physical capacity; admitted executions prove that bound.
-/
def rxWord (bits : List Bool) : BitVec 32 :=
  (BitVec.ofBoolListLE bits).setWidth 32

/-- Every physical bit is the corresponding prefix element, with false padding.
-/
theorem rxWord_getLsbD (bits : List Bool) (index : Nat) (valid : index < 32) :
    (rxWord bits).getLsbD index = bits.getD index false := by
  simp [rxWord, valid]

@[simp] theorem rxWord_empty : rxWord [] = 0 := by
  simp [rxWord, BitVec.ofBoolListLE]

theorem rxWord_above_prefix (bits : List Bool) (index : Nat) (above : bits.length ≤ index) :
    (rxWord bits).getLsbD index = false := by
  simp [rxWord, List.getD_eq_getElem?_getD, List.getElem?_eq_none above]

@[simp] theorem length_txBits (word : BitVec 32) (length : Nat) :
    (txBits word length).length = length := by
  simp [txBits]

@[simp] theorem txBits_getElem? (word : BitVec 32) (length index : Nat) :
    (txBits word length)[index]? =
      if index < length then some (word.getLsbD index) else none := by
  simp [txBits]

/-- The source's optional indexed TX lookup is exactly the packed payload bit
while the logical TX request still has a bit to consume. -/
theorem txBits_getD (word : BitVec 32) (length index : Nat) (available : index < length) :
    (txBits word length).getD index false = word.getLsbD index := by
  simp [txBits, List.getD_eq_getElem?_getD, available]

/-- Keep the complete payload as a ghost: unused high bits need not be zero.
Only the currently meaningful low bit is equated to the logical source list.
-/
theorem tx_shift_low_bit (payload : BitVec 32) (length consumed : Nat)
    (available : consumed < length) :
    (payload >>> consumed).getLsbD 0 =
      (txBits payload length).getD consumed false := by
  simp only [BitVec.getLsbD_ushiftRight, Nat.add_zero,
    txBits_getD payload length consumed available]

/-- Logical suffixes agree with the meaningful prefix of the shifted full
payload. This deliberately does not reconstruct the complete shift register.
-/
theorem txBits_drop (payload : BitVec 32) (length consumed : Nat) :
    (txBits payload length).drop consumed =
      txBits (payload >>> consumed) (length - consumed) := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_drop, txBits_getElem?, BitVec.getLsbD_ushiftRight]
  have condition : consumed + index < length ↔ index < length - consumed := by omega
  simp only [condition]
  done

/-- Packing and unpacking retains every admitted RX prefix element. -/
theorem rxWord_roundTrip (bits : List Bool) (bounded : bits.length ≤ 32) :
    txBits (rxWord bits) bits.length = bits := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < bits.length
  · rw [txBits_getElem?, if_pos inside, rxWord_getLsbD bits index (by omega)]
    simp [List.getD_eq_getElem?_getD, inside]
    done
  · simp [txBits, inside]
  done

/-- At a valid packed bit, appending changes exactly the next prefix position.
No bound on the list is needed for this local bit equation. -/
theorem rxWord_append_getLsbD (bits : List Bool) (bit : Bool) (index : Nat)
    (valid : index < 32) :
    (rxWord (bits ++ [bit])).getLsbD index =
      if index = bits.length then bit else (rxWord bits).getLsbD index := by
  simp only [rxWord, BitVec.getLsbD_setWidth, valid, decide_true,
    Bool.true_and, BitVec.getLsbD_ofBoolListLE]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  by_cases before : index < bits.length
  · simp [before, Nat.ne_of_lt before]
  · by_cases next : index = bits.length
    · simp [next]
    · simp [before, next,
        List.getElem?_eq_none (by simp; omega : [bit].length ≤ index - bits.length)]
  done

end Pinwheel.Hardware.Buffered.SpiPacking
