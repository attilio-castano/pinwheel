import Pinwheel.Hardware.Readback.Boolean

namespace Pinwheel.Hardware.Streaming.Readback

/-- CIRCT's most-significant-bit form of the seven-bit credit comparison. -/
theorem lt64 : ∀ x : BitVec 7,
    BitVec.ofBool (decide (x.toNat < (64#7).toNat)) = ~~~(x.extractLsb' 6 1) := by
  decide +kernel

theorem lt32 : ∀ x : BitVec 7,
    BitVec.ofBool (decide (x.toNat < (32#7).toNat)) =
      BitVec.ofBool (decide (x.extractLsb' 5 2 = 0#2)) := by
  decide +kernel

theorem lt16 : ∀ x : BitVec 7,
    BitVec.ofBool (decide (x.toNat < (16#7).toNat)) =
      BitVec.ofBool (decide (x.extractLsb' 4 3 = 0#3)) := by
  decide +kernel

theorem lt8 : ∀ x : BitVec 7,
    BitVec.ofBool (decide (x.toNat < (8#7).toNat)) =
      BitVec.ofBool (decide (x.extractLsb' 3 4 = 0#4)) := by
  decide +kernel

theorem lt4 : ∀ x : BitVec 7,
    BitVec.ofBool (decide (x.toNat < (4#7).toNat)) =
      BitVec.ofBool (decide (x.extractLsb' 2 5 = 0#5)) := by
  decide +kernel

theorem lt2 : ∀ x : BitVec 7,
    BitVec.ofBool (decide (x.toNat < (2#7).toNat)) =
      BitVec.ofBool (decide (x.extractLsb' 1 6 = 0#6)) := by
  decide +kernel

theorem lt1 : ∀ x : BitVec 7,
    BitVec.ofBool (decide (x.toNat < (1#7).toNat)) =
      BitVec.ofBool (decide (x.extractLsb' 0 7 = 0#7)) := by
  decide +kernel

theorem count_lt2 : ∀ x : BitVec 4,
    BitVec.ofBool (decide (x.toNat < (2#4).toNat)) =
      BitVec.ofBool (decide (x.extractLsb' 1 3 = 0#3)) := by
  decide +kernel

theorem count_lt4 : ∀ x : BitVec 4,
    BitVec.ofBool (decide (x.toNat < (4#4).toNat)) =
      BitVec.ofBool (decide (x.extractLsb' 2 2 = 0#2)) := by
  decide +kernel

end Pinwheel.Hardware.Streaming.Readback
