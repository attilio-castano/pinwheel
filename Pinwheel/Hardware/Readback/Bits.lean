import Pinwheel.Hardware.Readback.Guard

namespace Pinwheel.Hardware.Readback.Guard

theorem bitExt {x y : BitVec w}
    (h : ∀ k, k < w → (x.getLsbD k = true ↔ y.getLsbD k = true)) : x = y := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  exact Bool.eq_iff_iff.mpr (h k hk)

theorem truthBit (a : BitVec 1) : (a.getLsbD 0 = true) ↔ a = 1 := by
  revert a
  decide +kernel

theorem bitMux (g : BitVec 1) (a b : BitVec w) (k : Nat) :
    ((if g = 1 then a else b).getLsbD k = true) ↔
      (if g = 1 then a.getLsbD k = true else b.getLsbD k = true) := by split <;> rfl

theorem bitAnd (a b : BitVec w) (k : Nat) :
    ((a &&& b).getLsbD k = true) ↔
      (if a.getLsbD k = true then b.getLsbD k = true else False) := by
  cases ha : a.getLsbD k <;> simp [ha]

theorem bitOr (a b : BitVec w) (k : Nat) :
    ((a ||| b).getLsbD k = true) ↔
      (if a.getLsbD k = true then True else b.getLsbD k = true) := by
  cases ha : a.getLsbD k <;> simp [ha]

theorem bitNot (a : BitVec w) (k : Nat) (hk : k < w) :
    ((~~~a).getLsbD k = true) ↔ (if a.getLsbD k = true then False else True) := by
  rw [BitVec.getLsbD_not]; cases a.getLsbD k <;> simp [hk]

theorem bitSlice (a : BitVec w) (start len k : Nat) (hk : k < len) :
    ((a.extractLsb' start len).getLsbD k = true) ↔ a.getLsbD (start+k) = true := by
  simp [hk]

theorem bitLow (a : BitVec w) (b : BitVec v) (k : Nat) (hk : k < v) :
    ((a ++ b).getLsbD k = true) ↔ b.getLsbD k = true := by simp [BitVec.getLsbD_append, hk]

theorem bitHigh (a : BitVec w) (b : BitVec v) (k : Nat) (hk : ¬k < v) :
    ((a ++ b).getLsbD k = true) ↔ a.getLsbD (k-v) = true := by simp [BitVec.getLsbD_append, hk]

end Pinwheel.Hardware.Readback.Guard
