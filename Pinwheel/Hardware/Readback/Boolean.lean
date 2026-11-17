import Pinwheel.Hardware.Circuit

namespace Pinwheel.Hardware.Readback

/-- Synthesis reduces an unsigned comparison against zero to the input bit. -/
theorem zero_lt_bit (x : BitVec 1) :
    BitVec.ofBool (decide ((0#1).toNat < x.toNat)) = x := by
  revert x
  decide +kernel

theorem eq_bits (x y : BitVec w) :
    x = y ↔ ∀ k : Fin w, x.getLsbD k.val = y.getLsbD k.val := by
  constructor
  · intro h
    subst y
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    exact h ⟨k, hk⟩

end Pinwheel.Hardware.Readback
