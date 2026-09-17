import Pinwheel.Hardware.Circuit

namespace Pinwheel.Hardware.Readback

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
