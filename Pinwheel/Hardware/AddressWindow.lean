import Pinwheel.Hardware.WordOps

/-! Complete-footprint range checks using widened arithmetic. Window upper
bounds may equal `2^w`; addresses and access endpoints never narrow before the
check. The combinational implementation uses only existing expression forms. -/
namespace Pinwheel.Hardware.AddressWindow

structure Window (w : Nat) where
  lower : Nat
  upper : Nat
  ordered : lower ≤ upper
  bounded : upper ≤ 2^w

def check (w lower upper : Nat) : Option (Window w) :=
  if h : lower ≤ upper ∧ upper ≤ 2^w then some ⟨lower, upper, h.1, h.2⟩ else none

structure Footprint (w : Nat) where
  bytes : Nat
  positive : 0 < bytes
  bounded : bytes ≤ 2^w

def Contains (window : Window w) (footprint : Footprint w) (address : BitVec w) : Prop :=
  window.lower ≤ address.toNat ∧ address.toNat + footprint.bytes ≤ window.upper

instance (window : Window w) (footprint : Footprint w) (address : BitVec w) :
    Decidable (Contains window footprint address) := inferInstanceAs (Decidable (_ ∧ _))

def widen (address : Expr I R w) : Expr I R (w+1) :=
  WordOps.cast (by omega) (.concat (.lit (0#1)) address)

def covers (window : Window w) (footprint : Footprint w) (address : Expr I R w) : Expr I R 1 :=
  .band (.inv (.ult (widen address) (.lit (BitVec.ofNat (w+1) window.lower))))
    (.inv (.ult (.lit (BitVec.ofNat (w+1) window.upper))
      (WordOps.add (widen address) (.lit (BitVec.ofNat (w+1) footprint.bytes)))))

/-- The local address is meaningful only after the complete-footprint check. -/
def offset (window : Window w) (address : Expr I R w) : Expr I R w :=
  .sub address (.lit (BitVec.ofNat w window.lower))

@[simp] theorem widen_eval (address : Expr I R w) (i : Values I) (s : Values R) :
    (widen address).eval i s = (address.eval i s).setWidth (w+1) := by
  simp [widen, Expr.eval, ← BitVec.toNat_inj]

theorem covers_eval (window : Window w) (footprint : Footprint w)
    (address : Expr I R w) (i : Values I) (s : Values R) :
    (covers window footprint address).eval i s =
      BitVec.ofBool (decide (Contains window footprint (address.eval i s))) := by
  simp only [covers, Expr.eval, widen_eval, WordOps.add_eval]
  simp only [BitVec.toNat_setWidth_of_le (by omega : w ≤ w+1), BitVec.toNat_ofNat, BitVec.toNat_add, Contains]
  have hp : 2^w < 2^(w+1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self w)
  have bounds := And.intro (Nat.lt_of_le_of_lt (Nat.le_trans window.ordered window.bounded) hp)
    (And.intro (Nat.lt_of_le_of_lt window.bounded hp) (Nat.lt_of_le_of_lt footprint.bounded hp))
  have sumBound : (address.eval i s).toNat + footprint.bytes < 2^(w+1) := by
    simpa only [Nat.pow_succ, Nat.mul_two] using
      Nat.add_lt_add_of_lt_of_le (address.eval i s).isLt footprint.bounded
  simp [Nat.mod_eq_of_lt bounds.1, Nat.mod_eq_of_lt bounds.2.1,
    Nat.mod_eq_of_lt bounds.2.2, Nat.mod_eq_of_lt sumBound, BitVec.not_ofBool]
  simp [← decide_not, Nat.not_lt]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  exact decide_eq_true_iff.symm

theorem check_some_iff (w lower upper : Nat) :
    (check w lower upper).isSome ↔ lower ≤ upper ∧ upper ≤ 2^w := by
  simp [check]

theorem covers_one_iff (window : Window w) (footprint : Footprint w)
    (address : Expr I R w) (i : Values I) (s : Values R) :
    (covers window footprint address).eval i s = 1 ↔ Contains window footprint (address.eval i s) := by
  rw [covers_eval]
  exact (BitVec.ofBool_eq_iff_eq (b := decide (Contains window footprint (address.eval i s)))
    (b' := true)).trans decide_eq_true_iff

theorem endpoint_le (window : Window w) (footprint : Footprint w) (address : BitVec w)
    (h : Contains window footprint address) : address.toNat + footprint.bytes ≤ 2^w :=
  Nat.le_trans h.2 window.bounded

theorem contains_address (window : Window w) (footprint : Footprint w) (address : BitVec w)
    (h : Contains window footprint address) : window.lower ≤ address.toNat ∧ address.toNat < window.upper := by
  have := footprint.positive
  have := h.2
  exact ⟨h.1, by omega⟩

theorem offset_eval_toNat (window : Window w) (footprint : Footprint w)
    (address : Expr I R w) (i : Values I) (s : Values R)
    (h : Contains window footprint (address.eval i s)) :
    ((offset window address).eval i s).toNat = (address.eval i s).toNat - window.lower := by
  have lowerBound : window.lower < 2^w := Nat.lt_of_le_of_lt h.1 (address.eval i s).isLt
  have lowLe : (BitVec.ofNat w window.lower) ≤ address.eval i s := by
    change window.lower % 2^w ≤ (address.eval i s).toNat
    simpa only [Nat.mod_eq_of_lt lowerBound] using h.1
  simp only [offset, Expr.eval, BitVec.toNat_sub_of_le lowLe, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lowerBound]

theorem covers_bind_eval (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (window : Window w) (footprint : Footprint w)
    (address : Expr I R w) (i : Values J) (s : Values S) :
    ((covers window footprint address).bind input register).eval i s =
      (covers window footprint (address.bind input register)).eval i s := by
  simp only [Expr.eval_bind, covers_eval]

end Pinwheel.Hardware.AddressWindow
