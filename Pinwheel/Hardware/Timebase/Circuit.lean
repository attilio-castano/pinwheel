import Pinwheel.Hardware.Timebase.Fractional
import Pinwheel.Hardware.AddressWindow

namespace Pinwheel.Hardware.Timebase

/-- Use an extra bit for the addition before testing and removing a full period. -/
def sum (phase : Expr I R (w + 1)) (denominator : Expr I R w) : Expr I R (w + 1) :=
  WordOps.add phase (AddressWindow.widen denominator)

def beatExpr (phase : Expr I R (w + 1)) (numerator denominator : Expr I R w) : Expr I R 1 :=
  .inv (.ult (sum phase denominator) (AddressWindow.widen numerator))

def advanceExpr (phase : Expr I R (w + 1)) (numerator denominator : Expr I R w) :
    Expr I R (w + 1) :=
  let total := sum phase denominator
  .mux (beatExpr phase numerator denominator)
    (.sub total (AddressWindow.widen numerator)) total

private theorem widened_toNat (x : Expr I R w) (i : Values I) (s : Values R) :
    ((AddressWindow.widen x).eval i s).toNat = (x.eval i s).toNat := by
  simp [AddressWindow.widen_eval, BitVec.toNat_setWidth_of_le (by omega : w ≤ w + 1)]

private theorem sum_toNat (p : Period)
    (phase : Expr I R (w + 1)) (numerator denominator : Expr I R w)
    (i : Values I) (s : Values R)
    (hp : (numerator.eval i s).toNat = p.numerator)
    (hq : (denominator.eval i s).toNat = p.denominator)
    (validPhase : (phase.eval i s).toNat < p.numerator) :
    ((sum phase denominator).eval i s).toNat = (phase.eval i s).toNat + p.denominator := by
  have numFits := (numerator.eval i s).isLt
  have denFits := (denominator.eval i s).isLt
  have wide : (phase.eval i s).toNat + p.denominator < 2 ^ (w + 1) := by
    rw [Nat.pow_succ]
    omega
  simp only [sum, WordOps.add_eval, BitVec.toNat_add, widened_toNat, hq, Nat.mod_eq_of_lt wide]

/-- The physical comparison and next-phase expression implement the rational
step for any period fitting the interface and any valid pre-edge phase. -/
theorem expressions_correct (p : Period)
    (phase : Expr I R (w + 1)) (numerator denominator : Expr I R w)
    (i : Values I) (s : Values R)
    (hp : (numerator.eval i s).toNat = p.numerator)
    (hq : (denominator.eval i s).toNat = p.denominator)
    (validPhase : (phase.eval i s).toNat < p.numerator) :
    (beatExpr phase numerator denominator).eval i s = BitVec.ofBool (beat p (phase.eval i s).toNat) ∧
      ((advanceExpr phase numerator denominator).eval i s).toNat =
        advance p (phase.eval i s).toNat := by
  have total := sum_toNat p phase numerator denominator i s hp hq validPhase
  have event : (beatExpr phase numerator denominator).eval i s =
      BitVec.ofBool (beat p (phase.eval i s).toNat) := by
    simp only [beatExpr, Expr.eval, total, widened_toNat, hp, beat, BitVec.not_ofBool, ← decide_not, Nat.not_lt]
  refine ⟨event, ?_⟩
  have num := widened_toNat numerator i s
  by_cases fire : p.numerator ≤ (phase.eval i s).toNat + p.denominator
  · have canSubtract :
        (AddressWindow.widen numerator).eval i s ≤ (sum phase denominator).eval i s := by
      simpa only [BitVec.le_def, num, hp, total] using fire
    simp only [advanceExpr, Expr.eval, event, advance, beat, fire, decide_true, BitVec.ofBool_true,
      eq_self, if_true, BitVec.toNat_sub_of_le canSubtract, total, num, hp]
  · simp only [advanceExpr, Expr.eval, event, advance, beat, fire, decide_false, BitVec.ofBool_false,
      show (0 : BitVec 1) ≠ 1 from by decide, Bool.false_eq_true, if_false, total]
  done

end Pinwheel.Hardware.Timebase
