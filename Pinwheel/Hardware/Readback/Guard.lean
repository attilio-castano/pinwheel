import Pinwheel.Hardware.Readback.Boolean

/-! Local Boolean facts for replaying propositional resolution over mux guards.
Word-valued data and comparisons may remain arbitrary atoms. -/
namespace Pinwheel.Hardware.Readback.Guard

theorem ext {x y : BitVec 1} (h : (x = 1) ↔ (y = 1)) : x = y := by
  revert x y
  decide +kernel

theorem extWord {x y : BitVec w} (h : ∀ z, (x = z) ↔ (y = z)) : x = y :=
  ((h x).mp rfl).symm

theorem band (a b : BitVec 1) :
    (a &&& b = 1) ↔ (if a = 1 then b = 1 else False) := by
  revert a b
  decide +kernel

theorem bor (a b : BitVec 1) :
    (a ||| b = 1) ↔ (if a = 1 then True else b = 1) := by
  revert a b
  decide +kernel

theorem inv (a : BitVec 1) :
    (~~~a = 1) ↔ (if a = 1 then False else True) := by
  revert a
  decide +kernel

theorem ofDecide (p : Prop) [Decidable p] : (BitVec.ofBool (decide p) = 1) ↔ p := by
  by_cases h : p <;> simp [h]

theorem mux (g : BitVec 1) (a b z : BitVec w) :
    ((if g = 1 then a else b) = z) ↔ (if g = 1 then a = z else b = z) := by
  split <;> rfl

theorem clauses {g t e q : Prop} [Decidable g] (h : q ↔ if g then t else e) :
    (g → t → ¬q → False) ∧ (g → ¬t → q → False) ∧
    (¬g → e → ¬q → False) ∧ (¬g → ¬e → q → False) := by
  by_cases hg : g <;> simp_all

end Pinwheel.Hardware.Readback.Guard
