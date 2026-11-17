import Pinwheel.Hardware.Readback.Boolean

/-! Ordinary-kernel algebra for one-bit-controlled mux networks. These laws
avoid enumerating all combinations of a wide priority selector. Payloads have
arbitrary types; no circuit invariant, selector exclusivity, or reachability
hypothesis is used. -/
namespace Pinwheel.Hardware.Readback.Mux

theorem bitOrOne (a b : BitVec 1) : (a ||| b = 1) ↔ a = 1 ∨ b = 1 := by
  revert a b
  decide +kernel

theorem bitAndOne (a b : BitVec 1) : (a &&& b = 1) ↔ a = 1 ∧ b = 1 := by
  revert a b
  decide +kernel

theorem bitNotOne (a : BitVec 1) : (~~~a = 1) ↔ ¬a = 1 := by
  revert a
  decide +kernel

theorem orIte {α : Sort u} (p q : Prop) [Decidable p] [Decidable q] (x y : α) :
    (if p ∨ q then x else y) = (if p then x else if q then x else y) := by
  by_cases hp : p <;> simp [hp]

theorem orSelect {α : Sort u} (a b : BitVec 1) (x y : α) :
    (if a ||| b = 1 then x else y) = (if a = 1 then x else if b = 1 then x else y) := by
  simp only [bitOrOne,orIte]

theorem notSelect {α : Sort u} (a : BitVec 1) (x y : α) :
    (if ~~~a = 1 then x else y) = (if a = 1 then y else x) := by
  simp only [bitNotOne,ite_not]

end Pinwheel.Hardware.Readback.Mux
