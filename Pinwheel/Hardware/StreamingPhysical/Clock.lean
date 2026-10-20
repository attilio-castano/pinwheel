import Pinwheel.Hardware.StreamingMapped.Boolean

/-! Zero-delay clock-tree semantics. Actual cell and pin inventories are supplied
by a read-back certificate; this model does not assert skew or timing closure. -/
namespace Pinwheel.Hardware.StreamingPhysical

open Pinwheel.Hardware.StreamingMapped

def ClockLevel (expression : Expr 1) (raw : Bool) : Bool :=
  expression.eval (fun _ => raw)

def Rising (before after : Bool) : Prop := before = false ∧ after = true

instance (before after : Bool) : Decidable (Rising before after) :=
  inferInstanceAs (Decidable (before = false ∧ after = true))

/-- Both raw-clock levels are checked from the actual interpreted clock cone. -/
structure PositiveClock (expression : Expr 1) : Prop where
  low : ClockLevel expression false = false
  high : ClockLevel expression true = true

theorem PositiveClock.level {expression : Expr 1} (certificate : PositiveClock expression)
    (raw : Bool) : ClockLevel expression raw = raw :=
  Bool.rec certificate.low certificate.high raw

theorem PositiveClock.rising_iff {expression : Expr 1} (certificate : PositiveClock expression)
    (before after : Bool) :
    Rising (ClockLevel expression before) (ClockLevel expression after) ↔ Rising before after := by
  simp only [certificate.level]

structure InactiveReset (expression : Expr 1) : Prop where
  low : ClockLevel expression false = true
  high : ClockLevel expression true = true

theorem InactiveReset.level {expression : Expr 1} (certificate : InactiveReset expression)
    (raw : Bool) : ClockLevel expression raw = true :=
  Bool.rec certificate.low certificate.high raw

structure Clocking (registers : Nat) where
  clock : Fin registers → Expr 1
  reset : Fin registers → Expr 1
  positive : ∀ index, PositiveClock (clock index)
  inactive : ∀ index, InactiveReset (reset index)

def Clocking.update (clocking : Clocking registers) (before after : Bool)
    (state data : Fin registers → Bool) (index : Fin registers) : Bool :=
  if ClockLevel (clocking.reset index) after = true then
    if Rising (ClockLevel (clocking.clock index) before) (ClockLevel (clocking.clock index) after)
    then data index else state index
  else false

theorem Clocking.update_eq (clocking : Clocking registers) (before after : Bool)
    (state data : Fin registers → Bool) (index : Fin registers) :
    clocking.update before after state data index =
      if Rising before after then data index else state index := by
  simp only [Clocking.update, (clocking.inactive index).level,
    (clocking.positive index).level, ↓reduceIte]

end Pinwheel.Hardware.StreamingPhysical
