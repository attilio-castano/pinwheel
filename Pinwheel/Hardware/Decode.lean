import Pinwheel.Hardware.Circuit
import Pinwheel.Hardware.Encoding

namespace Pinwheel.Hardware.Decode

structure Fields where
  kind : BitVec 2 -- 1 action, 2 halt, 3 fault
  levels : BitVec 3
  duration : BitVec 8
  capture : Bool
  slot : BitVec 3
  deriving DecidableEq, Repr

def Fields.instruction (d : Fields) : Option Engine.Instruction :=
  if d.kind = 1 then some (.action ⟨d.levels, d.duration.toFin,
    if d.capture then some d.slot.toFin else none⟩)
  else if d.kind = 2 then some .halt else none

def value (word : BitVec 16) : Fields where
  kind := if word[15] then (if word = 0x8000 then 2 else 3)
    else if word[3] then 1 else if word.extractLsb' 0 3 = 0 then 1 else 3
  levels := word.extractLsb' 12 3
  duration := word.extractLsb' 4 8
  capture := word[3]
  slot := word.extractLsb' 0 3

inductive Port : Nat → Type where
  | kind : Port 2
  | levels : Port 3
  | duration : Port 8
  | capture : Port 1
  | slot : Port 3

def Fields.values (d : Fields) : Values Port
  | _, .kind => d.kind
  | _, .levels => d.levels
  | _, .duration => d.duration
  | _, .capture => BitVec.ofBool d.capture
  | _, .slot => d.slot

/-- Stateless decoder logic, reusable inside any circuit with a 16-bit word signal. -/
def logic (word : Expr I R 16) : {w : Nat} → Port w → Expr I R w
  | _, .kind => .mux (.slice 15 1 (by decide) word)
      (.mux (.equal word (.lit 0x8000)) (.lit 2) (.lit 3))
      (.mux (.slice 3 1 (by decide) word) (.lit 1)
        (.mux (.zero (.slice 0 3 (by decide) word)) (.lit 1) (.lit 3)))
  | _, .levels => .slice 12 3 (by decide) word
  | _, .duration => .slice 4 8 (by decide) word
  | _, .capture => .slice 3 1 (by decide) word
  | _, .slot => .slice 0 3 (by decide) word

def observe (outputs : Values Port) : Fields :=
  ⟨outputs .kind, outputs .levels, outputs .duration, decide (outputs .capture = 1), outputs .slot⟩

theorem value_correct (word : BitVec 16) : (value word).instruction = Encoding.decode word := by
  simp only [value, Fields.instruction, Encoding.decode]
  by_cases hop : word[15] = true <;> by_cases halt : word = 0x8000 <;>
    by_cases cap : word[3] = true <;> by_cases slot : word.extractLsb' 0 3 = 0 <;> simp_all

theorem extract_bit (word : BitVec w) (i : Nat) (hi : i < w) :
    word.extractLsb' i 1 = BitVec.ofBool word[i] := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hk0 : k = 0 := by omega
  simp [hk0, BitVec.getLsbD_eq_getElem, hi]

@[simp] theorem bool_one (b : Bool) : BitVec.ofBool b = 1#1 ↔ b = true := by
  cases b <;> decide

@[simp] theorem test_decide (p : Prop) [Decidable p] : BitVec.ofBool (decide p) = 1#1 ↔ p := by
  by_cases h : p <;> simp [h]

theorem logic_correct (word : Expr I R 16) (inputs : Values I) (registers : Values R) :
    observe (fun p => (logic word p).eval inputs registers) = value (word.eval inputs registers) := by
  simp only [observe, logic, Expr.eval]
  simp [extract_bit (word.eval inputs registers) 15 (by decide), extract_bit (word.eval inputs registers) 3 (by decide), value]
  grind

theorem logic_values_correct (word : Expr I R 16) (inputs : Values I) (registers : Values R)
    (port : Port w) :
    (logic word port).eval inputs registers = (value (word.eval inputs registers)).values port := by
  cases port <;> simp [logic, Expr.eval, Fields.values, value,
    extract_bit (word.eval inputs registers) 15 (by decide),
    extract_bit (word.eval inputs registers) 3 (by decide)]
  by_cases halt : word.eval inputs registers = 32768#16 <;>
    by_cases slot : (word.eval inputs registers).extractLsb' 0 3 = 0#3 <;> simp_all

end Pinwheel.Hardware.Decode
