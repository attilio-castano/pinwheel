import Pinwheel.Hardware.WordOps

/-! A combinational runtime-selected word ALU built entirely from existing
expressions. Operands and the unsigned shift amount have independent widths;
shift amounts are never implicitly masked. Width zero follows BitVec semantics.

The four-bit selector has ten legal encodings, in the order below. Reserved
encodings 10..15 produce value zero and validity zero. Validity reports only
selector legality: overflow and overshifts are defined arithmetic, not faults.
-/
namespace Pinwheel.Hardware.WordALU

inductive Op where
  | add | sub | bitAnd | bitOr | bitXor | signedLess | unsignedLess
  | shiftLeft | shiftRight | arithmeticRight
  deriving DecidableEq, Repr

def Op.code : Op → BitVec 4
  | .add => 0 | .sub => 1 | .bitAnd => 2 | .bitOr => 3 | .bitXor => 4
  | .signedLess => 5 | .unsignedLess => 6 | .shiftLeft => 7
  | .shiftRight => 8 | .arithmeticRight => 9

def decode (selector : BitVec 4) : Option Op :=
  match selector.toNat with
  | 0 => some .add | 1 => some .sub | 2 => some .bitAnd | 3 => some .bitOr
  | 4 => some .bitXor | 5 => some .signedLess | 6 => some .unsignedLess
  | 7 => some .shiftLeft | 8 => some .shiftRight | 9 => some .arithmeticRight
  | _ => none

def legal (selector : BitVec 4) : Bool := decide (selector.toNat < 10)

def evaluateOp (op : Op) (left right : BitVec w) (amount : BitVec n) : BitVec w :=
  match op with
  | .add => left+right
  | .sub => left-right
  | .bitAnd => left &&& right
  | .bitOr => left ||| right
  | .bitXor => left ^^^ right
  | .signedLess => if left.toInt < right.toInt then 1 else 0
  | .unsignedLess => if left.toNat < right.toNat then 1 else 0
  | .shiftLeft => left <<< amount.toNat
  | .shiftRight => left >>> amount.toNat
  | .arithmeticRight => left.sshiftRight amount.toNat

def evaluate (selector : BitVec 4) (left right : BitVec w) (amount : BitVec n) : BitVec w :=
  match decode selector with
  | some op => evaluateOp op left right amount
  | none => 0

def operation (op : Op) (left right : Expr I R w) (amount : Expr I R n) : Expr I R w :=
  match op with
  | .add => WordOps.add left right
  | .sub => .sub left right
  | .bitAnd => .band left right
  | .bitOr => WordOps.wordOr left right
  | .bitXor => WordOps.wordXor left right
  | .signedLess => .mux (WordOps.signedLess left right) (.lit 1) (.lit 0)
  | .unsignedLess => .mux (.ult left right) (.lit 1) (.lit 0)
  | .shiftLeft => WordOps.shiftLeftBy left amount
  | .shiftRight => WordOps.shiftRightBy left amount
  | .arithmeticRight => WordOps.arithmeticRightBy left amount

def operations : List Op := [.add, .sub, .bitAnd, .bitOr, .bitXor, .signedLess,
  .unsignedLess, .shiftLeft, .shiftRight, .arithmeticRight]

def value (selector : Expr I R 4) (left right : Expr I R w) (amount : Expr I R n) : Expr I R w :=
  operations.foldr (fun op rest =>
    .mux (.equal selector (.lit op.code)) (operation op left right amount) rest) (.lit 0)

def valid (selector : Expr I R 4) : Expr I R 1 := .ult selector (.lit 10)

@[simp] theorem operation_eval (op : Op) (left right : Expr I R w) (amount : Expr I R n)
    (i : Values I) (s : Values R) :
    (operation op left right amount).eval i s = evaluateOp op (left.eval i s) (right.eval i s) (amount.eval i s) := by
  cases op <;> simp [operation, evaluateOp, Expr.eval, BitVec.slt]
  all_goals simp only [show (1#1) = BitVec.ofBool true from rfl,
    BitVec.ofBool_eq_iff_eq, decide_eq_true_eq]

theorem selector_cases (selector : BitVec 4) :
    selector = 0 ∨ selector = 1 ∨ selector = 2 ∨ selector = 3 ∨ selector = 4 ∨
    selector = 5 ∨ selector = 6 ∨ selector = 7 ∨ selector = 8 ∨ selector = 9 ∨
    selector = 10 ∨ selector = 11 ∨ selector = 12 ∨ selector = 13 ∨ selector = 14 ∨ selector = 15 := by
  revert selector
  decide +kernel

@[simp] theorem decode_code (op : Op) : decode op.code = some op := by cases op <;> rfl

theorem decode_isSome (selector : BitVec 4) : (decode selector).isSome = legal selector := by
  rcases selector_cases selector with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst selector; rfl

@[simp] theorem value_eval (selector : Expr I R 4) (left right : Expr I R w) (amount : Expr I R n)
    (i : Values I) (s : Values R) :
    (value selector left right amount).eval i s =
      evaluate (selector.eval i s) (left.eval i s) (right.eval i s) (amount.eval i s) := by
  rcases selector_cases (selector.eval i s) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp [value, operations, Expr.eval, h, Op.code, evaluate, decode]

@[simp] theorem valid_eval (selector : Expr I R 4) (i : Values I) (s : Values R) :
    (valid selector).eval i s = BitVec.ofBool (legal (selector.eval i s)) := rfl

theorem decode_none_iff (selector : BitVec 4) : decode selector = none ↔ 10 ≤ selector.toNat := by
  rcases selector_cases selector with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst selector; decide +kernel

theorem code_injective : Function.Injective Op.code := by
  intro a b h
  have he := congrArg decode h
  simpa only [decode_code, Option.some.injEq] using he

@[simp] theorem legal_code (op : Op) : legal op.code = true := by cases op <;> rfl

theorem valid_one_iff (selector : Expr I R 4) (i : Values I) (s : Values R) :
    (valid selector).eval i s = 1 ↔ (decode (selector.eval i s)).isSome = true := by
  rw [valid_eval, decode_isSome]
  simpa using (BitVec.ofBool_eq_iff_eq (b := legal (selector.eval i s)) (b' := true))

theorem selected_eval (selector : Expr I R 4) (left right : Expr I R w) (amount : Expr I R n)
    (i : Values I) (s : Values R) (op : Op) (h : selector.eval i s = op.code) :
    (value selector left right amount).eval i s = evaluateOp op (left.eval i s) (right.eval i s) (amount.eval i s) ∧
      (valid selector).eval i s = 1 := by
  simp [value_eval, valid_eval, h, evaluate]

/-- Every reserved raw code has a deterministic result and deasserted validity;
the operands, amount and raw register state are unrestricted. -/
theorem reserved_eval (selector : Expr I R 4) (left right : Expr I R w) (amount : Expr I R n)
    (i : Values I) (s : Values R) (h : 10 ≤ (selector.eval i s).toNat) :
    (value selector left right amount).eval i s = 0 ∧ (valid selector).eval i s = 0 := by
  have hd := (decode_none_iff (selector.eval i s)).mpr h
  simp [value_eval, valid_eval, evaluate, hd, legal, Nat.not_lt_of_ge h]

theorem value_bind_eval (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (selector : Expr I R 4)
    (left right : Expr I R w) (amount : Expr I R n) (i : Values J) (s : Values S) :
    ((value selector left right amount).bind input register).eval i s =
      (value (selector.bind input register) (left.bind input register)
        (right.bind input register) (amount.bind input register)).eval i s := by
  simp only [Expr.eval_bind, value_eval]

theorem valid_bind_eval (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (selector : Expr I R 4) (i : Values J) (s : Values S) :
    ((valid selector).bind input register).eval i s =
      (valid (selector.bind input register)).eval i s := by
  simp only [Expr.eval_bind, valid_eval]

end Pinwheel.Hardware.WordALU
