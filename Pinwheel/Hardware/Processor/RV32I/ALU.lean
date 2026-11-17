import Pinwheel.Hardware.WordALU
import Pinwheel.Hardware.Processor.RV32I.Semantics

/-! RV32I adapters for the generic word ALU. The explicit word-register adapter
uses only rhs[4:0] as its shift amount. Immediate arithmetic sign-extends all
twelve immediate bits, including SLTIU. No decoding, register file, retirement,
fetch, or memory behavior is introduced here.
-/
namespace Pinwheel.Hardware.Processor.RV32I.ALU

def registerOp : RegisterOp → WordALU.Op
  | .add => .add | .sub => .sub | .sll => .shiftLeft | .slt => .signedLess
  | .sltu => .unsignedLess | .bitXor => .bitXor | .srl => .shiftRight
  | .sra => .arithmeticRight | .bitOr => .bitOr | .bitAnd => .bitAnd

def immediateOp : ImmediateOp → WordALU.Op
  | .add => .add | .slt => .signedLess | .sltu => .unsignedLess
  | .bitXor => .bitXor | .bitOr => .bitOr | .bitAnd => .bitAnd

def shiftOp : ShiftOp → WordALU.Op
  | .left => .shiftLeft | .rightLogical => .shiftRight | .rightArithmetic => .arithmeticRight

/-- Runtime control uses the generic ALU encoding, not raw RISC-V funct fields. -/
def value (selector : Expr I R 4) (left right : Expr I R 32) : Expr I R 32 :=
  WordALU.value selector left right (.slice 0 5 (by decide) right)

def valid (selector : Expr I R 4) : Expr I R 1 := WordALU.valid selector

def register (op : RegisterOp) (left right : Expr I R 32) : Expr I R 32 :=
  value (.lit (registerOp op).code) left right

def extendImmediate (bits : Expr I R 12) : Expr I R 32 :=
  .concat (.mux (WordOps.signBit bits) (.lit (BitVec.allOnes 20)) (.lit 0)) bits

def immediate (op : ImmediateOp) (left : Expr I R 32) (bits : Expr I R 12) : Expr I R 32 :=
  WordALU.value (.lit (immediateOp op).code) left (extendImmediate bits) (.lit (0#5))

def shiftImmediate (op : ShiftOp) (left : Expr I R 32) (amount : Expr I R 5) : Expr I R 32 :=
  WordALU.value (.lit (shiftOp op).code) left (.lit 0) amount

@[simp] theorem extendImmediate_eval (bits : Expr I R 12) (i : Values I) (s : Values R) :
    (extendImmediate bits).eval i s = signedImmediate (bits.eval i s) := by
  rw [signedImmediate, BitVec.signExtend_eq_append_of_le (by decide : 12 ≤ 32)]
  simp only [extendImmediate, Expr.eval, WordOps.signBit_eval]
  cases (bits.eval i s).msb <;> rfl

@[simp] theorem value_eval (selector : Expr I R 4) (left right : Expr I R 32)
    (i : Values I) (s : Values R) :
    (value selector left right).eval i s = WordALU.evaluate (selector.eval i s)
      (left.eval i s) (right.eval i s) ((right.eval i s).extractLsb' 0 5) := by
  simp only [value, WordALU.value_eval, Expr.eval]

@[simp] theorem valid_eval (selector : Expr I R 4) (i : Values I) (s : Values R) :
    (valid selector).eval i s = BitVec.ofBool (WordALU.legal (selector.eval i s)) :=
  WordALU.valid_eval selector i s

@[simp] theorem register_eval (op : RegisterOp) (left right : Expr I R 32)
    (i : Values I) (s : Values R) :
    (register op left right).eval i s = Semantics.registerALU op (left.eval i s) (right.eval i s) := by
  cases op <;> simp [register, value_eval, Expr.eval, WordALU.evaluate, WordALU.evaluateOp,
    registerOp, Semantics.registerALU, Semantics.shift, Semantics.bit, Semantics.signedLess, BitVec.ult]

@[simp] theorem immediate_eval (op : ImmediateOp) (left : Expr I R 32) (bits : Expr I R 12)
    (i : Values I) (s : Values R) :
    (immediate op left bits).eval i s = Semantics.immediateALU op (left.eval i s) (bits.eval i s) := by
  cases op <;> simp [immediate, Expr.eval, WordALU.evaluate, WordALU.evaluateOp,
    immediateOp, Semantics.immediateALU, Semantics.bit, Semantics.signedLess, BitVec.ult]

@[simp] theorem shiftImmediate_eval (op : ShiftOp) (left : Expr I R 32) (amount : Expr I R 5)
    (i : Values I) (s : Values R) :
    (shiftImmediate op left amount).eval i s = Semantics.shift op (left.eval i s) (amount.eval i s) := by
  cases op <;> simp [shiftImmediate, Expr.eval, WordALU.evaluate, WordALU.evaluateOp, shiftOp, Semantics.shift]

theorem register_valid (op : RegisterOp) (i : Values I) (s : Values R) :
    (valid (Expr.lit (registerOp op).code)).eval i s = 1 := by simp [Expr.eval]

theorem immediate_valid (op : ImmediateOp) (i : Values I) (s : Values R) :
    (valid (Expr.lit (immediateOp op).code)).eval i s = 1 := by simp [Expr.eval]

theorem shiftImmediate_valid (op : ShiftOp) (i : Values I) (s : Values R) :
    (valid (Expr.lit (shiftOp op).code)).eval i s = 1 := by simp [Expr.eval]

theorem reserved_eval (selector : Expr I R 4) (left right : Expr I R 32)
    (i : Values I) (s : Values R) (h : 10 ≤ (selector.eval i s).toNat) :
    (value selector left right).eval i s = 0 ∧ (valid selector).eval i s = 0 :=
  WordALU.reserved_eval selector left right (.slice 0 5 (by decide) right) i s h

theorem value_bind_eval (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (selector : Expr I R 4)
    (left right : Expr I R 32) (i : Values J) (s : Values S) :
    ((value selector left right).bind input register).eval i s =
      (value (selector.bind input register) (left.bind input register) (right.bind input register)).eval i s := by
  simp only [Expr.eval_bind, value_eval]

end Pinwheel.Hardware.Processor.RV32I.ALU
