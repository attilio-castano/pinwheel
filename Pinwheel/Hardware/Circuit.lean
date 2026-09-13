import Std

namespace Pinwheel.Hardware

/-- Width-indexed signal values; an input/register can only be read at its declared width. -/
abbrev Values (Signal : Nat → Type) := {w : Nat} → Signal w → BitVec w

/-- Finite expression trees have no combinational cycles. Registers refer to pre-edge values. -/
inductive Expr (Input Register : Nat → Type) : Nat → Type where
  | input : Input w → Expr Input Register w
  | reg : Register w → Expr Input Register w
  | lit : BitVec w → Expr Input Register w
  | inv : Expr Input Register w → Expr Input Register w
  | band : Expr Input Register w → Expr Input Register w → Expr Input Register w
  | sub : Expr Input Register w → Expr Input Register w → Expr Input Register w
  | zero : Expr Input Register w → Expr Input Register 1
  | mux : Expr Input Register 1 → Expr Input Register w → Expr Input Register w → Expr Input Register w

def Expr.eval (inputs : Values I) (registers : Values R) : Expr I R w → BitVec w
  | .input i => inputs i
  | .reg r => registers r
  | .lit v => v
  | .inv x => ~~~x.eval inputs registers
  | .band x y => x.eval inputs registers &&& y.eval inputs registers
  | .sub x y => x.eval inputs registers - y.eval inputs registers
  | .zero x => BitVec.ofBool (decide (x.eval inputs registers = 0))
  | .mux c t f => if c.eval inputs registers = 1 then t.eval inputs registers else f.eval inputs registers

/-- Every next-register expression is evaluated against one shared input/pre-edge snapshot. -/
structure Circuit (Input Register Output : Nat → Type) where
  next : {w : Nat} → Register w → Expr Input Register w
  output : {w : Nat} → Output w → Expr Input Register w

def Circuit.step (c : Circuit I R O) (inputs : Values I) (registers : Values R) : Values R :=
  fun r => (c.next r).eval inputs registers

def Circuit.observe (c : Circuit I R O) (inputs : Values I) (registers : Values R) : Values O :=
  fun o => (c.output o).eval inputs registers

/-- Arithmetic is modular at the declared width; the countdown must guard zero. -/
theorem byte_decrement_wrap (inputs : Values I) (registers : Values R) :
    (Expr.sub (.lit (0 : BitVec 8)) (.lit 1)).eval inputs registers = 255 := rfl

end Pinwheel.Hardware
