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
  | slice (start len : Nat) (fits : start + len ≤ w) : Expr Input Register w → Expr Input Register len
  | equal : Expr Input Register w → Expr Input Register w → Expr Input Register 1
  | ult : Expr Input Register w → Expr Input Register w → Expr Input Register 1
  | zero : Expr Input Register w → Expr Input Register 1
  | mux : Expr Input Register 1 → Expr Input Register w → Expr Input Register w → Expr Input Register w

def Expr.eval (inputs : Values I) (registers : Values R) : Expr I R w → BitVec w
  | .input i => inputs i
  | .reg r => registers r
  | .lit v => v
  | .inv x => ~~~x.eval inputs registers
  | .band x y => x.eval inputs registers &&& y.eval inputs registers
  | .sub x y => x.eval inputs registers - y.eval inputs registers
  | .slice start len _ x => (x.eval inputs registers).extractLsb' start len
  | .equal x y => BitVec.ofBool (decide (x.eval inputs registers = y.eval inputs registers))
  | .ult x y => BitVec.ofBool (decide ((x.eval inputs registers).toNat < (y.eval inputs registers).toNat))
  | .zero x => BitVec.ofBool (decide (x.eval inputs registers = 0))
  | .mux c t f => if c.eval inputs registers = 1 then t.eval inputs registers else f.eval inputs registers

/-- Instantiate a proved subcircuit by replacing its input/register leaves with wires. -/
def Expr.bind (input : {w : Nat} → I w → Expr J S w)
    (register : {w : Nat} → R w → Expr J S w) : Expr I R w → Expr J S w
  | .input i => input i
  | .reg r => register r
  | .lit v => .lit v
  | .inv x => .inv (x.bind input register)
  | .band x y => .band (x.bind input register) (y.bind input register)
  | .sub x y => .sub (x.bind input register) (y.bind input register)
  | .slice start len fits x => .slice start len fits (x.bind input register)
  | .equal x y => .equal (x.bind input register) (y.bind input register)
  | .ult x y => .ult (x.bind input register) (y.bind input register)
  | .zero x => .zero (x.bind input register)
  | .mux c t f => .mux (c.bind input register) (t.bind input register) (f.bind input register)

theorem Expr.eval_bind (input : {w : Nat} → I w → Expr J S w)
    (register : {w : Nat} → R w → Expr J S w) (e : Expr I R w)
    (inputs : Values J) (registers : Values S) :
    (e.bind input register).eval inputs registers =
      e.eval (fun i => (input i).eval inputs registers) (fun r => (register r).eval inputs registers) := by
  induction e <;> simp_all [Expr.bind, Expr.eval]

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
