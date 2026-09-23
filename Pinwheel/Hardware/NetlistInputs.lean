import Pinwheel.Hardware.NetlistExtend
import Pinwheel.Hardware.NetlistTools

/-! A checked input substitution may simplify input-to-literal comparisons.
This preserves shared wires while allowing command admission to leave unrelated
command decoders on their original direct paths. -/
namespace Pinwheel.Hardware

structure InputMap (I J R : Nat → Type) where
  input : {w : Nat} → I w → Expr J R w
  literalEq : {w : Nat} → I w → BitVec w → Expr J R 1
  correct : ∀ {w : Nat} (p : I w) (v : BitVec w) (j : Values J) (r : Values R),
    (literalEq p v).eval j r = BitVec.ofBool (decide ((input p).eval j r = v))

namespace InputMap

def expression (m : InputMap I J R) : Expr I R w → Expr J R w
  | .input p => m.input p
  | .reg r => .reg r
  | .lit v => .lit v
  | .concat a b => .concat (m.expression a) (m.expression b)
  | .inv a => .inv (m.expression a)
  | .band a b => .band (m.expression a) (m.expression b)
  | .sub a b => .sub (m.expression a) (m.expression b)
  | .slice s n h a => .slice s n h (m.expression a)
  | .equal a b => match a, b with
    | .input p, .lit v => m.literalEq p v
    | a, b => .equal (m.expression a) (m.expression b)
  | .ult a b => .ult (m.expression a) (m.expression b)
  | .zero a => .zero (m.expression a)
  | .mux c a b => .mux (m.expression c) (m.expression a) (m.expression b)

theorem expression_correct (m : InputMap I J R) (e : Expr I R w) (j : Values J) (r : Values R) :
    (m.expression e).eval j r = e.eval (fun p => (m.input p).eval j r) r := by
  induction e <;> simp_all [expression, Expr.eval]
  case equal a b ha hb =>
    unfold expression
    split
    all_goals simp_all only [Expr.eval, m.correct]
    all_goals rfl

/-- The same substitution below a shared combinational wire. -/
def belowWire (m : InputMap I J R) : InputMap (WithWire I width) (WithWire J width) R where
  input := fun p => match p with
    | .input q => (m.input q).weaken
    | .wire => .input .wire
  literalEq := fun p v => match p with
    | .input q => (m.literalEq q v).weaken
    | .wire => .equal (.input .wire) (.lit v)
  correct := by
    intro w p v j r
    cases p
    all_goals simp only [Expr.weaken, Expr.eval_bind, Expr.eval, m.correct]
    all_goals rfl

/-- Interpret the replacement input leaves. -/
def values (m : InputMap I J R) (j : Values J) (r : Values R) : Values I :=
  fun p => (m.input p).eval j r

theorem belowWire_values (m : InputMap I J R) (j : Values J) (r : Values R) (v : BitVec width) :
    (m.belowWire.values (WithWire.values j v) r : Values (WithWire I width)) =
      (fun {_} p => WithWire.values (m.values j r) v p) := by
  funext w p
  cases p
  all_goals simp only [values, belowWire, Expr.weaken_correct, Expr.eval, WithWire.values]

/-- Substitute inputs through a netlist without expanding shared expressions. -/
def netlist : {I J : Nat → Type} → InputMap I J R → Netlist R O I → Netlist R O J
  | _, _, m, .finish c => .finish {
      next := fun r => m.expression (c.next r)
      output := fun o => m.expression (c.output o) }
  | _, _, m, .letWire e body => .letWire (m.expression e) (netlist m.belowWire body)

theorem netlist_step (m : InputMap I J R) (n : Netlist R O I) (j : Values J) (s : Values R) (r : R w) :
    (m.netlist n).step j s r = n.step (m.values j s) s r := by
  induction n generalizing J
  all_goals simp_all only [netlist, Netlist.step, Circuit.step, expression_correct, belowWire_values]
  all_goals rfl

theorem netlist_observe (m : InputMap I J R) (n : Netlist R O I) (j : Values J) (s : Values R)
    (o : O w) : (m.netlist n).observe j s o = n.observe (m.values j s) s o := by
  induction n generalizing J
  all_goals simp_all only [netlist, Netlist.observe, Circuit.observe, expression_correct, belowWire_values]
  all_goals rfl

end InputMap
end Pinwheel.Hardware
