import Pinwheel.Hardware.Netlist

/-! Wrap a proved netlist with additional state that feeds its inputs.
The inner netlist's expressions are reused unchanged; only their input and
register leaves are rewired. -/
namespace Pinwheel.Hardware

/-- Registers of a wrapped design: every inner register plus wrapper-owned state. -/
inductive Extended (R X : Nat → Type) : Nat → Type where
  | inner : R w → Extended R X w
  | extra : X w → Extended R X w

def Extended.values (s : Values R) (x : Values X) : Values (Extended R X)
  | _, .inner r => s r
  | _, .extra e => x e

def Extended.innerValues (s : Values (Extended R X)) : Values R := fun r => s (.inner r)
def Extended.extraValues (s : Values (Extended R X)) : Values X := fun x => s (.extra x)

/-- An expression remains valid below one more combinational wire. -/
def Expr.weaken (e : Expr I R w) : Expr (WithWire I width) R w :=
  e.bind (fun p => .input (.input p)) (fun r => .reg r)

theorem Expr.weaken_correct (e : Expr I R w) (i : Values I) (s : Values R) (v : BitVec width) :
    (e.weaken (width := width)).eval (WithWire.values i v) s = e.eval i s := by
  simp only [Expr.weaken, Expr.eval_bind, Expr.eval, WithWire.values]
  done

def Expr.inner (input : {w : Nat} → I w → Expr J (Extended R X) w) (e : Expr I R w) :
    Expr J (Extended R X) w :=
  e.bind input (fun r => .reg (.inner r))

theorem Expr.inner_correct (input : {w : Nat} → I w → Expr J (Extended R X) w) (e : Expr I R w)
    (j : Values J) (s : Values (Extended R X)) :
    (e.inner input).eval j s = e.eval (fun p => (input p).eval j s) (Extended.innerValues s) := by
  simp only [Expr.inner, Expr.eval_bind, Expr.eval]
  rfl

def belowWire (input : {w : Nat} → I w → Expr J S w) :
    {w : Nat} → WithWire I width w → Expr (WithWire J width) S w
  | _, .input p => (input p).weaken
  | _, .wire => .input .wire

theorem belowWire_correct (input : {w : Nat} → I w → Expr J S w)
    (j : Values J) (s : Values S) (v : BitVec width) :
    (fun {w} (p : WithWire I width w) => (belowWire input p).eval (WithWire.values j v) s) =
      (WithWire.values (fun {w} (p : I w) => (input p).eval j s) v : Values (WithWire I width)) := by
  funext w p
  cases p <;> simp only [belowWire, Expr.weaken_correct, Expr.eval, WithWire.values]
  done

/-- Every inner input becomes an expression over outer inputs and extended state;
wrapper registers receive their own next-state expressions. Shared wires keep
their order, and only `finish` updates state. -/
def Netlist.extend : {I J : Nat → Type} → Netlist R O I →
    ({w : Nat} → I w → Expr J (Extended R X) w) →
    ({w : Nat} → X w → Expr J (Extended R X) w) → Netlist (Extended R X) O J
  | _, _, .finish c, input, extra => .finish {
      next := fun r => match r with
        | .inner r => (c.next r).inner input
        | .extra x => extra x
      output := fun o => (c.output o).inner input }
  | _, _, .letWire e body, input, extra =>
      .letWire (e.inner input) (body.extend (belowWire input) (fun x => (extra x).weaken))

theorem Netlist.extend_inner (n : Netlist R O I)
    (input : {w : Nat} → I w → Expr J (Extended R X) w)
    (extra : {w : Nat} → X w → Expr J (Extended R X) w)
    (j : Values J) (s : Values (Extended R X)) (r : R w) :
    (n.extend input extra).step j s (.inner r) =
      n.step (fun p => (input p).eval j s) (Extended.innerValues s) r := by
  induction n generalizing J with
  | finish c => simp only [Netlist.extend, Netlist.step, Circuit.step, Expr.inner_correct]
  | letWire e body ih =>
    simp only [Netlist.extend, Netlist.step, ih, belowWire_correct, Expr.inner_correct]
  done

theorem Netlist.extend_extra (n : Netlist R O I)
    (input : {w : Nat} → I w → Expr J (Extended R X) w)
    (extra : {w : Nat} → X w → Expr J (Extended R X) w)
    (j : Values J) (s : Values (Extended R X)) (x : X w) :
    (n.extend input extra).step j s (.extra x) = (extra x).eval j s := by
  induction n generalizing J with
  | finish c => simp only [Netlist.extend, Netlist.step, Circuit.step]
  | letWire e body ih =>
    simp only [Netlist.extend, Netlist.step, ih, Expr.weaken_correct]
  done

theorem Netlist.extend_observe (n : Netlist R O I)
    (input : {w : Nat} → I w → Expr J (Extended R X) w)
    (extra : {w : Nat} → X w → Expr J (Extended R X) w)
    (j : Values J) (s : Values (Extended R X)) (o : O w) :
    (n.extend input extra).observe j s o =
      n.observe (fun p => (input p).eval j s) (Extended.innerValues s) o := by
  induction n generalizing J with
  | finish c => simp only [Netlist.extend, Netlist.observe, Circuit.observe, Expr.inner_correct]
  | letWire e body ih =>
    simp only [Netlist.extend, Netlist.observe, ih, belowWire_correct, Expr.inner_correct]
  done

end Pinwheel.Hardware
