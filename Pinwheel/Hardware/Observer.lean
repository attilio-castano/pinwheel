import Pinwheel.Hardware.NetlistExtend
import Pinwheel.Hardware.NetlistTools

/-! Stateful output adapters observe a core without changing its transition.
This is the output-side counterpart of `Feeder`. -/
namespace Pinwheel.Hardware

inductive Observed (I O : Nat → Type) : Nat → Type where
  | input : I w → Observed I O w
  | output : O w → Observed I O w

def Observed.values (i : Values I) (o : Values O) : Values (Observed I O)
  | _, .input p => i p
  | _, .output p => o p

structure Observer (I O X P : Nat → Type) where
  next : {w : Nat} → X w → Expr (Observed I O) X w
  output : {w : Nat} → P w → Expr (Observed I O) X w

namespace Observer

def belowWire (a : Observer I O X P) : Observer (WithWire I width) O X P where
  next := fun x => (a.next x).bind (fun p => match p with
    | .input i => .input (.input (.input i)) | .output o => .input (.output o)) (.reg)
  output := fun x => (a.output x).bind (fun p => match p with
    | .input i => .input (.input (.input i)) | .output o => .input (.output o)) (.reg)

def bind (c : Circuit I R O) (e : Expr (Observed I O) X w) : Expr I (Extended R X) w :=
  e.bind (fun p => match p with
    | .input i => .input i
    | .output o => (c.output o).inner (.input)) (fun x => .reg (.extra x))

def wrap : {I : Nat → Type} → Observer I O X P → Netlist R O I → Netlist (Extended R X) P I
  | _, a, .finish c => .finish {
      next := fun r => match r with
        | .inner r => (c.next r).inner (.input)
        | .extra x => bind c (a.next x)
      output := fun o => bind c (a.output o) }
  | _, a, .letWire e body => .letWire (e.inner (.input)) (wrap a.belowWire body)

theorem inner_step (a : Observer I O X P) (n : Netlist R O I) (i : Values I)
    (s : Values (Extended R X)) (r : R w) :
    (a.wrap n).step i s (.inner r) = n.step i (Extended.innerValues s) r := by
  induction n
  all_goals simp_all only [wrap, Netlist.step, Circuit.step, Expr.inner_correct, Expr.eval]
  all_goals done

theorem extra_step (a : Observer I O X P) (n : Netlist R O I) (i : Values I)
    (s : Values (Extended R X)) (x : X w) :
    (a.wrap n).step i s (.extra x) =
      (a.next x).eval (Observed.values i (n.observe i (Extended.innerValues s)))
        (Extended.extraValues s) := by
  induction n
  all_goals simp_all only [wrap, Netlist.step, Circuit.step, Netlist.observe,
    bind, Expr.eval_bind, Expr.inner_correct, Expr.eval, belowWire]
  all_goals congr 1
  all_goals funext w p
  all_goals cases p
  all_goals simp only [Expr.eval, Expr.inner_correct, Observed.values, WithWire.values, Circuit.observe]

theorem observe (a : Observer I O X P) (n : Netlist R O I) (i : Values I)
    (s : Values (Extended R X)) (o : P w) :
    (a.wrap n).observe i s o =
      (a.output o).eval (Observed.values i (n.observe i (Extended.innerValues s)))
        (Extended.extraValues s) := by
  induction n
  all_goals simp_all only [wrap, Netlist.observe, Circuit.observe,
    bind, Expr.eval_bind, Expr.inner_correct, Expr.eval, belowWire]
  all_goals congr 1
  all_goals funext w p
  all_goals cases p
  all_goals simp only [Expr.eval, Expr.inner_correct, Observed.values, WithWire.values, Circuit.observe]

end Observer
end Pinwheel.Hardware
