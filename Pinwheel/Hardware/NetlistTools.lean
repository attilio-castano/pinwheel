import Pinwheel.Hardware.Netlist
import Pinwheel.Hardware.TimedPairs

/-! Timed observations and output maps for any structural netlist. -/
namespace Pinwheel.Hardware

/-- A netlist as a timed component over raw valuations. -/
def Netlist.component (n : Netlist R O I) : Timed.Component (Values I) (Values R) (Values O) :=
  ⟨fun i r => n.step i r, fun i r => n.observe i r⟩

/-- A netlist as a timed component over input records. -/
def Netlist.componentOf {P : Type} (values : P → Values I) (n : Netlist R O I) :
    Timed.Component P (Values R) (Values O) :=
  ⟨fun i r => n.step (values i) r, fun i r => n.observe (values i) r⟩

/-- Expose a netlist's expressions at its outer interface. The emitter's
operation cache restores shared expressions; this adds no state or edges. -/
def Netlist.toCircuit : {I : Nat → Type} → Netlist R O I → Circuit I R O
  | _, .finish c => c
  | _, .letWire e body =>
    let input : {w : Nat} → WithWire _ _ w → Expr _ R w := fun p => match p with
      | .input p => .input p | .wire => e
    { next := fun r => (body.toCircuit.next r).bind input (.reg)
      output := fun o => (body.toCircuit.output o).bind input (.reg) }

theorem Netlist.toCircuit_step (n : Netlist R O I) (i : Values I) (s : Values R) (r : R w) :
    n.toCircuit.step i s r = n.step i s r := by
  induction n with
  | finish c => rfl
  | letWire e body ih =>
    simp only [toCircuit, Circuit.step, Expr.eval_bind, Expr.eval, Netlist.step]
    rw [← ih]
    congr 1
    funext w p
    cases p <;> rfl
    done

theorem Netlist.toCircuit_observe (n : Netlist R O I) (i : Values I) (s : Values R) (o : O w) :
    n.toCircuit.observe i s o = n.observe i s o := by
  induction n
  all_goals simp_all only [toCircuit, Circuit.observe, Expr.eval_bind, Expr.eval, Netlist.observe]
  all_goals congr 1
  all_goals funext w p
  all_goals cases p <;> rfl
  all_goals done

/-! ### Output maps -/

/-- No registers. -/
inductive NoRegister : Nat → Type

/-- The only valuation of no registers. -/
def NoRegister.values : Values NoRegister := fun r => nomatch r

/-- New outputs as expressions over a netlist's outputs. -/
def Netlist.mapOutputs {O' : Nat → Type} : {I : Nat → Type} → Netlist R O I →
    ({w : Nat} → O' w → Expr O NoRegister w) → Netlist R O' I
  | _, .finish c, out => .finish
      { next := c.next
        output := fun o => (out o).bind (fun q => c.output q) (fun r => nomatch r) }
  | _, .letWire e body, out => .letWire e (body.mapOutputs out)

theorem Netlist.mapOutputs_step {O' : Nat → Type} (n : Netlist R O I)
    (out : {w : Nat} → O' w → Expr O NoRegister w)
    (i : Values I) (s : Values R) (r : R w) : (n.mapOutputs out).step i s r = n.step i s r := by
  induction n with
  | finish c => rfl
  | letWire e body ih => exact ih _

/-- A mapped output is its expression evaluated on the netlist's observations. -/
theorem Netlist.mapOutputs_observe {O' : Nat → Type} (n : Netlist R O I)
    (out : {w : Nat} → O' w → Expr O NoRegister w) (i : Values I) (s : Values R) (o : O' w) :
    (n.mapOutputs out).observe i s o = (out o).eval (n.observe i s) (fun r => nomatch r) := by
  induction n with
  | finish c =>
    simp only [Netlist.mapOutputs, Netlist.observe, Circuit.observe, Expr.eval_bind]
    congr 1
    funext w r
    exact nomatch r
  | letWire e body ih => exact ih _

end Pinwheel.Hardware
