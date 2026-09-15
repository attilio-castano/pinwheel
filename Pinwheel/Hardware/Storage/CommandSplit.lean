import Pinwheel.Hardware.Storage.Small
import Pinwheel.Hardware.Timed

namespace Pinwheel.Hardware.Storage.CommandSplit
open Loader.Machine

/-- Only the push command can be changed by small-store validation. -/
def checked (command : BitVec 3) (capacity : BitVec 1) : BitVec 3 :=
  if command == 2 && capacity == 0 then 6 else command

def adapted (i : Values Input) (capacity : BitVec 1) : Values Input
  | _, .command => checked (i .command) capacity
  | _, p => i p

/-- Bind capacity rejection at the command leaves, but decode unaffected command
predicates directly. This changes no state, cycle boundary, or storage format. -/
def expression (capacity : Expr Input R 1) : Expr Input R w → Expr Input R w
  | .input .command => .mux (.band (.equal (.input .command) (.lit 2)) (.zero capacity)) (.lit 6) (.input .command)
  | .input p => .input p
  | .reg r => .reg r
  | .lit v => .lit v
  | .concat x y => .concat (expression capacity x) (expression capacity y)
  | .inv x => .inv (expression capacity x)
  | .band x y => .band (expression capacity x) (expression capacity y)
  | .sub x y => .sub (expression capacity x) (expression capacity y)
  | .slice start len fits x => .slice start len fits (expression capacity x)
  | .equal x y => match x, y with
    | .input .command, .lit n =>
      if n != 2 && n != 6 then .equal (.input .command) (.lit n)
      else .equal (expression capacity (.input .command)) (.lit n)
    | x, y => .equal (expression capacity x) (expression capacity y)
  | .ult x y => .ult (expression capacity x) (expression capacity y)
  | .zero x => .zero (expression capacity x)
  | .mux c t f => .mux (expression capacity c) (expression capacity t) (expression capacity f)

set_option backward.isDefEq.respectTransparency false in
theorem expression_correct (capacity : Expr Input R 1) (e : Expr Input R w)
    (i : Values Input) (r : Values R) :
    (expression capacity e).eval i r = e.eval (adapted i (capacity.eval i r)) r := by
  induction e <;> simp_all [expression, Expr.eval, adapted, checked]
  case equal x y hx hy =>
    unfold expression
    split <;> simp_all [Expr.eval, adapted, checked]
    split <;> simp_all [Expr.eval]
    split <;> simp_all [Ne.symm]
    done
  case input p =>
    cases p <;> simp [expression, Expr.eval]
    done
  done

/-- The same capacity predicate, expressed against the logical machine registers. -/
def capacity : Loader.Machine.E 1 := Small.capacityGate.bind (fun p => .input p)
  (fun r => match r with | .control r => .reg (.control r) | _ => .lit 0)

theorem capacity_correct (i : Inputs) (s : Small.State) :
    capacity.eval i.values s.reference.values = BitVec.ofBool (Small.capacity s.control.cursor i.data) := by
  exact Small.capacity_correct i s
  done

set_option backward.isDefEq.respectTransparency false in
theorem adapted_small (i : Inputs) (s : Small.State) (p : Input w) :
    adapted i.values (capacity.eval i.values s.reference.values) p = (Small.adapt i s).values p := by
  cases hc : Small.capacity s.control.cursor i.data <;>
    cases p <;> simp [adapted, capacity_correct, checked, Small.adapt, Inputs.values, hc]
  done

/-- Commit/bank selection and start decode have no capacity/data cone. -/
theorem commit_structure : expression capacity Loader.Machine.commitGate = Loader.Machine.commitGate := by
  rfl
  done

theorem start_structure : expression capacity
    (Loader.startGate.bind controlInputs controlReg) = Loader.startGate.bind controlInputs controlReg := by
  rfl
  done

def circuit (c : Circuit Input R O) (cap : Expr Input R 1) : Circuit Input R O where
  next := fun r => expression cap (c.next r)
  output := fun o => expression cap (c.output o)

def component (c : Circuit Input R O) (cap : Expr Input R 1) :
    Timed.Component (Values Input) (Values R) (Values O) :=
  ⟨(circuit c cap).step, (circuit c cap).observe⟩

/-- Reference wiring applies the capacity adapter to all command uses. -/
def reference (c : Circuit Input R O) (cap : Expr Input R 1) :
    Timed.Component (Values Input) (Values R) (Values O) :=
  ⟨fun i r => c.step (adapted i (cap.eval i r)) r,
    fun i r => c.observe (adapted i (cap.eval i r)) r⟩

theorem component_same (c : Circuit Input R O) (cap : Expr Input R 1) :
    component c cap = reference c cap := by
  simp only [component, reference, Timed.Component.mk.injEq]
  constructor <;> funext i r w p
  all_goals exact expression_correct cap _ i r
  done

/-- Whole-circuit pre/post-edge observations agree for every initial register
valuation and input sequence, including invalid uploads and busy commands. -/
theorem trace_correct (c : Circuit Input R O) (cap : Expr Input R 1)
    (s : Values R) (requests : List (Values Input)) :
    (component c cap).trace s requests = (reference c cap).trace s requests := by
  rw [component_same]
  done

end Pinwheel.Hardware.Storage.CommandSplit
