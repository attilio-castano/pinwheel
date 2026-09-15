import Pinwheel.Hardware.Storage.CacheProofs

namespace Pinwheel.Hardware.Storage.Cache
open Loader

inductive Register : Nat → Type where
  | machine : Machine.Register w → Register w
  | current : Register 64

def State.values (s : State) : Values Register
  | _, .machine r => s.machine.values r | _, .current => s.current

abbrev E := Expr Machine.Input Register

def lift : {w : Nat} → Machine.Register w → E w := fun r => .reg (.machine r)
def liftExpr (e : Machine.E w) : E w := e.bind (fun p => .input p) lift

def baseInputs : {w : Nat} → Reactive.Input w → E w
  | _, .current => .reg .current | _, p => liftExpr (Machine.baseInputs p)

def coreReg : {w : Nat} → Reactive.Register w → E w := fun r => lift (.core r)
def chosen (r : Loader.Store.Register w) : E w := liftExpr (Machine.chosen r)
def read (address : E 8) : E 64 :=
  Execution.readTree 6 (fun k => chosen (.word k))
    (Execution.readTree 8 (fun k => chosen (.index k)) address)
def target : E 8 := Reactive.target.bind baseInputs coreReg
def feedInputs : {w : Nat} → Reactive.Input w → E w
  | _, .successor => read target | _, p => baseInputs p

def circuit : Circuit Machine.Input Register Machine.Output where
  next := fun r => match r with
    | .machine (.core p) => (Reactive.circuit.next p).bind feedInputs coreReg
    | .machine p => liftExpr (Machine.circuit.next p)
    | .current => .mux
      (Execution.bor (.inv (liftExpr (Reactive.running.bind (fun _ => .lit 0) Machine.coreReg)))
        (.inv (.equal ((Reactive.circuit.next .pc).bind feedInputs coreReg) (coreReg .pc))))
      (read target) (.reg .current)
  output := fun o => match o with
    | .core p => (Reactive.circuit.output p).bind feedInputs coreReg
    | .control p => liftExpr (Machine.circuit.output (.control p))

theorem lift_correct (i : Machine.Inputs) (s : State) (e : Machine.E w) :
    (liftExpr e).eval i.values s.values = e.eval i.values s.machine.values := by
  simp [liftExpr, Expr.eval_bind, Expr.eval, lift, State.values]
  done

theorem base_correct (i : Machine.Inputs) (s : State) (p : Reactive.Input w) :
    (baseInputs p).eval i.values s.values = (base i s).values p := by
  cases p <;> simp [baseInputs, lift_correct, Machine.base_correct, base, Reactive.Inputs.values,
    Expr.eval, State.values]
  done

theorem read_correct (i : Machine.Inputs) (s : State) (a : E 8) :
    (read a).eval i.values s.values = Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
      (a.eval i.values s.values) := by
  simp [read, Execution.readTree_correct, chosen, lift_correct, Machine.chosen_correct, Loader.Store.read]
  done

theorem target_correct (i : Machine.Inputs) (s : State) :
    target.eval i.values s.values = Reactive.targetValue (base i s) s.machine.core := by
  simp only [target, Expr.eval_bind, base_correct, coreReg, lift, Expr.eval, State.values,
    Machine.State.values, Reactive.target_correct]
  done

theorem feed_correct_circuit (i : Machine.Inputs) (s : State) (p : Reactive.Input w) :
    (feedInputs p).eval i.values s.values = (feed i s).values p := by
  cases p <;> simp [feedInputs, base_correct, read_correct, target_correct, feed, Reactive.Inputs.values]
  done

set_option backward.isDefEq.respectTransparency false in
theorem next_correct (i : Machine.Inputs) (s : State) (r : Register w) :
    circuit.step i.values s.values r = (next i s).values r := by
  cases r with
  | machine r =>
    cases r <;> simp only [Circuit.step, circuit, lift_correct, Expr.eval_bind, feed_correct_circuit,
      coreReg, lift, Expr.eval, State.values, Machine.State.values, next,
      Reactive.next_correct]
    all_goals exact Machine.next_correct i s.machine _
  | current =>
    simp only [Circuit.step, circuit, Execution.bor, Expr.eval, lift_correct, Expr.eval_bind,
      feed_correct_circuit, coreReg, lift, State.values, Machine.State.values, Reactive.next_correct, read_correct, target_correct]
    simp [Machine.coreReg, Expr.eval, Machine.State.values, Reactive.running, Reactive.runningValue,
      Reactive.State.values, next, feed]
  done

end Pinwheel.Hardware.Storage.Cache
