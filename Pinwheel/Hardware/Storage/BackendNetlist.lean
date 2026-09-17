import Pinwheel.Hardware.Storage.Backend
import Pinwheel.Hardware.Netlist

namespace Pinwheel.Hardware.Storage.Backend
open Loader

def fresh (e : Expr I R w) : Expr (WithWire I width) R w :=
  e.bind (fun p => .input (.input p)) (fun r => .reg r)

theorem fresh_correct (e : Expr I R w) (i : Values I) (s : Values R) (v : BitVec width) :
    (fresh e).eval (WithWire.values i v) s = e.eval i s := by
  simp only [fresh, Expr.eval_bind, Expr.eval, WithWire.values]
  done

abbrev SuccessorInput := WithWire Machine.Input 64
abbrev FinalInput := WithWire SuccessorInput 8

def successor : E 64 := lift (Cache.read Cache.target)

def feed : {w : Nat} → Reactive.Input w → Expr SuccessorInput Register w
  | _, .successor => .input .wire
  | _, p => fresh (lift (Cache.baseInputs p))

def coreRegS : {w : Nat} → Reactive.Register w → Expr SuccessorInput Register w :=
  fun r => .reg (.core r)

def nextPC : Expr SuccessorInput Register 8 := (Reactive.circuit.next .pc).bind feed coreRegS

def feedFinal (p : Reactive.Input w) : Expr FinalInput Register w := fresh (feed p)
def coreRegF : {w : Nat} → Reactive.Register w → Expr FinalInput Register w := fun r => .reg (.core r)

def body : Circuit FinalInput Register Machine.Output where
  next := fun r => match r with
    | .core r => (Reactive.circuit.next r).bind feedFinal coreRegF
    | .current => .mux
      (Execution.bor (.inv (fresh (fresh (lift (Cache.liftExpr
        (Reactive.running.bind (fun _ => .lit 0) Machine.coreReg))))))
        (.inv (.equal (.input .wire) (.reg (.core .pc)))))
      (.input (.input .wire)) (.reg .current)
    | r => fresh (fresh (circuit.next r))
  output := fun o => match o with
    | .core o => (Reactive.circuit.output o).bind feedFinal coreRegF
    | .control o => fresh (fresh (circuit.output (.control o)))

/-- The same successor fetch and next-PC combinational values are shared by
all consumers. These bindings introduce no state or additional clock edges. -/
def netlist : Netlist Register Machine.Output Machine.Input :=
  .letWire successor (.letWire nextPC (.finish body))

def successorValues (i : Machine.Inputs) (s : State) : Values SuccessorInput :=
  WithWire.values i.values (successor.eval i.values s.values)

def finalValues (i : Machine.Inputs) (s : State) : Values FinalInput :=
  WithWire.values (successorValues i s) (nextPC.eval (successorValues i s) s.values)

theorem feed_correct (i : Machine.Inputs) (s : State) (p : Reactive.Input w) :
    (feed p).eval (successorValues i s) s.values = (Cache.feed (adapt i s) s.reference).values p := by
  cases p <;> simp [feed, successorValues, fresh_correct, lift_correct, Cache.base_correct,
    successor, Expr.eval, WithWire.values, Cache.read_correct, Cache.target_correct,
    Cache.feed, Reactive.Inputs.values]
  done

theorem successor_correct (i : Machine.Inputs) (s : State) :
    successor.eval i.values s.values = (Cache.feed (adapt i s) s.reference).successor :=
  feed_correct i s .successor

theorem pc_correct (i : Machine.Inputs) (s : State) :
    nextPC.eval (successorValues i s) s.values =
      (Cache.next (adapt i s) s.reference).machine.core.pc := by
  simp only [nextPC, Expr.eval_bind, feed_correct, coreRegS, Expr.eval, State.values,
    Reactive.next_correct, Cache.next]
  rfl
  done

theorem feedFinal_correct (i : Machine.Inputs) (s : State) (p : Reactive.Input w) :
    (feedFinal p).eval (finalValues i s) s.values = (Cache.feed (adapt i s) s.reference).values p := by
  simp only [feedFinal, finalValues, fresh_correct, feed_correct]
  done

theorem netlist_next (i : Machine.Inputs) (s : State) (r : Register w) :
    netlist.step i.values s.values r = (next i s).values r := by
  cases r
  all_goals simp only [netlist, Netlist.step, Circuit.step, body, fresh_correct]
  all_goals first | exact next_correct i s _ | skip
  case core p =>
    change ((Reactive.circuit.next p).bind feedFinal coreRegF).eval (finalValues i s) s.values = _
    simp only [Expr.eval_bind, feedFinal_correct, coreRegF, Expr.eval, State.values,
      Reactive.next_correct, next, Cache.next]
    rfl
  case current =>
    change (body.next .current).eval (finalValues i s) s.values = _
    simp only [body, Execution.bor, Expr.eval, finalValues, fresh_correct, WithWire.values,
      pc_correct, State.values, next]
    simp only [successorValues, fresh_correct, lift_correct, Cache.lift_correct,
      WithWire.values, successor_correct]
    simp [Expr.eval_bind, Machine.coreReg, Expr.eval, Machine.State.values,
      Reactive.running, Reactive.State.values, Reactive.runningValue, Cache.next,
      State.reference, State.small, Small.State.reference]
  done

theorem netlist_output (i : Machine.Inputs) (s : State) (o : Machine.Output w) :
    netlist.observe i.values s.values o = circuit.observe i.values s.values o := by
  cases o
  all_goals simp only [netlist, Netlist.observe, body, Circuit.observe, fresh_correct]
  rename_i p
  change ((Reactive.circuit.output p).bind feedFinal coreRegF).eval (finalValues i s) s.values = _
  simp only [Expr.eval_bind, feedFinal_correct, coreRegF, Expr.eval, State.values,
    circuit, lift_correct, Cache.circuit, Expr.eval_bind, Cache.feed_correct_circuit,
    Cache.coreReg, Cache.lift, Cache.State.values, Machine.State.values]
  rfl
  done

def netlistComponent : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  ⟨fun i r => netlist.step i.values r, fun i r => netlist.observe i.values r⟩

def netlistRefinement : Timed.Refinement netlistComponent component where
  Rel := fun r s => @r = @s.values
  step := fun i r s h => by
    subst r
    exact funext fun w => funext fun p => netlist_next i s p
  observe := fun i r s h => by
    subst r
    exact funext fun w => funext fun p => netlist_output i s p

def netlistCompleteRefinement : Timed.Refinement netlistComponent referenceComponent :=
  netlistRefinement.trans refinement

theorem netlist_trace (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    netlistComponent.trace s.values inputs = referenceComponent.trace s.reference.machine inputs :=
  netlistCompleteRefinement.trace_eq s.values s.reference.machine ⟨s, rfl, h, rfl⟩ inputs

theorem netlist_initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    netlistComponent.trace (netlist.step i.values s.values) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs := by
  have hn : (netlist.step i.values s.values : Values Register) = (fun {_} r => (next i s).values r) :=
    funext fun w => funext fun r => netlist_next i s r
  rw [hn, ← initialize_machine_next i s hi]
  exact netlist_trace (next i s) (initialize_valid i s hi) inputs
  done

end Pinwheel.Hardware.Storage.Backend
