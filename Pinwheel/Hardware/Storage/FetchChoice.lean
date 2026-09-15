import Pinwheel.Hardware.Storage.CacheContract
import Pinwheel.Hardware.Reactive.FetchChoice

namespace Pinwheel.Hardware.Storage.FetchChoice
open Loader

inductive Variant where
  | lateIndex | lateRecord
  deriving DecidableEq, Repr

def branch : Cache.E 1 :=
  Reactive.Fetch.branchExpr.bind Cache.baseInputs Cache.coreReg

def candidate (b : Bool) : Cache.E 8 :=
  (Reactive.Fetch.candidateExpr b).bind Cache.baseInputs Cache.coreReg

def readIndex (address : Cache.E 8) : Cache.E 6 :=
  Execution.readTree 8 (fun k => Cache.chosen (.index k)) address

def readDictionary (index : Cache.E 6) : Cache.E 64 :=
  Execution.readTree 6 (fun k => Cache.chosen (.word k)) index

def fetch : Variant → Cache.E 64
  | .lateIndex => readDictionary (Reactive.Fetch.selectionExpr branch candidate readIndex)
  | .lateRecord => Reactive.Fetch.selectionExpr branch candidate Cache.read

theorem branch_correct (i : Machine.Inputs) (s : Cache.State) :
    branch.eval i.values s.values =
      BitVec.ofBool (Reactive.Fetch.branchBit ⟨Cache.base i s, s.machine.core⟩) := by
  simp [branch, Expr.eval_bind, Cache.base_correct, Cache.coreReg, Cache.lift,
    Expr.eval, Cache.State.values, Machine.State.values, Reactive.Fetch.branchExpr_correct]
  done

theorem candidate_correct (i : Machine.Inputs) (s : Cache.State) (b : Bool) :
    (candidate b).eval i.values s.values =
      Reactive.Fetch.candidateAddress ⟨Cache.base i s, s.machine.core⟩ b := by
  simp [candidate, Expr.eval_bind, Cache.base_correct, Cache.coreReg, Cache.lift,
    Expr.eval, Cache.State.values, Machine.State.values, Reactive.Fetch.candidateExpr_correct]
  done

theorem readIndex_correct (i : Machine.Inputs) (s : Cache.State) (a : Cache.E 8) :
    (readIndex a).eval i.values s.values =
      s.machine.memory (Machine.selected i s.machine) (.index (a.eval i.values s.values)) := by
  simp [readIndex, Execution.readTree_correct, Cache.chosen, Cache.lift_correct, Machine.chosen_correct]
  done

theorem readDictionary_correct (i : Machine.Inputs) (s : Cache.State) (a : Cache.E 6) :
    (readDictionary a).eval i.values s.values =
      s.machine.memory (Machine.selected i s.machine) (.word (a.eval i.values s.values)) := by
  simp [readDictionary, Execution.readTree_correct, Cache.chosen, Cache.lift_correct, Machine.chosen_correct]
  done

theorem fetch_correct (v : Variant) (i : Machine.Inputs) (s : Cache.State) :
    (fetch v).eval i.values s.values = (Cache.read Cache.target).eval i.values s.values := by
  have hi := Reactive.Fetch.selectionExpr_correct ⟨Cache.base i s, s.machine.core⟩
    i.values s.values branch candidate readIndex
    (fun a => s.machine.memory (Machine.selected i s.machine) (.index a))
    (branch_correct i s) (candidate_correct i s) (readIndex_correct i s)
  have hw := Reactive.Fetch.selectionExpr_correct ⟨Cache.base i s, s.machine.core⟩
    i.values s.values branch candidate Cache.read
    (Store.read (s.machine.memory (Machine.selected i s.machine)))
    (branch_correct i s) (candidate_correct i s) (Cache.read_correct i s)
  cases v <;> simp [fetch, readDictionary_correct, hi, hw, Cache.read_correct,
    Cache.target_correct, Store.read, Reactive.Fetch.Request.address]
  done

def feedInputs (v : Variant) : {w : Nat} → Reactive.Input w → Cache.E w
  | _, .successor => fetch v
  | _, p => Cache.baseInputs p

def circuit (v : Variant) : Circuit Machine.Input Cache.Register Machine.Output where
  next := fun r => match r with
    | .machine (.core p) => (Reactive.circuit.next p).bind (feedInputs v) Cache.coreReg
    | .machine p => Cache.liftExpr (Machine.circuit.next p)
    | .current => .mux
      (Execution.bor (.inv (Cache.liftExpr (Reactive.running.bind (fun _ => .lit 0) Machine.coreReg)))
        (.inv (.equal ((Reactive.circuit.next .pc).bind (feedInputs v) Cache.coreReg) (Cache.coreReg .pc))))
      (fetch v) (.reg .current)
  output := fun o => match o with
    | .core p => (Reactive.circuit.output p).bind (feedInputs v) Cache.coreReg
    | .control p => Cache.liftExpr (Machine.circuit.output (.control p))

theorem feedInputs_correct (v : Variant) (i : Machine.Inputs) (s : Cache.State)
    (p : Reactive.Input w) :
    (feedInputs v p).eval i.values s.values = (Cache.feedInputs p).eval i.values s.values := by
  cases p <;> simp [feedInputs, Cache.feedInputs, fetch_correct]
  done

theorem step_same (v : Variant) (i : Machine.Inputs) (s : Cache.State) (r : Cache.Register w) :
    (circuit v).step i.values s.values r = Cache.circuit.step i.values s.values r := by
  cases r
  case current =>
    simp [Circuit.step, circuit, Cache.circuit, Execution.bor, Expr.eval, Expr.eval_bind, feedInputs_correct, fetch_correct]
  case machine p =>
    cases p <;> simp [Circuit.step, circuit, Cache.circuit, Expr.eval_bind, feedInputs_correct]
  done

theorem observe_same (v : Variant) (i : Machine.Inputs) (s : Cache.State) (o : Machine.Output w) :
    (circuit v).observe i.values s.values o = Cache.circuit.observe i.values s.values o := by
  cases o <;> simp [Circuit.observe, circuit, Cache.circuit, Expr.eval_bind, feedInputs_correct]
  done

def component (v : Variant) : Timed.Component Machine.Inputs (Values Cache.Register) (Values Machine.Output) :=
  ⟨fun i s => (circuit v).step i.values s, fun i s => (circuit v).observe i.values s⟩

def refinement (v : Variant) : Timed.Refinement (component v) Cache.component where
  Rel := fun r s => @r = @Cache.State.values s
  step := fun i r s h => by
    simpa only [component, Cache.component, h] using
      funext fun w => funext fun p : Cache.Register w =>
        (step_same v i s p).trans (Cache.next_correct i s p)
  observe := fun i r s h => by
    simpa only [component, Cache.component, h] using
      funext fun w => funext fun o : Machine.Output w => observe_same v i s o

def completeRefinement (v : Variant) : Timed.Refinement (component v) Cache.referenceComponent :=
  (refinement v).trans Cache.refinement

theorem trace_correct (v : Variant) (s : Cache.State) (h : Cache.Valid s)
    (inputs : List Machine.Inputs) :
    (component v).trace s.values inputs = Cache.referenceComponent.trace s.machine inputs :=
  (completeRefinement v).trace_eq s.values s.machine ⟨s, rfl, h, rfl⟩ inputs

end Pinwheel.Hardware.Storage.FetchChoice
