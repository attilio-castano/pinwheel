import Pinwheel.Hardware.Loader.Machine

namespace Pinwheel.Hardware.Loader.Machine

theorem control_correct (i : Inputs) (s : State) (p : Loader.Input w) :
    (controlInputs p).eval i.values s.values = (controlInput i s).values p := by
  cases p <;> simp only [controlInputs, Expr.eval_bind, coreReg, Expr.eval, State.values,
    Inputs.values, controlInput, Loader.Inputs.values]
  exact Reactive.running_correct ⟨false, false, 0, {}, 0, 0, 0⟩ s.core
  done

theorem commit_correct (i : Inputs) (s : State) :
    commitGate.eval i.values s.values = BitVec.ofBool (committing i s) := by
  simp only [commitGate, Expr.eval_bind, control_correct, controlReg, Expr.eval, State.values,
    Loader.commit_correct, committing]
  done

theorem selected_correct (i : Inputs) (s : State) :
    selectedGate.eval i.values s.values = BitVec.ofBool (selected i s) := by
  simp [selectedGate, Expr.eval, commit_correct, controlReg, State.values, Loader.State.values, selected]
  split <;> rfl
  done

theorem chosen_correct (i : Inputs) (s : State) (r : Store.Register w) :
    (chosen r).eval i.values s.values = s.memory (selected i s) r := by
  cases h : selected i s <;> simp [chosen, Expr.eval, selected_correct, memoryReg, State.values, h]
  done

theorem read_correct (i : Inputs) (s : State) (a : E 8) :
    (readExpr a).eval i.values s.values = Store.read (s.memory (selected i s)) (a.eval i.values s.values) := by
  simp [readExpr, Execution.readTree_correct, chosen_correct, Store.read]
  done

theorem usable_correct (i : Inputs) (s : State) :
    usableGate.eval i.values s.values = BitVec.ofBool (usable i s) := by
  simp [usableGate, Execution.bor, Expr.eval, commit_correct, controlReg, State.values,
    Loader.State.values, Inputs.values, usable]
  done

theorem base_correct (i : Inputs) (s : State) (p : Reactive.Input w) :
    (baseInputs p).eval i.values s.values = (baseInput i s).values p := by
  cases p <;> simp [baseInputs, Execution.bor, Expr.eval_bind, Expr.eval, control_correct,
    controlReg, coreReg, State.values, Loader.start_correct, commit_correct,
    chosen_correct, read_correct, usable_correct, Inputs.values, Reactive.Inputs.values, baseInput,
    Bool.or_assoc]
  all_goals try simp [Loader.State.values]
  all_goals repeat' (first | rfl | (split <;> try simp_all))
  done

theorem scheduler_correct (i : Inputs) (s : State) (p : Reactive.Input w) :
    (schedulerInputs p).eval i.values s.values = (schedulerInput i s).values p := by
  cases p <;> simp only [schedulerInputs, base_correct, schedulerInput, Reactive.Inputs.values]
  simp only [read_correct, addressB, Expr.eval_bind, base_correct, coreReg, Expr.eval,
    State.values, Reactive.target_correct]
  done

theorem memory_correct (i : Inputs) (s : State) (b : Bool) (p : Store.Input w) :
    (memoryInputs b p).eval i.values s.values = (memoryInput i s b).values p := by
  cases p <;> simp [memoryInputs, pushGate, Expr.eval_bind, control_correct, controlReg,
    Expr.eval, State.values, Loader.push_correct, Inputs.values, Store.Inputs.values, memoryInput]
  all_goals cases b <;> cases h : s.control.active <;> simp [Loader.State.values, h]
  done

/-- Every controller, execution and memory register matches the functional machine. -/
theorem next_correct (i : Inputs) (s : State) (r : Register w) :
    circuit.step i.values s.values r = (next i s).values r := by
  cases r <;> simp only [Circuit.step, circuit, Expr.eval_bind, control_correct, scheduler_correct,
    memory_correct, controlReg, coreReg, memoryReg, Expr.eval, State.values, next,
    Loader.next_correct, Reactive.next_correct, Store.next_correct]
  done

def run (s : State) : List Inputs → State
  | [] => s | i :: rest => run (next i s) rest

def circuitRun (v : Values Register) : List Inputs → Values Register
  | [] => v | i :: rest => circuitRun (circuit.step i.values v) rest

theorem run_correct (s : State) (requests : List Inputs) :
    (circuitRun s.values requests : Values Register) = (fun {_} r => (run s requests).values r) := by
  induction requests generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have h : (circuit.step i.values s.values : Values Register) = (fun {_} r => (next i s).values r) :=
      funext fun _ => funext fun r => next_correct i s r
    simpa only [circuitRun, h, run] using ih (next i s)
  done

end Pinwheel.Hardware.Loader.Machine
