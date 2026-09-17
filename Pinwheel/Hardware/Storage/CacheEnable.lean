import Pinwheel.Hardware.Storage.BankSelectReadback

namespace Pinwheel.Hardware.Storage.Backend.CacheEnable
open Loader

/-- Compare at the leaves of a choice instead of after a wide output mux. -/
def different (left right : Expr I R w) : Expr I R 1 :=
  match left with
  | .mux c t f => .mux c (different t right) (different f right)
  | e => .inv (.equal e right)

theorem different_correct (left right : Expr I R w) (i : Values I) (s : Values R) :
    (different left right).eval i s = (.inv (.equal left right) : Expr I R 1).eval i s := by
  induction left <;> simp_all [different, Expr.eval]
  split <;> simp_all
  done

/-- Idle always refreshes. In the running case, compare each possible PC result
directly; halt, fault and reset still compare zero against the current PC. -/
def decision : Reactive.E 1 :=
  .mux Reactive.running
    (.mux (.input .reset) (.inv (.zero (.reg .pc)))
      (different (Reactive.advance .pc) (.reg .pc))) (.lit 1)

theorem decision_correct (i : Values Reactive.Input) (s : Values Reactive.Register) :
    decision.eval i s =
      (Execution.bor (.inv Reactive.running)
        (.inv (.equal (Reactive.circuit.next .pc) (.reg .pc)))).eval i s := by
  simp only [decision, Reactive.circuit, different_correct, Expr.eval, Reactive.stop, Reactive.hold,
    Execution.bor]
  rcases BitVec.eq_zero_or_eq_one (Reactive.running.eval i s) with h | h <;> simp [h]
  simp only [show (1#1) = BitVec.allOnes 1 from rfl, BitVec.allOnes_and]
  split <;> simp only [BitVec.not_ofBool]
  all_goals first | rfl | simp only [eq_comm]
  rfl
  done

def busyFeed (p : Reactive.Input w) : Expr SuccessorInput Register w :=
  match p with
  | .reset => Execution.bor (.input (.input .init))
      (Execution.bor (.input (.input .reset)) (.inv (.reg (.control .valid))))
  | .start => .lit 0
  | .last => .mux (.reg (.control .active)) (.reg (.last true)) (.reg (.last false))
  | p => BankSelect.feed p

def running : E 1 := Reactive.running.bind (fun _ => .lit 0) (fun r => .reg (.core r))

theorem busy_feed_eq (i : Values Machine.Input) (s : Values Register) (c : BitVec 64)
    (h : running.eval i s = 1) (p : Reactive.Input w) :
    (busyFeed p).eval (WithWire.values i c) s = (BankSelect.feed p).eval (WithWire.values i c) s := by
  cases p <;> simp only [busyFeed, BankSelect.feed, fresh_correct]
  all_goals simp [Cache.baseInputs, Cache.liftExpr, Cache.lift, Machine.baseInputs, BankSelect.lift,
    Expr.bind, CommandSplit.expression, logical, Small.logical, smallReg, Reactive.running,
    Machine.controlInputs, Machine.coreReg, Machine.controlReg, Machine.commitGate,
    Loader.commitGate, Loader.startGate, Loader.gate, Loader.command, Machine.chosen,
    Machine.selectedGate, Machine.memoryReg, Expr.eval, Execution.bor, WithWire.values, running] at h ⊢
  all_goals simp [h.1, h.2]
  all_goals bv_decide
  done

def enable : Expr SuccessorInput Register 1 := decision.bind busyFeed coreRegS

theorem enable_correct (i : Values Machine.Input) (s : Values Register) (c : BitVec 64) :
    enable.eval (WithWire.values i c) s =
      (Execution.bor (.inv (fresh running))
        (.inv (.equal BankSelect.nextPC (.reg (.core .pc))))).eval (WithWire.values i c) s := by
  by_cases h : running.eval i s = 1
  · simp only [enable, Expr.eval_bind, busy_feed_eq i s c h, decision_correct,
      Execution.bor, Expr.eval, BankSelect.nextPC, fresh_correct, coreRegS, running, Reactive.running]
    rfl
    done
  · have hz := (BitVec.eq_zero_or_eq_one (running.eval i s)).resolve_right h
    simp only [enable, Expr.eval_bind, decision, Expr.eval, fresh_correct,
      Execution.bor, coreRegS, Reactive.running, running] at h hz ⊢
    simp only [hz]
    split
    all_goals first | contradiction | simp only [BitVec.not_not, BitVec.zero_and]
    rfl
    done
  done

theorem running_same :
    BankSelect.lift (Cache.liftExpr (Reactive.running.bind (fun _ => .lit 0) Machine.coreReg)) = running := by
  rfl
  done

def body : Circuit FinalInput Register Machine.Output where
  next := fun r => match r with
    | .current => .mux (fresh enable) (.input (.input .wire)) (.reg .current)
    | r => BankSelect.body.next r
  output := BankSelect.body.output

def netlist : Netlist Register Machine.Output Machine.Input :=
  .letWire (BankSelect.successor false) (.letWire BankSelect.nextPC (.finish body))

theorem body_next_eq (i : Values Machine.Input) (s : Values Register) (c : BitVec 64) (r : Register w) :
    (body.next r).eval (WithWire.values (WithWire.values i c) (BankSelect.nextPC.eval (WithWire.values i c) s)) s =
      (BankSelect.body.next r).eval
        (WithWire.values (WithWire.values i c) (BankSelect.nextPC.eval (WithWire.values i c) s)) s := by
  cases r <;> simp only [body]
  simp only [BankSelect.body, running_same, Expr.eval, fresh_correct, enable_correct,
    Execution.bor, WithWire.values]
  rfl
  done

theorem netlist_next (i : Machine.Inputs) (s : State) (r : Register w) :
    netlist.step i.values s.values r = (next i s).values r := by
  simpa only [netlist, BankSelect.netlist, Netlist.step, Circuit.step, body_next_eq] using
    BankSelect.netlist_next false i s r
  done

theorem netlist_output (i : Machine.Inputs) (s : State) (o : Machine.Output w) :
    netlist.observe i.values s.values o = Backend.circuit.observe i.values s.values o := by
  simpa only [netlist, BankSelect.netlist, Netlist.observe, Circuit.observe, body] using
    BankSelect.netlist_output false i s o
  done

def component : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  ⟨fun i r => netlist.step i.values r, fun i r => netlist.observe i.values r⟩

def refinement : Timed.Refinement component Backend.component where
  Rel := fun r s => @r = @s.values
  step := fun i _r s h => h ▸ (funext fun _w => funext fun p => netlist_next i s p)
  observe := fun i _r s h => h ▸ (funext fun _w => funext fun p => netlist_output i s p)

def completeRefinement : Timed.Refinement component referenceComponent :=
  refinement.trans Backend.refinement

theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    component.trace s.values inputs = referenceComponent.trace s.reference.machine inputs :=
  completeRefinement.trace_eq s.values s.reference.machine ⟨s, rfl, h, rfl⟩ inputs

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    component.trace (netlist.step i.values s.values) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs := by
  have hn : (netlist.step i.values s.values : Values Register) = (fun {_} r => (next i s).values r) :=
    funext fun w => funext fun r => netlist_next i s r
  rw [hn, ← initialize_machine_next i s hi]
  exact trace_correct (next i s) (initialize_valid i s hi) inputs
  done

end Pinwheel.Hardware.Storage.Backend.CacheEnable
