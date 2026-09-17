import Pinwheel.Hardware.Storage.BackendReadback

namespace Pinwheel.Hardware.Storage.Backend.BankSelect
open Loader

/-- Apply the proved command split before substituting physical storage wires. -/
def lift (e : Expr Machine.Input Cache.Register w) : E w :=
  (CommandSplit.expression (Cache.liftExpr CommandSplit.capacity) e).bind
    (fun p => .input p) logical

theorem lift_eq (e : Expr Machine.Input Cache.Register w)
    (i : Values Machine.Input) (s : Values Register) :
    (lift e).eval i s = (Backend.lift e).eval i s := by
  simp only [lift, Backend.lift, Expr.eval_bind, Expr.eval,
    CommandSplit.expression_correct]
  congr 1
  funext n p
  cases p <;> simp [CommandSplit.adapted, CommandSplit.checked, inputs, Small.inputs,
    Cache.liftExpr, CommandSplit.capacity, Small.capacityGate, Expr.eval_bind, Expr.eval,
    logical, Cache.lift, Small.logical, smallReg]
  bv_decide
  done

def selected : E 1 := lift (Cache.liftExpr Machine.selectedGate)
def target : E 8 := lift Cache.target

def bankIndex (b : Bool) (address : Expr I Register 8) : Expr I Register 6 :=
  Execution.readTree 8 (fun k => .concat (.lit (0#1)) (.reg (.index b k) : Expr I Register 5)) address

def bankWord (b : Bool) (address : Expr I Register 6) : Expr I Register 64 :=
  Execution.readTree 6 (Readback.word b) address

/-- Both program banks complete their lookup before the final bank selection.
The address and the two reads use only the same pre-edge register snapshot. -/
def lateRead : E 64 :=
  .mux selected (bankWord true (bankIndex true target))
    (bankWord false (bankIndex false target))

def successor (lateBank : Bool) : E 64 :=
  if lateBank then lateRead else lift (Cache.read Cache.target)

theorem lateRead_eq (i : Machine.Inputs) (s : State) :
    lateRead.eval i.values s.values = Backend.successor.eval i.values s.values := by
  simp only [lateRead, bankWord, bankIndex, Expr.eval, Execution.readTree_correct,
    Readback.word_eval, selected, target, lift_eq, Backend.lift_correct,
    Cache.lift_correct, Machine.selected_correct, Cache.target_correct,
    Backend.successor_correct]
  cases h : Machine.selected (adapt i s) s.reference.machine <;>
    simp [Cache.feed, Reactive.Fetch.resolve, Loader.Store.read, h]
  all_goals rfl
  done

theorem successor_eq (lateBank : Bool) (i : Machine.Inputs) (s : State) :
    (successor lateBank).eval i.values s.values = Backend.successor.eval i.values s.values := by
  cases lateBank <;> simp only [successor, Bool.false_eq_true, reduceIte, lift_eq,
    Backend.successor, lateRead_eq]
  done

def memoryInputs (b : Bool) (p : Store.Input w) : E w :=
  lift (Cache.liftExpr (Machine.memoryInputs b p))

def wordNext (b : Bool) (k : BitVec 5) : E 55 :=
  .mux (.band (memoryInputs b .write)
    (.equal (memoryInputs b .cursor) (.lit (BitVec.ofNat 9 k.toNat))))
    (Dense.compressExpr (.input .data)) (.reg (.word b k))

def circuit : Circuit Machine.Input Register Machine.Output where
  next := fun r => match r with
    | .control r => lift (Cache.circuit.next (.machine (.control r)))
    | .core r => lift (Cache.circuit.next (.machine (.core r)))
    | .word b k => wordNext b k
    | .index b k => .slice 0 5 (by decide) (lift (Cache.circuit.next (.machine (.memory b (.index k)))))
    | .idle b => lift (Cache.circuit.next (.machine (.memory b .idle)))
    | .last b => lift (Cache.circuit.next (.machine (.memory b .last)))
    | .current => lift (Cache.circuit.next .current)
  output := fun o => lift (Cache.circuit.output o)

def feed : {w : Nat} → Reactive.Input w → Expr SuccessorInput Register w
  | _, .successor => .input .wire
  | _, p => fresh (lift (Cache.baseInputs p))

def nextPC : Expr SuccessorInput Register 8 := (Reactive.circuit.next .pc).bind feed coreRegS
def feedFinal (p : Reactive.Input w) : Expr FinalInput Register w := fresh (feed p)

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

/-- False is the command-split control; true moves bank selection after both reads. -/
def netlist (lateBank : Bool) : Netlist Register Machine.Output Machine.Input :=
  .letWire (successor lateBank) (.letWire nextPC (.finish body))

theorem feed_eq (i : Values Machine.Input) (s : Values Register) (c : BitVec 64)
    (p : Reactive.Input w) :
    (feed p).eval (WithWire.values i c) s = (Backend.feed p).eval (WithWire.values i c) s := by
  cases p <;> simp only [feed, Backend.feed, fresh_correct, lift_eq]
  done

theorem pc_eq (i : Values Machine.Input) (s : Values Register) (c : BitVec 64) :
    nextPC.eval (WithWire.values i c) s = Backend.nextPC.eval (WithWire.values i c) s := by
  simp only [nextPC, Backend.nextPC, Expr.eval_bind, feed_eq]
  done

theorem body_next_eq (i : Values Machine.Input) (s : Values Register)
    (c : BitVec 64) (d : BitVec 8) (r : Register w) :
    (body.next r).eval (WithWire.values (WithWire.values i c) d) s =
      (Backend.body.next r).eval (WithWire.values (WithWire.values i c) d) s := by
  cases r <;> simp only [body, Backend.body, feedFinal, Backend.feedFinal,
    Expr.eval_bind, fresh_correct, feed_eq, circuit, Backend.circuit,
    wordNext, Backend.wordNext, memoryInputs, Backend.memoryInputs, Expr.eval, lift_eq]
  all_goals first | rfl | simp only [Execution.bor, Expr.eval, fresh_correct, lift_eq]
  done

theorem body_output_eq (i : Values Machine.Input) (s : Values Register)
    (c : BitVec 64) (d : BitVec 8) (o : Machine.Output w) :
    (body.output o).eval (WithWire.values (WithWire.values i c) d) s =
      (Backend.body.output o).eval (WithWire.values (WithWire.values i c) d) s := by
  cases o <;> simp only [body, Backend.body, feedFinal, Backend.feedFinal,
    Expr.eval_bind, fresh_correct, feed_eq, circuit, Backend.circuit, lift_eq]
  done

theorem netlist_next (lateBank : Bool) (i : Machine.Inputs) (s : State) (r : Register w) :
    (netlist lateBank).step i.values s.values r = (next i s).values r := by
  simpa only [netlist, Backend.netlist, Netlist.step, Circuit.step,
    body_next_eq, pc_eq, successor_eq] using Backend.netlist_next i s r
  done

theorem netlist_output (lateBank : Bool) (i : Machine.Inputs) (s : State) (o : Machine.Output w) :
    (netlist lateBank).observe i.values s.values o = Backend.circuit.observe i.values s.values o := by
  simpa only [netlist, Backend.netlist, Netlist.observe, Circuit.observe,
    body_output_eq, pc_eq, successor_eq] using Backend.netlist_output i s o
  done

def component (lateBank : Bool) : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  ⟨fun i r => (netlist lateBank).step i.values r, fun i r => (netlist lateBank).observe i.values r⟩

def refinement (lateBank : Bool) : Timed.Refinement (component lateBank) Backend.component where
  Rel := fun r s => @r = @s.values
  step := fun i _r s h => h ▸ (funext fun _w => funext fun p => netlist_next lateBank i s p)
  observe := fun i _r s h => h ▸ (funext fun _w => funext fun p => netlist_output lateBank i s p)

def completeRefinement (lateBank : Bool) : Timed.Refinement (component lateBank) referenceComponent :=
  (refinement lateBank).trans Backend.refinement

theorem trace_correct (lateBank : Bool) (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    (component lateBank).trace s.values inputs = referenceComponent.trace s.reference.machine inputs :=
  (completeRefinement lateBank).trace_eq s.values s.reference.machine ⟨s, rfl, h, rfl⟩ inputs

theorem initialized_trace (lateBank : Bool) (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    (component lateBank).trace ((netlist lateBank).step i.values s.values) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs := by
  have hn : ((netlist lateBank).step i.values s.values : Values Register) = (fun {_} r => (next i s).values r) :=
    funext fun w => funext fun r => netlist_next lateBank i s r
  rw [hn, ← initialize_machine_next i s hi]
  exact trace_correct lateBank (next i s) (initialize_valid i s hi) inputs
  done

end Pinwheel.Hardware.Storage.Backend.BankSelect
