import Pinwheel.Hardware.Storage.DenseStore
import Pinwheel.Hardware.Storage.CacheContract
import Pinwheel.Hardware.Storage.CommandSplit

/-! The selected general backend: two 32 x 55-bit dictionaries, two 256 x 5-bit
index banks, atomic loader, reactive scheduler, and a 64-bit current-word cache.
All implementation wiring is a Circuit value; the host capacity contract is explicit. -/
namespace Pinwheel.Hardware.Storage.Backend
open Loader

inductive Register : Nat → Type where
  | control : Loader.Register w → Register w
  | core : Reactive.Register w → Register w
  | word : Bool → BitVec 5 → Register 55
  | index : Bool → BitVec 8 → Register 5
  | idle : Bool → Register 6
  | last : Bool → Register 8
  | current : Register 64

structure State where
  control : Loader.State
  core : Reactive.State
  words : Bool → Vector (BitVec 55) 32
  indices : Bool → Vector (BitVec 5) 256
  idle : Bool → BitVec 6
  last : Bool → BitVec 8
  current : BitVec 64

def State.values (s : State) : Values Register
  | _, .control r => s.control.values r | _, .core r => s.core.values r
  | _, .word b k => (s.words b)[k.toNat] | _, .index b k => (s.indices b)[k.toNat]
  | _, .idle b => s.idle b | _, .last b => s.last b | _, .current => s.current

def State.small (s : State) : Small.State :=
  ⟨s.control, s.core, fun b => (s.words b).map Dense.expand, s.indices, s.idle, s.last⟩

def State.reference (s : State) : Cache.State := ⟨s.small.reference, s.current⟩

def adapt (i : Machine.Inputs) (s : State) : Machine.Inputs := Small.adapt i s.small

abbrev E := Expr Machine.Input Register

def smallReg : {w : Nat} → Small.Register w → E w
  | _, .control r => .reg (.control r) | _, .core r => .reg (.core r)
  | _, .word b k => Dense.expandExpr (.reg (.word b k))
  | _, .index b k => .reg (.index b k) | _, .idle b => .reg (.idle b)
  | _, .last b => .reg (.last b)

def inputs (p : Machine.Input w) : E w := (Small.inputs p).bind (fun p => .input p) smallReg

def logical : {w : Nat} → Cache.Register w → E w
  | _, .machine r => (Small.logical r).bind (fun p => .input p) smallReg
  | _, .current => .reg .current

def lift (e : Expr Machine.Input Cache.Register w) : E w := e.bind inputs logical

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

def writing (i : Machine.Inputs) (s : State) (b : Bool) (k : BitVec 5) : Bool :=
  let m := Machine.memoryInput (adapt i s) s.reference.machine b
  m.write && m.cursor == BitVec.ofNat 9 k.toNat

def next (i : Machine.Inputs) (s : State) : State :=
  let n := Cache.next (adapt i s) s.reference
  ⟨n.machine.control, n.machine.core,
    fun b => Vector.ofFn fun k => if writing i s b (BitVec.ofFin k)
      then Dense.compress i.data else (s.words b)[k.val],
    fun b => Vector.ofFn fun k => (n.machine.memory b (.index (BitVec.ofFin k))).extractLsb' 0 5,
    fun b => n.machine.memory b .idle, fun b => n.machine.memory b .last, n.current⟩

theorem smallReg_correct (i : Machine.Inputs) (s : State) (r : Small.Register w) :
    (smallReg r).eval i.values s.values = s.small.values r := by
  cases r <;> simp [smallReg, Dense.expand_correct, Expr.eval, State.values,
    State.small, Small.State.values]
  done

theorem logical_correct (i : Machine.Inputs) (s : State) (r : Cache.Register w) :
    (logical r).eval i.values s.values = s.reference.values r := by
  cases r <;> simp [logical, Expr.eval_bind, Expr.eval, smallReg_correct,
    Small.logical_correct, State.reference, Cache.State.values, State.values]
  done

theorem inputs_correct (i : Machine.Inputs) (s : State) (p : Machine.Input w) :
    (inputs p).eval i.values s.values = (adapt i s).values p := by
  simpa only [inputs, Expr.eval_bind, Expr.eval, smallReg_correct, adapt] using
    Small.inputs_correct i s.small p
  done

theorem lift_correct (i : Machine.Inputs) (s : State) (e : Expr Machine.Input Cache.Register w) :
    (lift e).eval i.values s.values = e.eval (adapt i s).values s.reference.values := by
  simp only [lift, Expr.eval_bind, inputs_correct, logical_correct]
  done

theorem next_correct (i : Machine.Inputs) (s : State) (r : Register w) :
    circuit.step i.values s.values r = (next i s).values r := by
  cases r
  all_goals simp only [Circuit.step, circuit, Expr.eval, lift_correct, next,
    State.values, Vector.getElem_ofFn]
  all_goals first | exact Cache.next_correct (adapt i s) s.reference _ |
    exact congrArg (BitVec.extractLsb' 0 5) (Cache.next_correct (adapt i s) s.reference _) | skip
  simp [wordNext, memoryInputs, lift_correct, Cache.lift_correct, Machine.memory_correct,
    Dense.compress_correct, Expr.eval, State.values, Machine.Inputs.values, Store.Inputs.values,
    writing, Bool.beq_eq_decide_eq]
  done

set_option backward.isDefEq.respectTransparency false in
theorem word_correct (i : Machine.Inputs) (s : State) (b : Bool) (k : Fin 32) :
    Dense.expand ((next i s).words b)[k.val] =
      (Cache.next (adapt i s) s.reference).machine.memory b (.word (BitVec.ofNat 6 k.val)) := by
  simp only [next, Vector.getElem_ofFn, Cache.next, Machine.next, Store.tick]
  have hk : k.val < 64 := by omega
  simp only [Store.offset, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk,
    writing, BitVec.extractLsb'_eq_self]
  split
  all_goals simp_all [State.reference, State.small, Small.State.reference, Machine.memoryInput,
    adapt, Small.adapt, Nat.mod_eq_of_lt hk]
  simp_all [Loader.push, Loader.goodWord, Machine.controlInput, Nat.mod_eq_of_lt (by omega : k.val < 512)]
  rename_i hw
  simp_all [hw.2, Nat.mod_eq_of_lt (by omega : k.val < 512), Small.capacity, k.isLt]
  simp_all [Loader.enabled, Dense.accepted_roundtrip]
  done

theorem next_small (i : Machine.Inputs) (s : State) :
    (next i s).small = Small.project (Cache.next (adapt i s) s.reference).machine := by
  simp only [State.small, next, Small.project]
  simp only [Small.State.mk.injEq, and_self, true_and, and_true, eq_self]
  funext b
  apply Vector.ext
  exact fun k hk => by simpa only [next, Vector.getElem_map, Vector.getElem_ofFn] using word_correct i s b ⟨k, hk⟩
  done

theorem next_fits (i : Machine.Inputs) (s : State) :
    Small.Fits (Cache.next (adapt i s) s.reference).machine := by
  simpa only [Small.Fits, Cache.next, State.reference, adapt] using Small.next_fits i s.small
  done

theorem reference_next (i : Machine.Inputs) (s : State) :
    (next i s).reference = Cache.next (adapt i s) s.reference := by
  change Cache.State.mk (next i s).small.reference (Cache.next (adapt i s) s.reference).current = _
  rw [next_small, Small.reference_project _ (next_fits i s)]
  done

def Valid (s : State) : Prop := Cache.Valid s.reference

theorem valid_next (i : Machine.Inputs) (s : State) (h : Valid s) : Valid (next i s) := by
  simpa only [Valid, reference_next] using Cache.valid_next (adapt i s) s.reference h
  done

theorem initialize_valid (i : Machine.Inputs) (s : State) (hi : i.init = true) : Valid (next i s) := by
  simpa only [Valid, reference_next] using Cache.initialize_valid (adapt i s) s.reference hi
  done

/-- The public capacity restriction rejects oversized pushes. All other commands
retain the atomic-loader contract, including malformed and busy commands. -/
def capacityInput (i : Machine.Inputs) (s : Machine.State) : Machine.Inputs :=
  {i with command := if i.command == 2 && !Small.capacity s.control.cursor i.data then 6 else i.command}

def referenceComponent : Timed.Component Machine.Inputs Machine.State (Values Machine.Output) :=
  ⟨fun i s => Machine.next (capacityInput i s) s,
    fun i s => Machine.circuit.observe (capacityInput i s).values s.values⟩

def component : Timed.Component Machine.Inputs State (Values Machine.Output) :=
  ⟨next, fun i s => circuit.observe i.values s.values⟩

/-- The initializing edge reaches the reference machine's own next state,
even if the cache invariant did not hold before initialization. -/
theorem initialize_machine_next (i : Machine.Inputs) (s : State) (hi : i.init = true) :
    (next i s).reference.machine = Machine.next (capacityInput i s.reference.machine) s.reference.machine := by
  exact (congrArg Cache.State.machine (reference_next i s)).trans
    (Cache.initialize_machine_next (adapt i s) s.reference hi)
  done

theorem machine_next (i : Machine.Inputs) (s : State) (h : Valid s) :
    (next i s).reference.machine = Machine.next (capacityInput i s.reference.machine) s.reference.machine := by
  exact (congrArg Cache.State.machine (reference_next i s)).trans (Cache.machine_next (adapt i s) s.reference h)
  done

theorem output_correct (i : Machine.Inputs) (s : State) (h : Valid s) (o : Machine.Output w) :
    circuit.observe i.values s.values o =
      Machine.circuit.observe (capacityInput i s.reference.machine).values s.reference.machine.values o := by
  exact (lift_correct i s (Cache.circuit.output o)).trans (Cache.output_correct (adapt i s) s.reference h o)
  done

def refinement : Timed.Refinement component referenceComponent where
  Rel := fun s t => Valid s ∧ s.reference.machine = t
  step := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact ⟨valid_next i s hv, machine_next i s hv⟩
  observe := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact funext fun w => funext fun o => output_correct i s hv o

def structuralComponent : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  ⟨fun i r => circuit.step i.values r, fun i r => circuit.observe i.values r⟩

def structuralRefinement : Timed.Refinement structuralComponent component where
  Rel := fun r s => @r = @s.values
  step := fun i r s h => by
    subst r
    exact funext fun w => funext fun p => next_correct i s p
  observe := fun _ _ _ h => congrArg _ h

def completeRefinement : Timed.Refinement structuralComponent referenceComponent :=
  structuralRefinement.trans refinement

theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    structuralComponent.trace s.values inputs = referenceComponent.trace s.reference.machine inputs :=
  completeRefinement.trace_eq s.values s.reference.machine ⟨s, rfl, h, rfl⟩ inputs

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    structuralComponent.trace (circuit.step i.values s.values) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs := by
  have hn : (circuit.step i.values s.values : Values Register) = (fun {_} r => (next i s).values r) :=
    funext fun w => funext fun r => next_correct i s r
  rw [hn, ← initialize_machine_next i s hi]
  exact trace_correct (next i s) (initialize_valid i s hi) inputs
  done

end Pinwheel.Hardware.Storage.Backend
