import Pinwheel.Hardware.Storage.Decoupled
import Pinwheel.Hardware.Storage.BackendNetlist
import Pinwheel.Hardware.Storage.FetchChoice

/-! The decoupled prefetch machine as a structural netlist on the selected
general backend: the same 32-entry dense dictionaries, index maps, loader and
scheduler, with two fetched-word registers and a start-word register in place of
the same-edge successor lookup. Shared wires: the successor fed to the scheduler
(a fetched word chosen by the branch bit while running, the start word at rest)
and the two candidate addresses of the next edge, computed from this edge's
dispatch decision; each dictionary read is addressed by a wire. Every register
step equals the functional dense machine, which projects onto the proved
decoupled machine, which refines the atomic reference. -/
namespace Pinwheel.Hardware.Storage.Backend.Prefetch
open Loader

inductive Register : Nat → Type where
  | inner : Backend.Register w → Register w
  | fetched : Bool → Register 64
  | startWord : Register 64

structure State where
  backend : Backend.State
  fetched : Bool → BitVec 64
  startWord : BitVec 64

def State.values (s : State) : Values Register
  | _, .inner r => s.backend.values r
  | _, .fetched b => s.fetched b
  | _, .startWord => s.startWord

def State.reference (s : State) : Storage.Decoupled.State :=
  ⟨s.backend.reference.machine, s.backend.current, s.fetched, s.startWord⟩

theorem reference_cache (s : State) : s.reference.cache = s.backend.reference := rfl

/-- Words, index maps, metadata and control follow the general backend; the core,
the cached word, the fetched words and the start word follow the decoupled machine. -/
def next (i : Machine.Inputs) (s : State) : State :=
  let n := Storage.Decoupled.next (adapt i s.backend) s.reference
  { backend := {Backend.next i s.backend with core := n.machine.core, current := n.current}
    fetched := n.fetched
    startWord := n.startWord }

abbrev E := Expr Machine.Input Register

def inner (e : Backend.E w) : E w := e.bind (fun p => .input p) (fun r => .reg (.inner r))

theorem inner_correct (e : Backend.E w) (i : Machine.Inputs) (s : State) :
    (inner e).eval i.values s.values = e.eval i.values s.backend.values := by
  simp only [inner, Expr.eval_bind, Expr.eval, State.values]

def liftC (e : Expr Machine.Input Cache.Register w) : E w := inner (Backend.lift e)

theorem liftC_correct (e : Expr Machine.Input Cache.Register w) (i : Machine.Inputs) (s : State) :
    (liftC e).eval i.values s.values = e.eval (adapt i s.backend).values s.backend.reference.values := by
  simp only [liftC, inner_correct, Backend.lift_correct]

/-! ### Level 0: the successor fed to the scheduler -/

def branch : E 1 := liftC FetchChoice.branch

def running : E 1 := Reactive.running.bind (fun _ => .lit 0) (fun r => .reg (.inner (.core r)))

def successor : E 64 :=
  .mux running (.mux branch (.reg (.fetched true)) (.reg (.fetched false))) (.reg .startWord)

def commit : E 1 := liftC (Cache.liftExpr Machine.commitGate)

theorem branch_correct (i : Machine.Inputs) (s : State) :
    branch.eval i.values s.values = BitVec.ofBool (Storage.Decoupled.branch (adapt i s.backend) s.reference) := by
  simp only [branch, liftC_correct, FetchChoice.branch_correct, Storage.Decoupled.branch, reference_cache]
  rfl

theorem running_correct (i : Machine.Inputs) (s : State) :
    running.eval i.values s.values = BitVec.ofBool (Reactive.runningValue s.reference.machine.core) := by
  simp only [running, Expr.eval_bind, Expr.eval, State.values, Backend.State.values]
  exact Reactive.running_correct ⟨false, false, 0, {}, 0, 0, 0⟩ s.backend.core

theorem successor_correct (i : Machine.Inputs) (s : State) :
    successor.eval i.values s.values = (Storage.Decoupled.feed (adapt i s.backend) s.reference).successor := by
  simp only [successor, Expr.eval, running_correct, branch_correct, State.values, Storage.Decoupled.feed]
  cases Reactive.runningValue s.reference.machine.core <;>
    cases Storage.Decoupled.branch (adapt i s.backend) s.reference <;> simp <;> rfl

theorem commit_correct (i : Machine.Inputs) (s : State) :
    commit.eval i.values s.values = BitVec.ofBool (Machine.committing (adapt i s.backend) s.reference.machine) := by
  simp only [commit, liftC_correct, Cache.lift_correct, Machine.commit_correct]
  rfl

/-! ### Level 1: below the successor wire, the scheduler's expressions -/

abbrev W1 := WithWire Machine.Input 64

def feed1 : {w : Nat} → Reactive.Input w → Expr W1 Register w
  | _, .successor => .input .wire
  | _, p => fresh (liftC (Cache.baseInputs p))

def coreReg1 : {w : Nat} → Reactive.Register w → Expr W1 Register w := fun r => .reg (.inner (.core r))

/-- Any scheduler expression, fed the shared successor. -/
def sched (e : Reactive.E w) : Expr W1 Register w := e.bind feed1 coreReg1

def values1 (i : Machine.Inputs) (s : State) : Values W1 :=
  WithWire.values i.values (successor.eval i.values s.values)

theorem feed1_correct (i : Machine.Inputs) (s : State) :
    (fun {w} (p : Reactive.Input w) => (feed1 p).eval (values1 i s) s.values) =
      ((Storage.Decoupled.feed (adapt i s.backend) s.reference).values : Values Reactive.Input) := by
  funext w p
  cases p <;> first
    | (simp only [feed1, values1, Expr.eval, WithWire.values, successor_correct]; rfl)
    | simp only [feed1, values1, fresh_correct, liftC_correct, Cache.base_correct,
        Storage.Decoupled.feed, Reactive.Inputs.values, reference_cache]

theorem coreReg1_correct (i : Machine.Inputs) (s : State) :
    (fun {w} (r : Reactive.Register w) => (coreReg1 r).eval (values1 i s) s.values) =
      (s.reference.machine.core.values : Values Reactive.Register) := by
  funext w r
  rfl

theorem sched_correct (e : Reactive.E w) (i : Machine.Inputs) (s : State) :
    (sched e).eval (values1 i s) s.values =
      e.eval (Storage.Decoupled.feed (adapt i s.backend) s.reference).values s.reference.machine.core.values := by
  simp only [sched, Expr.eval_bind, feed1_correct, coreReg1_correct]

theorem candidate1_correct (i : Machine.Inputs) (s : State) (b : Bool) :
    (sched (Storage.Dispatch.candidateExpr b)).eval (values1 i s) s.values =
      Storage.Dispatch.candidate (Storage.Decoupled.feed (adapt i s.backend) s.reference) s.reference.machine.core b := by
  simp only [sched_correct, Storage.Dispatch.candidateExpr_correct]

/-! ### Levels 2 and 3: the candidate wires, then the body -/

abbrev W2 := WithWire W1 8
abbrev W3 := WithWire W2 8

def feed3 (p : Reactive.Input w) : Expr W3 Register w := fresh (fresh (feed1 p))
def coreReg3 : {w : Nat} → Reactive.Register w → Expr W3 Register w := fun r => .reg (.inner (.core r))
def leaf (e : E w) : Expr W3 Register w := fresh (fresh (fresh e))

/-- The cached word loads the fed successor on a dispatch or at rest. -/
def enable3 : Expr W3 Register 1 :=
  Execution.bor (fresh (fresh (sched Storage.Dispatch.dispatchingExpr))) (.inv (leaf running))

/-- The selected bank's composite read, at a wire-supplied or literal address. -/
def read3 (address : Expr W3 Register 8) : Expr W3 Register 64 :=
  Execution.readTree 6 (fun k => leaf (liftC (Cache.chosen (.word k))))
    (Execution.readTree 8 (fun k => leaf (liftC (Cache.chosen (.index k)))) address)

def body : Circuit W3 Register Machine.Output where
  next := fun r => match r with
    | .inner (.core r) => (Reactive.circuit.next r).bind feed3 coreReg3
    | .inner .current => .mux enable3 (.input (.input (.input .wire))) (.reg (.inner .current))
    | .fetched true => read3 (.input (.input .wire))
    | .fetched false => read3 (.input .wire)
    | .startWord => .mux (leaf commit) (read3 (.lit 0)) (.reg .startWord)
    | .inner r => leaf (inner (Backend.circuit.next r))
  output := fun o => match o with
    | .core o => (Reactive.circuit.output o).bind feed3 coreReg3
    | .control o => leaf (inner (Backend.circuit.output (.control o)))

def netlist : Netlist Register Machine.Output Machine.Input :=
  .letWire successor (.letWire (sched (Storage.Dispatch.candidateExpr true))
    (.letWire (fresh (sched (Storage.Dispatch.candidateExpr false))) (.finish body)))

def values3 (i : Machine.Inputs) (s : State) : Values W3 :=
  WithWire.values (WithWire.values (values1 i s)
      ((sched (Storage.Dispatch.candidateExpr true)).eval (values1 i s) s.values))
    ((sched (Storage.Dispatch.candidateExpr false)).eval (values1 i s) s.values)

theorem leaf_correct (e : E w) (i : Machine.Inputs) (s : State) :
    (leaf e).eval (values3 i s) s.values = e.eval i.values s.values := by
  simp only [leaf, values3, values1, fresh_correct]

theorem feed3_correct (i : Machine.Inputs) (s : State) :
    (fun {w} (p : Reactive.Input w) => (feed3 p).eval (values3 i s) s.values) =
      ((Storage.Decoupled.feed (adapt i s.backend) s.reference).values : Values Reactive.Input) := by
  funext w p
  simp only [feed3, values3, fresh_correct]
  exact congrFun (congrFun (feed1_correct i s) _) _

theorem coreReg3_correct (i : Machine.Inputs) (s : State) :
    (fun {w} (r : Reactive.Register w) => (coreReg3 r).eval (values3 i s) s.values) =
      (s.reference.machine.core.values : Values Reactive.Register) := by
  funext w r
  rfl

theorem read3_correct (i : Machine.Inputs) (s : State) (a : Expr W3 Register 8) :
    (read3 a).eval (values3 i s) s.values =
      Loader.Store.read (s.reference.machine.memory (Machine.selected (adapt i s.backend) s.reference.machine))
        (a.eval (values3 i s) s.values) := by
  simp only [read3, Execution.readTree_correct, leaf_correct, liftC_correct, Cache.chosen,
    Cache.lift_correct, Machine.chosen_correct, Loader.Store.read, State.reference]

theorem wire3_successor (i : Machine.Inputs) (s : State) :
    values3 i s (.input (.input .wire)) = (Storage.Decoupled.feed (adapt i s.backend) s.reference).successor := by
  simp only [values3, values1, WithWire.values, successor_correct]

theorem wire3_taken (i : Machine.Inputs) (s : State) :
    values3 i s (.input .wire) =
      Storage.Dispatch.candidate (Storage.Decoupled.feed (adapt i s.backend) s.reference) s.reference.machine.core true := by
  simp only [values3, WithWire.values, candidate1_correct]

theorem wire3_untaken (i : Machine.Inputs) (s : State) :
    values3 i s .wire =
      Storage.Dispatch.candidate (Storage.Decoupled.feed (adapt i s.backend) s.reference) s.reference.machine.core false := by
  simp only [values3, WithWire.values, candidate1_correct]

theorem running3 (i : Machine.Inputs) (s : State) :
    (leaf running).eval (values3 i s) s.values = BitVec.ofBool (Reactive.runningValue s.reference.machine.core) := by
  rw [leaf_correct, running_correct]

theorem dispatch3 (i : Machine.Inputs) (s : State) :
    (fresh (fresh (sched Storage.Dispatch.dispatchingExpr))).eval (values3 i s) s.values =
      BitVec.ofBool (Storage.Dispatch.dispatching (Storage.Decoupled.feed (adapt i s.backend) s.reference)
        s.reference.machine.core) := by
  simp only [values3, fresh_correct, sched_correct, Storage.Dispatch.dispatching_correct]

theorem enable3_correct (i : Machine.Inputs) (s : State) :
    enable3.eval (values3 i s) s.values =
      BitVec.ofBool (Storage.Dispatch.dispatching (Storage.Decoupled.feed (adapt i s.backend) s.reference)
        s.reference.machine.core || !Reactive.runningValue s.reference.machine.core) := by
  simp only [enable3, Execution.bor, Expr.eval, running3, dispatch3]
  cases Storage.Dispatch.dispatching (Storage.Decoupled.feed (adapt i s.backend) s.reference) s.reference.machine.core <;>
    cases Reactive.runningValue s.reference.machine.core <;> decide

theorem netlist_step (i : Machine.Inputs) (s : State) (r : Register w) :
    netlist.step i.values s.values r = body.step (values3 i s) s.values r := by
  simp only [netlist, Netlist.step, values3, values1, fresh_correct]

theorem netlist_observe (i : Machine.Inputs) (s : State) (o : Machine.Output w) :
    netlist.observe i.values s.values o = body.observe (values3 i s) s.values o := by
  simp only [netlist, Netlist.observe, values3, values1, fresh_correct]

theorem netlist_next (i : Machine.Inputs) (s : State) (r : Register w) :
    netlist.step i.values s.values r = (next i s).values r := by
  rw [netlist_step]
  cases r with
  | fetched b =>
    cases b <;> simp only [Circuit.step, body, read3_correct, Expr.eval, wire3_taken, wire3_untaken,
      State.values, next, Storage.Decoupled.next]
  | startWord =>
    simp only [Circuit.step, body, Expr.eval, leaf_correct, commit_correct, read3_correct, State.values,
      next, Storage.Decoupled.next]
    cases Machine.committing (adapt i s.backend) s.reference.machine <;> simp <;> rfl
  | inner r =>
    cases r with
    | core p =>
      simp only [Circuit.step, body, Expr.eval_bind, feed3_correct, coreReg3_correct,
        Reactive.next_correct, State.values, next, Backend.State.values, Storage.Decoupled.next]
    | current =>
      simp only [Circuit.step, body, Expr.eval, enable3_correct, wire3_successor, State.values, next,
        Backend.State.values, Storage.Decoupled.next]
      cases Storage.Dispatch.dispatching (Storage.Decoupled.feed (adapt i s.backend) s.reference)
          s.reference.machine.core <;>
        cases Reactive.runningValue s.reference.machine.core <;> simp <;> rfl
    | control p =>
      simpa only [Circuit.step, body, leaf_correct, inner_correct, State.values, next,
        Backend.State.values] using Backend.next_correct i s.backend (.control p)
    | word b k =>
      simpa only [Circuit.step, body, leaf_correct, inner_correct, State.values, next,
        Backend.State.values] using Backend.next_correct i s.backend (.word b k)
    | index b k =>
      simpa only [Circuit.step, body, leaf_correct, inner_correct, State.values, next,
        Backend.State.values] using Backend.next_correct i s.backend (.index b k)
    | idle b =>
      simpa only [Circuit.step, body, leaf_correct, inner_correct, State.values, next,
        Backend.State.values] using Backend.next_correct i s.backend (.idle b)
    | last b =>
      simpa only [Circuit.step, body, leaf_correct, inner_correct, State.values, next,
        Backend.State.values] using Backend.next_correct i s.backend (.last b)

/-- No output reads the fetched words, the start word or the successor: every
output is the general backend's. -/
theorem netlist_output (i : Machine.Inputs) (s : State) (o : Machine.Output w) :
    netlist.observe i.values s.values o = Backend.circuit.observe i.values s.backend.values o := by
  rw [netlist_observe]
  cases o with
  | control o =>
    simp only [Circuit.observe, body, leaf_correct, inner_correct]
  | core o =>
    simp only [Circuit.observe, body, Expr.eval_bind, feed3_correct, coreReg3_correct, Backend.circuit,
      Backend.lift_correct, Cache.circuit, Cache.feed_correct_circuit, Cache.coreReg, Cache.lift,
      Expr.eval, Cache.State.values, Machine.State.values]
    cases o with
    | state r => rfl
    | readA => rfl
    | busy => rfl
    | readB =>
      simp only [Reactive.circuit, Reactive.target_correct]
      rfl

/-! ### Refinement -/

def Valid (s : State) : Prop := Storage.Decoupled.Valid s.reference

theorem reference_next (i : Machine.Inputs) (s : State) :
    (next i s).reference = Storage.Decoupled.next (adapt i s.backend) s.reference := by
  have hm : (Backend.next i s.backend).small.reference =
      (Cache.next (adapt i s.backend) s.backend.reference).machine :=
    congrArg Cache.State.machine (Backend.reference_next i s.backend)
  simp only [Cache.next, Backend.State.small, Small.State.reference, Machine.State.mk.injEq] at hm
  generalize hn : Storage.Decoupled.next (adapt i s.backend) s.reference = n
  have hmach : n.machine =
      {Machine.next (adapt i s.backend) s.reference.machine with core := n.machine.core} := by
    rw [← hn]
    simp [Storage.Decoupled.next]
  simp only [next, hn]
  simp only [State.reference, Backend.State.reference, Backend.State.small, Small.State.reference]
  show (⟨_, n.current, n.fetched, n.startWord⟩ : Storage.Decoupled.State) =
    ⟨n.machine, n.current, n.fetched, n.startWord⟩
  rw [hmach]
  simp only [Storage.Decoupled.State.mk.injEq, Machine.State.mk.injEq, and_true, true_and]
  exact ⟨hm.1, hm.2.2⟩

def component : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  ⟨fun i r => netlist.step i.values r, fun i r => netlist.observe i.values r⟩

def functional : Timed.Component Machine.Inputs State (Values Machine.Output) :=
  ⟨next, fun i s => Backend.circuit.observe i.values s.backend.values⟩

theorem valid_next (i : Machine.Inputs) (s : State) (h : Valid s) : Valid (next i s) := by
  simpa only [Valid, reference_next] using Storage.Decoupled.valid_next (adapt i s.backend) s.reference h

theorem machine_next (i : Machine.Inputs) (s : State) (h : Valid s) :
    (next i s).reference.machine =
      Machine.next (capacityInput i s.reference.machine) s.reference.machine := by
  rw [reference_next]
  exact Storage.Decoupled.machine_next (adapt i s.backend) s.reference h

theorem output_correct (i : Machine.Inputs) (s : State) (h : Valid s) (o : Machine.Output w) :
    Backend.circuit.observe i.values s.backend.values o =
      Machine.circuit.observe (capacityInput i s.reference.machine).values s.reference.machine.values o :=
  Backend.output_correct i s.backend h.1 o

def refinement : Timed.Refinement functional referenceComponent where
  Rel := fun s t => Valid s ∧ s.reference.machine = t
  step := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact ⟨valid_next i s hv, machine_next i s hv⟩
  observe := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact funext fun w => funext fun o => output_correct i s hv o

def structuralRefinement : Timed.Refinement component functional where
  Rel := fun r s => @r = @s.values
  step := fun i r s h => by
    subst r
    exact funext fun w => funext fun p => netlist_next i s p
  observe := fun i r s h => by
    subst r
    exact funext fun w => funext fun p => netlist_output i s p

def completeRefinement : Timed.Refinement component referenceComponent :=
  structuralRefinement.trans refinement

theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    component.trace s.values inputs = referenceComponent.trace s.reference.machine inputs :=
  completeRefinement.trace_eq s.values s.reference.machine ⟨s, rfl, h, rfl⟩ inputs

theorem initialize_valid (i : Machine.Inputs) (s : State) (hi : i.init = true) : Valid (next i s) := by
  simpa only [Valid, reference_next] using
    Storage.Decoupled.initialize_valid (adapt i s.backend) s.reference (by simpa [adapt, Small.adapt] using hi)

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    component.trace (netlist.step i.values s.values) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs := by
  have hn : (netlist.step i.values s.values : Values Register) = (fun {_} r => (next i s).values r) :=
    funext fun w => funext fun r => netlist_next i s r
  have hm : (next i s).reference.machine =
      Machine.next (capacityInput i s.reference.machine) s.reference.machine := by
    rw [reference_next]
    exact Storage.Decoupled.initialize_machine_next (adapt i s.backend) s.reference
      (by simpa [adapt, Small.adapt] using hi)
  rw [hn, ← hm]
  exact trace_correct (next i s) (initialize_valid i s hi) inputs

end Pinwheel.Hardware.Storage.Backend.Prefetch
