import Pinwheel.Hardware.Storage.SinglePort
import Pinwheel.Hardware.Storage.BackendNetlist
import Pinwheel.Hardware.Storage.FetchChoice

/-! The one-port fetch organization as a structural netlist on the selected
general backend: the same dense dictionaries, index maps, loader and scheduler,
with two fetched-word registers, a start-word register and one flag in place of
the same-edge successor lookup, and **one** composite read of the selected bank.

Three shared wires: the successor fed to the scheduler, the port's address, and
the word behind it. The address is the entered word's untaken candidate on a
dispatch; otherwise word 0 on a commit, and else the current word's taken
candidate on the edge after an entry and its untaken one on every other edge —
the dispatch decision, the deepest select, comes last. Every register step
equals the functional dense machine, which projects onto the one-port policy
machine, which refines the atomic reference on ready programs. -/
namespace Pinwheel.Hardware.Storage.Backend.OnePort
open Loader

inductive Register : Nat → Type where
  | inner : Backend.Register w → Register w
  | fetched : Bool → Register 64
  | startWord : Register 64
  | second : Register 1

structure State where
  backend : Backend.State
  fetched : Bool → BitVec 64
  startWord : BitVec 64
  second : Bool

def State.values (s : State) : Values Register
  | _, .inner r => s.backend.values r
  | _, .fetched b => s.fetched b
  | _, .startWord => s.startWord
  | _, .second => BitVec.ofBool s.second

def State.reference (s : State) : SinglePort.State :=
  ⟨s.backend.reference.machine, s.backend.current, ⟨s.fetched, s.startWord, s.second⟩⟩

theorem reference_cache (s : State) : s.reference.cache = s.backend.reference := rfl

/-- Words, index maps, metadata and control follow the general backend; the core,
the cached word and the policy's registers follow the one-port machine. -/
def next (i : Machine.Inputs) (s : State) : State :=
  let n := SinglePort.next (adapt i s.backend) s.reference
  { backend := {Backend.next i s.backend with core := n.machine.core, current := n.current}
    fetched := n.policy.fetched
    startWord := n.policy.startWord
    second := n.policy.second }

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

def commit : E 1 := liftC (Cache.liftExpr Machine.commitGate)

/-- A scheduler expression that does not consult the successor. -/
def feed0 : {w : Nat} → Reactive.Input w → E w
  | _, .successor => .lit 0
  | _, p => liftC (Cache.baseInputs p)

def sched0 (e : Reactive.E w) : E w := e.bind feed0 (fun r => .reg (.inner (.core r)))

/-- Feed the taken word only for a branching word with the branch bit set. -/
def choose : E 1 := .band (sched0 Dispatch.branchingExpr) branch

def successor : E 64 :=
  .mux running (.mux choose (.reg (.fetched true)) (.reg (.fetched false))) (.reg .startWord)

theorem branch_correct (i : Machine.Inputs) (s : State) :
    branch.eval i.values s.values = BitVec.ofBool (FetchPolicy.branch (adapt i s.backend) s.reference) := by
  simp only [branch, liftC_correct, FetchChoice.branch_correct, FetchPolicy.branch, reference_cache]
  rfl

theorem running_correct (i : Machine.Inputs) (s : State) :
    running.eval i.values s.values = BitVec.ofBool (Reactive.runningValue s.reference.machine.core) := by
  simp only [running, Expr.eval_bind, Expr.eval, State.values, Backend.State.values]
  exact Reactive.running_correct ⟨false, false, 0, {}, 0, 0, 0⟩ s.backend.core

theorem commit_correct (i : Machine.Inputs) (s : State) :
    commit.eval i.values s.values = BitVec.ofBool (Machine.committing (adapt i s.backend) s.reference.machine) := by
  simp only [commit, liftC_correct, Cache.lift_correct, Machine.commit_correct]
  rfl

theorem sched0_correct (e : Reactive.E w) (i : Machine.Inputs) (s : State) :
    (sched0 e).eval i.values s.values =
      e.eval ({Cache.base (adapt i s.backend) s.reference.cache with successor := 0} : Reactive.Inputs).values
        s.reference.machine.core.values := by
  have hf : (fun {w} (p : Reactive.Input w) => (feed0 p).eval i.values s.values) =
      (({Cache.base (adapt i s.backend) s.reference.cache with successor := 0} : Reactive.Inputs).values :
        Values Reactive.Input) := by
    funext w p
    cases p <;> first
      | rfl
      | simp only [feed0, liftC_correct, Cache.base_correct, Reactive.Inputs.values, reference_cache]
  have hr : (fun {w} (r : Reactive.Register w) => (Expr.reg (Register.inner (.core r)) : E w).eval i.values s.values) =
      (s.reference.machine.core.values : Values Reactive.Register) := by
    funext w r
    rfl
  simp only [sched0, Expr.eval_bind, hf, hr]

theorem choose_correct (i : Machine.Inputs) (s : State) :
    choose.eval i.values s.values =
      BitVec.ofBool (SinglePort.choose (Cache.base (adapt i s.backend) s.reference.cache) s.reference.machine.core) := by
  simp only [choose, Expr.eval, sched0_correct, Dispatch.branchingExpr_correct, branch_correct,
    SinglePort.choose, FetchPolicy.branch, BitVec.ofBool_and_ofBool]

theorem successor_correct (i : Machine.Inputs) (s : State) :
    successor.eval i.values s.values =
      (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference).successor := by
  simp only [successor, Expr.eval, running_correct, choose_correct, State.values]
  show _ = (if Reactive.runningValue s.reference.machine.core
    then s.fetched (SinglePort.choose (Cache.base (adapt i s.backend) s.reference.cache) s.reference.machine.core)
    else s.startWord)
  cases Reactive.runningValue s.reference.machine.core <;>
    cases SinglePort.choose (Cache.base (adapt i s.backend) s.reference.cache) s.reference.machine.core <;> simp

/-! ### Level 1: below the successor wire, the scheduler's expressions and the address -/

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
      ((FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference).values : Values Reactive.Input) := by
  funext w p
  cases p <;> first
    | (simp only [feed1, values1, Expr.eval, WithWire.values, successor_correct]; rfl)
    | simp only [feed1, values1, fresh_correct, liftC_correct, Cache.base_correct,
        FetchPolicy.feed, Reactive.Inputs.values, reference_cache]

theorem coreReg1_correct (i : Machine.Inputs) (s : State) :
    (fun {w} (r : Reactive.Register w) => (coreReg1 r).eval (values1 i s) s.values) =
      (s.reference.machine.core.values : Values Reactive.Register) := by
  funext w r
  rfl

theorem sched_correct (e : Reactive.E w) (i : Machine.Inputs) (s : State) :
    (sched e).eval (values1 i s) s.values =
      e.eval (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference).values
        s.reference.machine.core.values := by
  simp only [sched, Expr.eval_bind, feed1_correct, coreReg1_correct]

/-- The port's address: the entered word's untaken candidate on a dispatch; else
word 0 on a commit; else the current word's taken candidate on the edge after an
entry, its untaken one otherwise. -/
def address : Expr W1 Register 8 :=
  .mux (sched Dispatch.dispatchingExpr) (sched (Dispatch.enteredExpr false))
    (.mux (fresh commit) (.lit 0)
      (.mux (.reg .second) (sched (Dispatch.heldExpr true)) (sched (Dispatch.heldExpr false))))

theorem address_correct (i : Machine.Inputs) (s : State) :
    address.eval (values1 i s) s.values =
      FetchPolicy.addresses SinglePort.policy (adapt i s.backend) s.reference 0 := by
  simp only [address, Expr.eval, sched_correct, Dispatch.dispatching_correct, Dispatch.enteredExpr_correct,
    Dispatch.heldExpr_correct, State.values]
  simp only [values1, fresh_correct, commit_correct, Reactive.bool_one]
  show _ = (if Machine.committing (adapt i s.backend) s.reference.machine then 0 else
    Dispatch.candidate (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference) s.reference.machine.core
      (SinglePort.readTaken (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
        s.reference.machine.core s.reference.policy))
  rw [Dispatch.candidate_split]
  unfold SinglePort.readTaken
  cases hd : Dispatch.dispatching (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
      s.reference.machine.core
  · cases hc : Machine.committing (adapt i s.backend) s.reference.machine
    · show _ = (if false = true then _ else _)
      cases hs : s.second <;> simp [State.reference, hs]
    · simp
  · have hc := FetchPolicy.dispatch_no_commit (P := SinglePort.policy) (adapt i s.backend) s.reference hd
    rw [hc]
    simp

/-! ### Level 2: the word behind the port; level 3: the body -/

abbrev W2 := WithWire W1 8
abbrev W3 := WithWire W2 64

/-- The selected bank's composite read at the address wire: the one read tree. -/
def word : Expr W2 Register 64 :=
  Execution.readTree 6 (fun k => fresh (fresh (liftC (Cache.chosen (.word k)))))
    (Execution.readTree 8 (fun k => fresh (fresh (liftC (Cache.chosen (.index k))))) (.input .wire))

def feed3 (p : Reactive.Input w) : Expr W3 Register w := fresh (fresh (feed1 p))
def coreReg3 : {w : Nat} → Reactive.Register w → Expr W3 Register w := fun r => .reg (.inner (.core r))
def leaf (e : E w) : Expr W3 Register w := fresh (fresh (fresh e))

def dispatch3 : Expr W3 Register 1 := fresh (fresh (sched Dispatch.dispatchingExpr))

/-- The cached word loads the fed successor on a dispatch or at rest. -/
def enable3 : Expr W3 Register 1 := Execution.bor dispatch3 (.inv (leaf running))

/-- The port read the taken candidate on this edge. -/
def taken3 : Expr W3 Register 1 := .band (.inv dispatch3) (.reg .second)

def body : Circuit W3 Register Machine.Output where
  next := fun r => match r with
    | .inner (.core r) => (Reactive.circuit.next r).bind feed3 coreReg3
    | .inner .current => .mux enable3 (.input (.input (.input .wire))) (.reg (.inner .current))
    | .fetched true => .mux taken3 (.input .wire) (.reg (.fetched true))
    | .fetched false => .mux taken3 (.reg (.fetched false)) (.input .wire)
    | .startWord => .mux (leaf commit) (.input .wire) (.reg .startWord)
    | .second => dispatch3
    | .inner r => leaf (inner (Backend.circuit.next r))
  output := fun o => match o with
    | .core o => (Reactive.circuit.output o).bind feed3 coreReg3
    | .control o => leaf (inner (Backend.circuit.output (.control o)))

def netlist : Netlist Register Machine.Output Machine.Input :=
  .letWire successor (.letWire address (.letWire word (.finish body)))

def values2 (i : Machine.Inputs) (s : State) : Values W2 :=
  WithWire.values (values1 i s) (address.eval (values1 i s) s.values)

def values3 (i : Machine.Inputs) (s : State) : Values W3 :=
  WithWire.values (values2 i s) (word.eval (values2 i s) s.values)

theorem leaf_correct (e : E w) (i : Machine.Inputs) (s : State) :
    (leaf e).eval (values3 i s) s.values = e.eval i.values s.values := by
  simp only [leaf, values3, values2, values1, fresh_correct]

theorem feed3_correct (i : Machine.Inputs) (s : State) :
    (fun {w} (p : Reactive.Input w) => (feed3 p).eval (values3 i s) s.values) =
      ((FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference).values : Values Reactive.Input) := by
  funext w p
  simp only [feed3, values3, values2, fresh_correct]
  exact congrFun (congrFun (feed1_correct i s) _) _

theorem coreReg3_correct (i : Machine.Inputs) (s : State) :
    (fun {w} (r : Reactive.Register w) => (coreReg3 r).eval (values3 i s) s.values) =
      (s.reference.machine.core.values : Values Reactive.Register) := by
  funext w r
  rfl

/-- The word wire is the policy's single read. -/
theorem wire3_word (i : Machine.Inputs) (s : State) :
    values3 i s .wire = FetchPolicy.reads SinglePort.policy (adapt i s.backend) s.reference 0 := by
  simp only [values3, WithWire.values, word, Execution.readTree_correct, values2, fresh_correct,
    Expr.eval, address_correct]
  simp only [values1, fresh_correct, liftC_correct, Cache.chosen, Cache.lift_correct,
    Machine.chosen_correct, FetchPolicy.reads_eq, Loader.Store.read, State.reference]

theorem wire3_successor (i : Machine.Inputs) (s : State) :
    values3 i s (.input (.input .wire)) =
      (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference).successor := by
  simp only [values3, values2, values1, WithWire.values, successor_correct]

theorem dispatch3_correct (i : Machine.Inputs) (s : State) :
    dispatch3.eval (values3 i s) s.values =
      BitVec.ofBool (Dispatch.dispatching (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
        s.reference.machine.core) := by
  simp only [dispatch3, values3, values2, fresh_correct, sched_correct, Dispatch.dispatching_correct]

theorem enable3_correct (i : Machine.Inputs) (s : State) :
    enable3.eval (values3 i s) s.values =
      BitVec.ofBool (Dispatch.dispatching (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
        s.reference.machine.core || !Reactive.runningValue s.reference.machine.core) := by
  simp only [enable3, Execution.bor, Expr.eval, leaf_correct, running_correct, dispatch3_correct]
  cases Dispatch.dispatching (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
      s.reference.machine.core <;>
    cases Reactive.runningValue s.reference.machine.core <;> decide

theorem taken3_correct (i : Machine.Inputs) (s : State) :
    taken3.eval (values3 i s) s.values =
      BitVec.ofBool (SinglePort.readTaken (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
        s.reference.machine.core s.reference.policy) := by
  simp only [taken3, Expr.eval, dispatch3_correct, State.values, SinglePort.readTaken]
  cases Dispatch.dispatching (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
      s.reference.machine.core <;>
    cases hs : s.second <;> simp [State.reference, hs] <;> decide

theorem netlist_step (i : Machine.Inputs) (s : State) (r : Register w) :
    netlist.step i.values s.values r = body.step (values3 i s) s.values r := by
  simp only [netlist, Netlist.step, values3, values2, values1]

theorem netlist_observe (i : Machine.Inputs) (s : State) (o : Machine.Output w) :
    netlist.observe i.values s.values o = body.observe (values3 i s) s.values o := by
  simp only [netlist, Netlist.observe, values3, values2, values1]

theorem netlist_next (i : Machine.Inputs) (s : State) (r : Register w) :
    netlist.step i.values s.values r = (next i s).values r := by
  rw [netlist_step]
  cases r with
  | fetched b =>
    have hn : (next i s).values (.fetched b) =
        (SinglePort.next (adapt i s.backend) s.reference).policy.fetched b := rfl
    rw [hn, SinglePort.next_fetched]
    cases b <;> simp only [Circuit.step, body, Expr.eval, taken3_correct, wire3_word, State.values] <;>
      cases SinglePort.readTaken (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
        s.reference.machine.core s.reference.policy <;> first | rfl | simp <;> rfl
  | startWord =>
    have hn : (next i s).values .startWord =
        (SinglePort.next (adapt i s.backend) s.reference).policy.startWord := rfl
    rw [hn, SinglePort.next_startWord]
    simp only [Circuit.step, body, Expr.eval, leaf_correct, commit_correct, wire3_word, State.values]
    cases Machine.committing (adapt i s.backend) s.reference.machine <;> first | rfl | simp <;> rfl
  | second =>
    have hn : (next i s).values .second =
        BitVec.ofBool (SinglePort.next (adapt i s.backend) s.reference).policy.second := rfl
    rw [hn, SinglePort.next_second]
    simp only [Circuit.step, body, dispatch3_correct]
  | inner r =>
    cases r with
    | core p =>
      simp only [Circuit.step, body, Expr.eval_bind, feed3_correct, coreReg3_correct,
        Reactive.next_correct, State.values, next, Backend.State.values, SinglePort.next, FetchPolicy.next]
    | current =>
      simp only [Circuit.step, body, Expr.eval, enable3_correct, wire3_successor, State.values, next,
        Backend.State.values, SinglePort.next, FetchPolicy.next]
      cases Dispatch.dispatching (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
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

/-- No output reads the policy's registers or the successor: every output is
the general backend's. -/
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

/-! ### Refinement, on ready programs -/

def Valid (s : State) : Prop := SinglePort.Valid s.reference

/-- The rule the one-port organization asks of every pushed word. -/
def Rule (i : Machine.Inputs) : Prop := SinglePort.Ready i.data = true

theorem reference_next (i : Machine.Inputs) (s : State) :
    (next i s).reference = SinglePort.next (adapt i s.backend) s.reference := by
  have hm : (Backend.next i s.backend).small.reference =
      (Cache.next (adapt i s.backend) s.backend.reference).machine :=
    congrArg Cache.State.machine (Backend.reference_next i s.backend)
  simp only [Cache.next, Backend.State.small, Small.State.reference, Machine.State.mk.injEq] at hm
  generalize hn : SinglePort.next (adapt i s.backend) s.reference = n
  have hmach : n.machine =
      {Machine.next (adapt i s.backend) s.reference.machine with core := n.machine.core} := by
    rw [← hn]
    simp [SinglePort.next, FetchPolicy.next]
  simp only [next, hn]
  simp only [State.reference, Backend.State.reference, Backend.State.small, Small.State.reference]
  show (⟨_, n.current, ⟨n.policy.fetched, n.policy.startWord, n.policy.second⟩⟩ : SinglePort.State) =
    ⟨n.machine, n.current, n.policy⟩
  rw [hmach]
  simp only [FetchPolicy.State.mk.injEq, Machine.State.mk.injEq, and_true, true_and]
  exact ⟨hm.1, hm.2.2⟩

def component : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  ⟨fun i r => netlist.step i.values r, fun i r => netlist.observe i.values r⟩

def functional : Timed.Component Machine.Inputs State (Values Machine.Output) :=
  ⟨next, fun i s => Backend.circuit.observe i.values s.backend.values⟩

theorem valid_next (i : Machine.Inputs) (s : State) (h : Valid s) (hr : Rule i) : Valid (next i s) := by
  unfold Valid
  rw [reference_next]
  exact FetchPolicy.valid_next SinglePort.correct (adapt i s.backend) s.reference h hr

theorem machine_next (i : Machine.Inputs) (s : State) (h : Valid s) :
    (next i s).reference.machine =
      Machine.next (capacityInput i s.reference.machine) s.reference.machine := by
  rw [reference_next]
  exact FetchPolicy.machine_next SinglePort.correct (adapt i s.backend) s.reference h

theorem output_correct (i : Machine.Inputs) (s : State) (h : Valid s) (o : Machine.Output w) :
    Backend.circuit.observe i.values s.backend.values o =
      Machine.circuit.observe (capacityInput i s.reference.machine).values s.reference.machine.values o :=
  Backend.output_correct i s.backend h.1 o

def refinement : Timed.RuleRefinement functional referenceComponent Rule where
  Rel := fun s t => Valid s ∧ s.reference.machine = t
  step := fun i s t hr h => by
    rcases h with ⟨hv, rfl⟩
    exact ⟨valid_next i s hv hr, machine_next i s hv⟩
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

def completeRefinement : Timed.RuleRefinement component referenceComponent Rule :=
  structuralRefinement.transRule refinement

/-- The emitted netlist's every pre/post-edge observation is the reference
machine's, on any history whose pushed words are ready. -/
theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs)
    (hr : ∀ i ∈ inputs, Rule i) :
    component.trace s.values inputs = referenceComponent.trace s.reference.machine inputs :=
  completeRefinement.trace_eq s.values s.reference.machine ⟨s, rfl, h, rfl⟩ inputs hr

theorem initialize_valid (i : Machine.Inputs) (s : State) (hi : i.init = true) : Valid (next i s) := by
  unfold Valid
  rw [reference_next]
  exact FetchPolicy.initialize_valid SinglePort.correct (adapt i s.backend) s.reference
    (by simpa [adapt, Small.adapt] using hi)

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) (hr : ∀ j ∈ inputs, Rule j) :
    component.trace (netlist.step i.values s.values) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs := by
  have hn : (netlist.step i.values s.values : Values Register) = (fun {_} r => (next i s).values r) :=
    funext fun w => funext fun r => netlist_next i s r
  have hm : (next i s).reference.machine =
      Machine.next (capacityInput i s.reference.machine) s.reference.machine := by
    rw [reference_next]
    exact FetchPolicy.initialize_machine_next (P := SinglePort.policy) (adapt i s.backend) s.reference
      (by simpa [adapt, Small.adapt] using hi)
  rw [hn, ← hm]
  exact trace_correct (next i s) (initialize_valid i s hi) inputs hr

end Pinwheel.Hardware.Storage.Backend.OnePort
