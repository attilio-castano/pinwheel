import Pinwheel.Hardware.Storage.FetchPolicy
import Pinwheel.Hardware.Storage.BackendNetlist
import Pinwheel.Hardware.Storage.FetchChoice
import Pinwheel.Hardware.NetlistExtend

/-! The selected general backend under any fetch policy.

A fetch policy changes one thing about the backend: where the scheduler's
successor word comes from. `core` is the backend with that word as a wire input —
dense dictionaries, index maps, loader, scheduler and the cached word, which
loads the fed word on a dispatch or at rest — proved once against the
functional step (`core_step`, `core_observe`). A policy's structural part is
then small: an expression for the fed word, two shared wires below it, and the
next-state expressions of its own registers (`Realization.twoWires`). From a
realization and the policy's `Correct`, every register and output step, the
projection onto the policy machine, the refinement of the atomic reference under
the policy's rule and the trace theorems follow, once. -/
namespace Pinwheel.Hardware.Storage.Backend.Policy
open Loader

/-! ### The backend with the successor as an input -/

/-- Machine inputs and the fed successor word. -/
abbrev WS := WithWire Machine.Input 64

def feedW : {w : Nat} → Reactive.Input w → Expr WS Backend.Register w
  | _, .successor => .input .wire
  | _, p => fresh (Backend.lift (Cache.baseInputs p))

/-- A scheduler expression over the backend's registers, fed the successor wire. -/
def schedW (e : Reactive.E w) : Expr WS Backend.Register w := e.bind feedW (fun r => .reg (.core r))

/-- The cached word loads the fed successor on a dispatch or at rest. -/
def enableW : Expr WS Backend.Register 1 :=
  Execution.bor (schedW Dispatch.dispatchingExpr) (.inv (schedW Reactive.running))

def core : Circuit WS Backend.Register Machine.Output where
  next := fun r => match r with
    | .core r => schedW (Reactive.circuit.next r)
    | .current => .mux enableW (.input .wire) (.reg .current)
    | r => fresh (Backend.circuit.next r)
  output := fun o => match o with
    | .core o => schedW (Reactive.circuit.output o)
    | .control o => fresh (Backend.circuit.output (.control o))

/-- What the scheduler sees when fed `x`. -/
def fedInputs (x : BitVec 64) (i : Machine.Inputs) (b : Backend.State) : Reactive.Inputs :=
  {Cache.base (adapt i b) b.reference with successor := x}

/-- The general backend's step with the scheduler fed `x`. -/
def fedNext (x : BitVec 64) (i : Machine.Inputs) (b : Backend.State) : Backend.State :=
  {Backend.next i b with
    core := Reactive.stepValue (fedInputs x i b) b.reference.machine.core
    current := if Dispatch.dispatching (fedInputs x i b) b.reference.machine.core ||
        !Reactive.runningValue b.reference.machine.core then x else b.current}

theorem feedW_correct (x : BitVec 64) (i : Machine.Inputs) (b : Backend.State) :
    (fun {w} (p : Reactive.Input w) => (feedW p).eval (WithWire.values i.values x) b.values) =
      ((fedInputs x i b).values : Values Reactive.Input) := by
  funext w p
  cases p <;> first
    | rfl
    | simp only [feedW, fresh_correct, Backend.lift_correct, Cache.base_correct, fedInputs,
        Reactive.Inputs.values]

theorem schedW_correct (e : Reactive.E w) (x : BitVec 64) (i : Machine.Inputs) (b : Backend.State) :
    (schedW e).eval (WithWire.values i.values x) b.values =
      e.eval (fedInputs x i b).values b.reference.machine.core.values := by
  have hr : (fun {w} (r : Reactive.Register w) =>
      (Expr.reg (Backend.Register.core r) : Expr WS Backend.Register w).eval
        (WithWire.values i.values x) b.values) =
      (b.reference.machine.core.values : Values Reactive.Register) := by
    funext w r
    rfl
  simp only [schedW, Expr.eval_bind, feedW_correct, hr]

theorem enableW_correct (x : BitVec 64) (i : Machine.Inputs) (b : Backend.State) :
    enableW.eval (WithWire.values i.values x) b.values =
      BitVec.ofBool (Dispatch.dispatching (fedInputs x i b) b.reference.machine.core ||
        !Reactive.runningValue b.reference.machine.core) := by
  simp only [enableW, Execution.bor, Expr.eval, schedW_correct, Dispatch.dispatching_correct,
    Reactive.running_correct]
  cases Dispatch.dispatching (fedInputs x i b) b.reference.machine.core <;>
    cases Reactive.runningValue b.reference.machine.core <;> decide

theorem core_step (x : BitVec 64) (i : Machine.Inputs) (b : Backend.State) (r : Backend.Register w) :
    core.step (WithWire.values i.values x) b.values r = (fedNext x i b).values r := by
  cases r with
  | core p =>
    simp only [Circuit.step, core, schedW_correct, Reactive.next_correct, fedNext,
      Backend.State.values]
  | current =>
    simp only [Circuit.step, core, Expr.eval, enableW_correct, WithWire.values, fedNext,
      Backend.State.values]
    cases Dispatch.dispatching (fedInputs x i b) b.reference.machine.core <;>
      cases Reactive.runningValue b.reference.machine.core <;> simp <;> rfl
  | control p =>
    simpa only [Circuit.step, core, fresh_correct, fedNext, Backend.State.values] using
      Backend.next_correct i b (.control p)
  | word k j =>
    simpa only [Circuit.step, core, fresh_correct, fedNext, Backend.State.values] using
      Backend.next_correct i b (.word k j)
  | index k j =>
    simpa only [Circuit.step, core, fresh_correct, fedNext, Backend.State.values] using
      Backend.next_correct i b (.index k j)
  | idle k =>
    simpa only [Circuit.step, core, fresh_correct, fedNext, Backend.State.values] using
      Backend.next_correct i b (.idle k)
  | last k =>
    simpa only [Circuit.step, core, fresh_correct, fedNext, Backend.State.values] using
      Backend.next_correct i b (.last k)

/-- No output reads the fed successor: every output is the general backend's. -/
theorem core_observe (x : BitVec 64) (i : Machine.Inputs) (b : Backend.State) (o : Machine.Output w) :
    core.observe (WithWire.values i.values x) b.values o = Backend.circuit.observe i.values b.values o := by
  cases o with
  | control o =>
    simp only [Circuit.observe, core, fresh_correct]
  | core o =>
    simp only [Circuit.observe, core, schedW_correct, Backend.circuit, Backend.lift_correct,
      Cache.circuit, Expr.eval_bind, Cache.feed_correct_circuit, Cache.coreReg, Cache.lift,
      Expr.eval, Cache.State.values, Machine.State.values]
    cases o with
    | state r => rfl
    | readA => rfl
    | busy => rfl
    | readB =>
      simp only [Reactive.circuit, Reactive.target_correct]
      rfl

/-! ### The functional machine: the backend and a policy's registers -/

section Functional
variable {p : Nat} {σ : Type}

structure State (σ : Type) where
  backend : Backend.State
  policy : σ

def State.reference (s : State σ) : FetchPolicy.State σ :=
  ⟨s.backend.reference.machine, s.backend.current, s.policy⟩

theorem reference_cache (s : State σ) : s.reference.cache = s.backend.reference := rfl

variable (P : FetchPolicy.Policy p σ)

/-- The word the policy feeds the scheduler on this edge. -/
def fedWord (i : Machine.Inputs) (s : State σ) : BitVec 64 :=
  (FetchPolicy.feed P (adapt i s.backend) s.reference).successor

theorem fedInputs_feed (i : Machine.Inputs) (s : State σ) :
    fedInputs (fedWord P i s) i s.backend = FetchPolicy.feed P (adapt i s.backend) s.reference := rfl

/-- Words, index maps, metadata and control follow the general backend; the core,
the cached word and the policy's registers follow the policy machine. -/
def next (i : Machine.Inputs) (s : State σ) : State σ :=
  let n := FetchPolicy.next P (adapt i s.backend) s.reference
  { backend := {Backend.next i s.backend with core := n.machine.core, current := n.current}
    policy := n.policy }

theorem next_backend (i : Machine.Inputs) (s : State σ) :
    (next P i s).backend = fedNext (fedWord P i s) i s.backend := rfl

theorem next_policy (i : Machine.Inputs) (s : State σ) :
    (next P i s).policy = (FetchPolicy.next P (adapt i s.backend) s.reference).policy := rfl

theorem reference_next (i : Machine.Inputs) (s : State σ) :
    (next P i s).reference = FetchPolicy.next P (adapt i s.backend) s.reference := by
  have hm : (Backend.next i s.backend).small.reference =
      (Cache.next (adapt i s.backend) s.backend.reference).machine :=
    congrArg Cache.State.machine (Backend.reference_next i s.backend)
  simp only [Cache.next, Backend.State.small, Small.State.reference, Machine.State.mk.injEq] at hm
  generalize hn : FetchPolicy.next P (adapt i s.backend) s.reference = n
  have hmach : n.machine =
      {Machine.next (adapt i s.backend) s.reference.machine with core := n.machine.core} := by
    rw [← hn]
    simp [FetchPolicy.next]
  simp only [next, hn]
  simp only [State.reference, Backend.State.reference, Backend.State.small, Small.State.reference]
  show (⟨_, n.current, n.policy⟩ : FetchPolicy.State σ) = ⟨n.machine, n.current, n.policy⟩
  rw [hmach]
  simp only [FetchPolicy.State.mk.injEq, Machine.State.mk.injEq, and_true, true_and]
  exact ⟨hm.1, hm.2.2⟩

end Functional

/-! ### Expressions a policy builds its wires from -/

section Expressions
variable {σ : Type} {X : Nat → Type}

/-- The backend's registers and the policy's. -/
abbrev Register (X : Nat → Type) := Extended Backend.Register X

abbrev E (X : Nat → Type) := Expr Machine.Input (Register X)

def State.values (val : σ → Values X) (s : State σ) : Values (Register X) :=
  Extended.values s.backend.values (val s.policy)

def inner (e : Backend.E w) : E X w := e.bind (fun p => .input p) (fun r => .reg (.inner r))

theorem inner_correct (val : σ → Values X) (e : Backend.E w) (i : Machine.Inputs) (s : State σ) :
    (inner (X := X) e).eval i.values (s.values val) = e.eval i.values s.backend.values := by
  simp only [inner, Expr.eval_bind, Expr.eval, State.values, Extended.values]

def liftC (e : Expr Machine.Input Cache.Register w) : E X w := inner (Backend.lift e)

theorem liftC_correct (val : σ → Values X) (e : Expr Machine.Input Cache.Register w)
    (i : Machine.Inputs) (s : State σ) :
    (liftC (X := X) e).eval i.values (s.values val) =
      e.eval (adapt i s.backend).values s.backend.reference.values := by
  simp only [liftC, inner_correct, Backend.lift_correct]

def branch : E X 1 := liftC FetchChoice.branch

def running : E X 1 := Reactive.running.bind (fun _ => .lit 0) (fun r => .reg (.inner (.core r)))

def commit : E X 1 := liftC (Cache.liftExpr Machine.commitGate)

theorem branch_correct (val : σ → Values X) (i : Machine.Inputs) (s : State σ) :
    (branch (X := X)).eval i.values (s.values val) =
      BitVec.ofBool (FetchPolicy.branch (adapt i s.backend) s.reference) := by
  simp only [branch, liftC_correct, FetchChoice.branch_correct, FetchPolicy.branch, reference_cache]
  rfl

theorem running_correct (val : σ → Values X) (i : Machine.Inputs) (s : State σ) :
    (running (X := X)).eval i.values (s.values val) =
      BitVec.ofBool (Reactive.runningValue s.reference.machine.core) := by
  simp only [running, Expr.eval_bind, Expr.eval, State.values, Extended.values, Backend.State.values]
  exact Reactive.running_correct ⟨false, false, 0, {}, 0, 0, 0⟩ s.backend.core

theorem commit_correct (val : σ → Values X) (i : Machine.Inputs) (s : State σ) :
    (commit (X := X)).eval i.values (s.values val) =
      BitVec.ofBool (Machine.committing (adapt i s.backend) s.reference.machine) := by
  simp only [commit, liftC_correct, Cache.lift_correct, Machine.commit_correct]
  rfl

/-- A scheduler expression that does not consult the successor, for the fed word itself. -/
def feed0 : {w : Nat} → Reactive.Input w → E X w
  | _, .successor => .lit 0
  | _, p => liftC (Cache.baseInputs p)

def sched0 (e : Reactive.E w) : E X w := e.bind feed0 (fun r => .reg (.inner (.core r)))

theorem sched0_correct (val : σ → Values X) (e : Reactive.E w) (i : Machine.Inputs) (s : State σ) :
    (sched0 (X := X) e).eval i.values (s.values val) =
      e.eval (fedInputs 0 i s.backend).values s.reference.machine.core.values := by
  have hf : (fun {w} (p : Reactive.Input w) => (feed0 (X := X) p).eval i.values (s.values val)) =
      ((fedInputs 0 i s.backend).values : Values Reactive.Input) := by
    funext w p
    cases p <;> first
      | rfl
      | simp only [feed0, liftC_correct, Cache.base_correct, fedInputs, Reactive.Inputs.values]
  have hr : (fun {w} (r : Reactive.Register w) =>
      (Expr.reg (Extended.inner (Backend.Register.core r)) : E X w).eval i.values (s.values val)) =
      (s.reference.machine.core.values : Values Reactive.Register) := by
    funext w r
    rfl
  simp only [sched0, Expr.eval_bind, hf, hr]

/-- Below the fed successor wire. -/
abbrev W1 := WithWire Machine.Input 64

def feed1 : {w : Nat} → Reactive.Input w → Expr W1 (Register X) w
  | _, .successor => .input .wire
  | _, p => fresh (liftC (Cache.baseInputs p))

/-- Any scheduler expression, fed the shared successor. -/
def sched (e : Reactive.E w) : Expr W1 (Register X) w :=
  e.bind feed1 (fun r => .reg (.inner (.core r)))

theorem sched_correct (val : σ → Values X) (e : Reactive.E w) (x : BitVec 64) (i : Machine.Inputs)
    (s : State σ) :
    (sched (X := X) e).eval (WithWire.values i.values x) (s.values val) =
      e.eval (fedInputs x i s.backend).values s.reference.machine.core.values := by
  have hf : (fun {w} (p : Reactive.Input w) =>
      (feed1 (X := X) p).eval (WithWire.values i.values x) (s.values val)) =
      ((fedInputs x i s.backend).values : Values Reactive.Input) := by
    funext w p
    cases p <;> first
      | rfl
      | simp only [feed1, fresh_correct, liftC_correct, Cache.base_correct, fedInputs,
          Reactive.Inputs.values]
  have hr : (fun {w} (r : Reactive.Register w) =>
      (Expr.reg (Extended.inner (Backend.Register.core r)) : Expr W1 (Register X) w).eval
        (WithWire.values i.values x) (s.values val)) =
      (s.reference.machine.core.values : Values Reactive.Register) := by
    funext w r
    rfl
  simp only [sched, Expr.eval_bind, hf, hr]

/-- The selected bank's composite read at an address, in any wire context given
how to place a level-0 expression there. -/
def readAt {J : Nat → Type} (place : {w : Nat} → E X w → Expr J (Register X) w)
    (address : Expr J (Register X) 8) : Expr J (Register X) 64 :=
  Execution.readTree 6 (fun k => place (liftC (Cache.chosen (.word k))))
    (Execution.readTree 8 (fun k => place (liftC (Cache.chosen (.index k)))) address)

theorem readAt_correct {J : Nat → Type} (val : σ → Values X)
    (place : {w : Nat} → E X w → Expr J (Register X) w) (j : Values J) (i : Machine.Inputs) (s : State σ)
    (hplace : ∀ {w : Nat} (e : E X w), (place e).eval j (s.values val) = e.eval i.values (s.values val))
    (address : Expr J (Register X) 8) :
    (readAt place address).eval j (s.values val) =
      Loader.Store.read (s.reference.machine.memory (Machine.selected (adapt i s.backend) s.reference.machine))
        (address.eval j (s.values val)) := by
  simp only [readAt, Execution.readTree_correct, hplace, liftC_correct, Cache.chosen,
    Cache.lift_correct, Machine.chosen_correct, Loader.Store.read, State.reference]

end Expressions

/-! ### Realizations -/

section Realizations
variable {p : Nat} {σ : Type} {X : Nat → Type} {P : FetchPolicy.Policy p σ}

/-- A netlist over the backend's registers and the policy's that steps the
backend as `core` fed the policy's word, steps the policy's registers as the
policy, and shows `core`'s outputs. -/
structure Realization (P : FetchPolicy.Policy p σ) (X : Nat → Type) where
  values : σ → Values X
  netlist : Netlist (Register X) Machine.Output Machine.Input
  inner : ∀ (i : Machine.Inputs) (s : State σ) {w : Nat} (r : Backend.Register w),
    netlist.step i.values (s.values values) (.inner r) =
      core.step (WithWire.values i.values (fedWord P i s)) s.backend.values r
  extra : ∀ (i : Machine.Inputs) (s : State σ) {w : Nat} (x : X w),
    netlist.step i.values (s.values values) (.extra x) = values (next P i s).policy x
  observe : ∀ (i : Machine.Inputs) (s : State σ) {w : Nat} (o : Machine.Output w),
    netlist.observe i.values (s.values values) o =
      core.observe (WithWire.values i.values (fedWord P i s)) s.backend.values o

variable (Z : Realization P X)

theorem netlist_next (i : Machine.Inputs) (s : State σ) (r : Register X w) :
    Z.netlist.step i.values (s.values Z.values) r = ((next P i s).values Z.values) r := by
  cases r with
  | inner r =>
    rw [Z.inner, core_step]
    rfl
  | extra x => exact Z.extra i s x

theorem netlist_output (i : Machine.Inputs) (s : State σ) (o : Machine.Output w) :
    Z.netlist.observe i.values (s.values Z.values) o =
      Backend.circuit.observe i.values s.backend.values o := by
  rw [Z.observe, core_observe]

/-! The two-wire shape: the fed successor, then two policy wires, then the body. -/

abbrev W2 (a : Nat) := WithWire W1 a
abbrev W3 (a b : Nat) := WithWire (W2 a) b

/-- `core`'s inputs in the body's context. -/
def input3 {a b : Nat} : {w : Nat} → WS w → Expr (W3 a b) (Register X) w
  | _, .wire => .input (.input (.input .wire))
  | _, .input q => .input (.input (.input (.input q)))

/-- A level-0 expression in the body's context. -/
def leaf {a b : Nat} (e : E X w) : Expr (W3 a b) (Register X) w := fresh (fresh (fresh e))

def body {a b : Nat} (regNext : {w : Nat} → X w → Expr (W3 a b) (Register X) w) :
    Circuit (W3 a b) (Register X) Machine.Output where
  next := fun r => match r with
    | .inner r => (core.next r).inner input3
    | .extra x => regNext x
  output := fun o => (core.output o).inner input3

def values3 {a b : Nat} (val : σ → Values X) (fed : E X 64) (wire2 : Expr W1 (Register X) a)
    (wire3 : Expr (W2 a) (Register X) b) (i : Machine.Inputs) (s : State σ) : Values (W3 a b) :=
  let v1 : Values W1 := WithWire.values i.values (fed.eval i.values (s.values val))
  let v2 : Values (W2 a) := WithWire.values v1 (wire2.eval v1 (s.values val))
  WithWire.values v2 (wire3.eval v2 (s.values val))

theorem leaf_correct {a b : Nat} (val : σ → Values X) (fed : E X 64) (wire2 : Expr W1 (Register X) a)
    (wire3 : Expr (W2 a) (Register X) b) (e : E X w) (i : Machine.Inputs) (s : State σ) :
    (leaf e).eval (values3 val fed wire2 wire3 i s) (s.values val) = e.eval i.values (s.values val) := by
  simp only [leaf, values3, fresh_correct]

/-- A realization from the fed word, two wires and the policy registers' updates. -/
def Realization.twoWires {a b : Nat} (val : σ → Values X) (fed : E X 64)
    (wire2 : Expr W1 (Register X) a) (wire3 : Expr (W2 a) (Register X) b)
    (regNext : {w : Nat} → X w → Expr (W3 a b) (Register X) w)
    (fed_correct : ∀ (i : Machine.Inputs) (s : State σ),
      fed.eval i.values (s.values val) = fedWord P i s)
    (extra_correct : ∀ (i : Machine.Inputs) (s : State σ) {w : Nat} (x : X w),
      (regNext x).eval (values3 val fed wire2 wire3 i s) (s.values val) = val (next P i s).policy x) :
    Realization P X where
  values := val
  netlist := .letWire fed (.letWire wire2 (.letWire wire3 (.finish (body regNext))))
  inner := fun i s _ r => by
    have hin : (fun {w} (q : WS w) =>
        (input3 (X := X) (a := a) (b := b) q).eval (values3 val fed wire2 wire3 i s) (s.values val)) =
        (WithWire.values i.values (fedWord P i s) : Values WS) := by
      funext w q
      cases q with
      | wire =>
        simp only [input3, Expr.eval, values3, WithWire.values]
        exact fed_correct i s
      | input q => rfl
    show ((core.next r).inner input3).eval (values3 val fed wire2 wire3 i s) (s.values val) = _
    rw [Expr.inner_correct, hin]
    rfl
  extra := fun i s _ x => extra_correct i s x
  observe := fun i s _ o => by
    have hin : (fun {w} (q : WS w) =>
        (input3 (X := X) (a := a) (b := b) q).eval (values3 val fed wire2 wire3 i s) (s.values val)) =
        (WithWire.values i.values (fedWord P i s) : Values WS) := by
      funext w q
      cases q with
      | wire =>
        simp only [input3, Expr.eval, values3, WithWire.values]
        exact fed_correct i s
      | input q => rfl
    show ((core.output o).inner input3).eval (values3 val fed wire2 wire3 i s) (s.values val) = _
    rw [Expr.inner_correct, hin]
    rfl

end Realizations

/-! ### Refinement of the atomic reference -/

section Refinement
variable {p : Nat} {σ : Type} {X : Nat → Type} {P : FetchPolicy.Policy p σ}

/-- The policy's rule at the backend's ports. The capacity check only turns a
push into a rejection, so a rule has to survive that. -/
structure Rules (C : FetchPolicy.Correct P) where
  Rule : Machine.Inputs → Prop
  adapted : ∀ (i : Machine.Inputs) (b : Backend.State), Rule i → C.Rule (adapt i b)

/-- A policy without a rule. -/
def Rules.none (C : FetchPolicy.Correct P) (h : ∀ i, C.Rule i) : Rules C := ⟨fun _ => True, fun i b _ => h (adapt i b)⟩

variable (Z : Realization P X) (C : FetchPolicy.Correct P) (R : Rules C)

def Valid (s : State σ) : Prop := FetchPolicy.Valid C s.reference

def component : Timed.Component Machine.Inputs (Values (Register X)) (Values Machine.Output) :=
  ⟨fun i r => Z.netlist.step i.values r, fun i r => Z.netlist.observe i.values r⟩

variable (P) in
def functional : Timed.Component Machine.Inputs (State σ) (Values Machine.Output) :=
  ⟨next P, fun i s => Backend.circuit.observe i.values s.backend.values⟩

theorem valid_next (i : Machine.Inputs) (s : State σ) (h : Valid C s) (hr : R.Rule i) :
    Valid C (next P i s) := by
  unfold Valid
  rw [reference_next]
  exact FetchPolicy.valid_next C (adapt i s.backend) s.reference h (R.adapted i s.backend hr)

theorem machine_next (i : Machine.Inputs) (s : State σ) (h : Valid C s) :
    (next P i s).reference.machine =
      Machine.next (capacityInput i s.reference.machine) s.reference.machine := by
  rw [reference_next]
  exact FetchPolicy.machine_next C (adapt i s.backend) s.reference h

theorem output_correct (i : Machine.Inputs) (s : State σ) (h : Valid C s) (o : Machine.Output w) :
    Backend.circuit.observe i.values s.backend.values o =
      Machine.circuit.observe (capacityInput i s.reference.machine).values s.reference.machine.values o :=
  Backend.output_correct i s.backend h.1 o

def refinement : Timed.RuleRefinement (functional P) referenceComponent R.Rule where
  Rel := fun s t => Valid C s ∧ s.reference.machine = t
  step := fun i s t hr h => by
    rcases h with ⟨hv, rfl⟩
    exact ⟨valid_next C R i s hv hr, machine_next C i s hv⟩
  observe := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact funext fun w => funext fun o => output_correct C i s hv o

def structuralRefinement : Timed.Refinement (component Z) (functional P) where
  Rel := fun r s => @r = @State.values σ X Z.values s
  step := fun i r s h => by
    subst r
    exact funext fun w => funext fun q => netlist_next Z i s q
  observe := fun i r s h => by
    subst r
    exact funext fun w => funext fun q => netlist_output Z i s q

/-- The emitted netlist refines the atomic reference, edge for edge, on inputs
satisfying the policy's rule. -/
def completeRefinement : Timed.RuleRefinement (component Z) referenceComponent R.Rule :=
  (structuralRefinement Z).transRule (refinement C R)

theorem related (s : State σ) (h : Valid C s) :
    (completeRefinement Z C R).Rel (s.values Z.values) s.reference.machine := ⟨s, rfl, h, rfl⟩

theorem trace_correct (s : State σ) (h : Valid C s) (inputs : List Machine.Inputs)
    (hr : ∀ i ∈ inputs, R.Rule i) :
    (component Z).trace (s.values Z.values) inputs = referenceComponent.trace s.reference.machine inputs :=
  (completeRefinement Z C R).trace_eq _ _ (related Z C R s h) inputs hr

theorem initialize_valid (i : Machine.Inputs) (s : State σ) (hi : i.init = true) :
    Valid C (next P i s) := by
  unfold Valid
  rw [reference_next]
  exact FetchPolicy.initialize_valid C (adapt i s.backend) s.reference
    (by simpa [adapt, Small.adapt] using hi)

theorem initialized_trace (s : State σ) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) (hr : ∀ j ∈ inputs, R.Rule j) :
    (component Z).trace (Z.netlist.step i.values (s.values Z.values)) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs := by
  have hn : (Z.netlist.step i.values (s.values Z.values) : Values (Register X)) =
      (fun {_} r => ((next P i s).values Z.values) r) :=
    funext fun w => funext fun r => netlist_next Z i s r
  have hm : (next P i s).reference.machine =
      Machine.next (capacityInput i s.reference.machine) s.reference.machine := by
    rw [reference_next]
    exact FetchPolicy.initialize_machine_next (P := P) (adapt i s.backend) s.reference
      (by simpa [adapt, Small.adapt] using hi)
  rw [hn, ← hm]
  exact trace_correct Z C R (next P i s) (initialize_valid C i s hi) inputs hr

end Refinement

end Pinwheel.Hardware.Storage.Backend.Policy
