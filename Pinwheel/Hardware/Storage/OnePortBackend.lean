import Pinwheel.Hardware.Storage.SinglePort
import Pinwheel.Hardware.Storage.PolicyBackend

/-! The one-port fetch organization as a structural netlist on the selected
general backend (`Backend.Policy`): two fetched-word registers, a start-word
register and one flag in place of the same-edge successor lookup, and **one**
composite read of the selected bank.

Three shared wires: the successor fed to the scheduler, the port's address, and
the word behind it. The address is the entered word's untaken candidate on a
dispatch; otherwise word 0 on a commit, and else the current word's taken
candidate on the edge after an entry and its untaken one on every other edge —
the dispatch decision, the deepest select, comes last. This file is the policy's
structural part only: the fed word, the two wires and the four register updates,
each proved to mean the policy's. The rest is the generic backend's. -/
namespace Pinwheel.Hardware.Storage.Backend.OnePort
open Loader

/-- The policy's registers. -/
inductive Reg : Nat → Type where
  | fetched : Bool → Reg 64
  | startWord : Reg 64
  | second : Reg 1

def values (st : SinglePort.Registers) : Values Reg
  | _, .fetched b => st.fetched b
  | _, .startWord => st.startWord
  | _, .second => BitVec.ofBool st.second

abbrev Register := Policy.Register Reg
abbrev State := Policy.State SinglePort.Registers
abbrev E := Policy.E Reg
abbrev W1 := Policy.W1
abbrev W2 := Policy.W2 8
abbrev W3 := Policy.W3 8 64

/-! ### Level 0: the successor fed to the scheduler -/

/-- Feed the taken word only for a branching word with the branch bit set. -/
def choose : E 1 := .band (Policy.sched0 Dispatch.branchingExpr) Policy.branch

def successor : E 64 :=
  .mux Policy.running
    (.mux choose (.reg (.extra (.fetched true))) (.reg (.extra (.fetched false))))
    (.reg (.extra .startWord))

theorem choose_correct (i : Machine.Inputs) (s : State) :
    choose.eval i.values (s.values values) =
      BitVec.ofBool (SinglePort.choose (Cache.base (adapt i s.backend) s.reference.cache) s.reference.machine.core) := by
  simp only [choose, Expr.eval, Policy.sched0_correct, Dispatch.branchingExpr_correct,
    Policy.branch_correct, SinglePort.choose, FetchPolicy.branch, BitVec.ofBool_and_ofBool]
  rfl

theorem successor_correct (i : Machine.Inputs) (s : State) :
    successor.eval i.values (s.values values) = Policy.fedWord SinglePort.policy i s := by
  simp only [successor, Expr.eval, Policy.running_correct, choose_correct]
  simp only [Policy.State.values, Extended.values, values]
  show _ = (if Reactive.runningValue s.reference.machine.core
    then s.policy.fetched (SinglePort.choose (Cache.base (adapt i s.backend) s.reference.cache) s.reference.machine.core)
    else s.policy.startWord)
  cases Reactive.runningValue s.reference.machine.core <;>
    cases SinglePort.choose (Cache.base (adapt i s.backend) s.reference.cache) s.reference.machine.core <;> simp

/-! ### Level 1: the port's address; level 2: the word behind it -/

/-- The entered word's untaken candidate on a dispatch; else word 0 on a commit;
else the current word's taken candidate on the edge after an entry, its untaken
one otherwise. -/
def address : Expr W1 Register 8 :=
  .mux (Policy.sched Dispatch.dispatchingExpr) (Policy.sched (Dispatch.enteredExpr false))
    (.mux (fresh Policy.commit) (.lit 0)
      (.mux (.reg (.extra .second)) (Policy.sched (Dispatch.heldExpr true))
        (Policy.sched (Dispatch.heldExpr false))))

/-- The selected bank's composite read at the address wire: the one read tree. -/
def word : Expr W2 Register 64 := Policy.readAt (fun e => fresh (fresh e)) (.input .wire)

theorem sched_correct (e : Reactive.E w) (i : Machine.Inputs) (s : State) :
    (Policy.sched e).eval (WithWire.values i.values (successor.eval i.values (s.values values)))
        (s.values values) =
      e.eval (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference).values
        s.reference.machine.core.values := by
  rw [Policy.sched_correct, successor_correct, Policy.fedInputs_feed]

theorem address_correct (i : Machine.Inputs) (s : State) :
    address.eval (WithWire.values i.values (successor.eval i.values (s.values values))) (s.values values) =
      FetchPolicy.addresses SinglePort.policy (adapt i s.backend) s.reference 0 := by
  simp only [address, Expr.eval, sched_correct, Dispatch.dispatching_correct, Dispatch.enteredExpr_correct,
    Dispatch.heldExpr_correct, fresh_correct, Policy.commit_correct, Reactive.bool_one]
  simp only [Policy.State.values, Extended.values, values]
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
      have hsec : (Policy.State.reference s).policy.second = s.policy.second := rfl
      by_cases hs : s.policy.second = true
      · simp [hsec, hs]
      · have hs' : s.policy.second = false := by simpa using hs
        simp [hsec, hs']
    · simp
  · have hc := FetchPolicy.dispatch_no_commit (P := SinglePort.policy) (adapt i s.backend) s.reference hd
    rw [hc]
    simp

/-- The word wire is the policy's single read. -/
theorem word_correct (i : Machine.Inputs) (s : State) :
    Policy.values3 values successor address word i s .wire =
      FetchPolicy.reads SinglePort.policy (adapt i s.backend) s.reference 0 := by
  simp only [Policy.values3, WithWire.values]
  unfold word
  rw [Policy.readAt_correct values (fun e => fresh (fresh e)) _ i s
    (fun e => by simp only [fresh_correct])]
  simp only [Expr.eval, WithWire.values, address_correct, FetchPolicy.reads_eq]

/-! ### Level 3: the policy's registers -/

def dispatch3 : Expr W3 Register 1 := fresh (fresh (Policy.sched Dispatch.dispatchingExpr))

/-- The port read the taken candidate on this edge. -/
def taken3 : Expr W3 Register 1 := .band (.inv dispatch3) (.reg (.extra .second))

def regNext : {w : Nat} → Reg w → Expr W3 Register w
  | _, .fetched true => .mux taken3 (.input .wire) (.reg (.extra (.fetched true)))
  | _, .fetched false => .mux taken3 (.reg (.extra (.fetched false))) (.input .wire)
  | _, .startWord => .mux (Policy.leaf Policy.commit) (.input .wire) (.reg (.extra .startWord))
  | _, .second => dispatch3

theorem dispatch3_correct (i : Machine.Inputs) (s : State) :
    dispatch3.eval (Policy.values3 values successor address word i s) (s.values values) =
      BitVec.ofBool (Dispatch.dispatching (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
        s.reference.machine.core) := by
  simp only [dispatch3, Policy.values3, fresh_correct, sched_correct, Dispatch.dispatching_correct]

theorem taken3_correct (i : Machine.Inputs) (s : State) :
    taken3.eval (Policy.values3 values successor address word i s) (s.values values) =
      BitVec.ofBool (SinglePort.readTaken (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
        s.reference.machine.core s.reference.policy) := by
  simp only [taken3, Expr.eval, dispatch3_correct]
  simp only [Policy.State.values, Extended.values, values, SinglePort.readTaken]
  cases Dispatch.dispatching (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
      s.reference.machine.core <;>
    (have hsec : (Policy.State.reference s).policy.second = s.policy.second := rfl
     by_cases hs : s.policy.second = true
     · simp [hsec, hs]
     · have hs' : s.policy.second = false := by simpa using hs
       simp [hsec, hs'])

theorem regNext_correct (i : Machine.Inputs) (s : State) {w : Nat} (x : Reg w) :
    (regNext x).eval (Policy.values3 values successor address word i s) (s.values values) =
      values (Policy.next SinglePort.policy i s).policy x := by
  have hword := word_correct i s
  have hnext : (Policy.next SinglePort.policy i s).policy =
      (SinglePort.next (adapt i s.backend) s.reference).policy := rfl
  cases x with
  | fetched b =>
    show _ = (Policy.next SinglePort.policy i s).policy.fetched b
    rw [hnext, SinglePort.next_fetched]
    cases b <;> simp only [regNext, Expr.eval, taken3_correct, hword] <;>
      simp only [Policy.State.values, Extended.values, values] <;>
      cases SinglePort.readTaken (FetchPolicy.feed SinglePort.policy (adapt i s.backend) s.reference)
        s.reference.machine.core s.reference.policy <;> first | rfl | simp <;> rfl
  | startWord =>
    show _ = (Policy.next SinglePort.policy i s).policy.startWord
    rw [hnext, SinglePort.next_startWord]
    simp only [regNext, Expr.eval, Policy.leaf_correct, Policy.commit_correct, hword]
    simp only [Policy.State.values, Extended.values, values]
    cases Machine.committing (adapt i s.backend) s.reference.machine <;> first | rfl | simp <;> rfl
  | second =>
    show _ = BitVec.ofBool (Policy.next SinglePort.policy i s).policy.second
    rw [hnext, SinglePort.next_second]
    simp only [regNext, dispatch3_correct]

/-! ### The backend -/

def realization : Policy.Realization SinglePort.policy Reg :=
  Policy.Realization.twoWires values successor address word regNext successor_correct regNext_correct

def netlist : Netlist Register Machine.Output Machine.Input := realization.netlist

/-- The rule the one-port organization asks of every pushed word. The capacity
check only turns a push into a rejection, so the rule survives it. -/
def rules : Policy.Rules SinglePort.correct where
  Rule := fun i => i.command = 2 → SinglePort.Ready i.data = true
  adapted := fun i b h hc => by
    -- the capacity check is an admission filter
    have had : adapt i b = Admission.admit (Small.capacity b.small.control.cursor) i := rfl
    rw [had] at hc
    exact h (Admission.admit_command _ i hc)

def Rule (i : Machine.Inputs) : Prop := rules.Rule i

def Valid (s : State) : Prop := Policy.Valid SinglePort.correct s

def component : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  Policy.component realization

def completeRefinement : Timed.RuleRefinement component referenceComponent rules.Rule :=
  Policy.completeRefinement realization SinglePort.correct rules

/-- The emitted netlist's every pre/post-edge observation is the reference
machine's, on any history whose pushed words are ready. -/
theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs)
    (hr : ∀ i ∈ inputs, Rule i) :
    component.trace (s.values values) inputs = referenceComponent.trace s.reference.machine inputs :=
  Policy.trace_correct realization SinglePort.correct rules s h inputs hr

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) (hr : ∀ j ∈ inputs, Rule j) :
    component.trace (netlist.step i.values (s.values values)) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs :=
  Policy.initialized_trace realization SinglePort.correct rules s i hi inputs hr

/-- Behind a push filter that rejects unready words, the netlist refines the
reference behind the same filter for every input history. The filter is not
part of the emitted netlist. -/
def admitted : Timed.Refinement (component.precompose (Admission.admit SinglePort.Ready))
    (referenceComponent.precompose (Admission.admit SinglePort.Ready)) :=
  Admission.discharge SinglePort.Ready completeRefinement

end Pinwheel.Hardware.Storage.Backend.OnePort
