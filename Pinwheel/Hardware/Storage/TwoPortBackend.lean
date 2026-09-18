import Pinwheel.Hardware.Storage.TwoPort
import Pinwheel.Hardware.Storage.PolicyBackend

/-! The two-port fetch organization as a structural netlist on the selected
general backend (`Backend.Policy`): the decoupled organization's registers and
fed word, with **two** composite reads. Port 0 reads word 0 on a commit and the
untaken candidate otherwise; its word is a shared wire, loaded by the untaken
register on every edge and by the start word on a commit. A commit edge does not
dispatch, so the commit select sits beside the held candidate and the dispatch
decision still comes last. No rule on programs. -/
namespace Pinwheel.Hardware.Storage.Backend.TwoPort
open Loader

/-- The policy's registers: the decoupled organization's. -/
inductive Reg : Nat → Type where
  | fetched : Bool → Reg 64
  | startWord : Reg 64

def values (st : Decoupled.Registers) : Values Reg
  | _, .fetched b => st.fetched b
  | _, .startWord => st.startWord

abbrev Register := Policy.Register Reg
abbrev State := Policy.State Decoupled.Registers
abbrev E := Policy.E Reg
abbrev W1 := Policy.W1
abbrev W2 := Policy.W2 64
abbrev W3 := Policy.W3 64 8

def successor : E 64 :=
  .mux Policy.running
    (.mux Policy.branch (.reg (.extra (.fetched true))) (.reg (.extra (.fetched false))))
    (.reg (.extra .startWord))

theorem successor_correct (i : Machine.Inputs) (s : State) :
    successor.eval i.values (s.values values) = Policy.fedWord Storage.TwoPort.policy i s := by
  simp only [successor, Expr.eval, Policy.running_correct, Policy.branch_correct]
  simp only [Policy.State.values, Extended.values, values]
  show _ = (if Reactive.runningValue s.reference.machine.core
    then s.policy.fetched (FetchPolicy.branch (adapt i s.backend) s.reference) else s.policy.startWord)
  cases Reactive.runningValue s.reference.machine.core <;>
    cases FetchPolicy.branch (adapt i s.backend) s.reference <;> simp

theorem sched_correct (e : Reactive.E w) (i : Machine.Inputs) (s : State) :
    (Policy.sched e).eval (WithWire.values i.values (successor.eval i.values (s.values values)))
        (s.values values) =
      e.eval (FetchPolicy.feed Storage.TwoPort.policy (adapt i s.backend) s.reference).values
        s.reference.machine.core.values := by
  rw [Policy.sched_correct, successor_correct, Policy.fedInputs_feed]

/-- Port 0's address: the entered word's untaken candidate on a dispatch; else
word 0 on a commit; else the current word's untaken candidate. -/
def address0 : Expr W1 Register 8 :=
  .mux (Policy.sched Dispatch.dispatchingExpr) (Policy.sched (Dispatch.enteredExpr false))
    (.mux (fresh Policy.commit) (.lit 0) (Policy.sched (Dispatch.heldExpr false)))

theorem address0_correct (i : Machine.Inputs) (s : State) :
    address0.eval (WithWire.values i.values (successor.eval i.values (s.values values))) (s.values values) =
      Storage.TwoPort.address0 (adapt i s.backend) s.reference := by
  simp only [address0, Expr.eval, sched_correct, Dispatch.dispatching_correct, Dispatch.enteredExpr_correct,
    Dispatch.heldExpr_correct, fresh_correct, Policy.commit_correct, Reactive.bool_one]
  unfold Storage.TwoPort.address0
  rw [Dispatch.candidate_split]
  cases hd : Dispatch.dispatching (FetchPolicy.feed Storage.TwoPort.policy (adapt i s.backend) s.reference)
      s.reference.machine.core
  · cases Machine.committing (adapt i s.backend) s.reference.machine <;> simp
  · have hc := FetchPolicy.dispatch_no_commit (P := Storage.TwoPort.policy) (adapt i s.backend) s.reference hd
    rw [hc]
    simp

/-- The word behind port 0, shared by the untaken register and the start word. -/
def word0 : Expr W1 Register 64 := Policy.readAt (fun e => fresh e) address0

/-- Port 1's address: the taken candidate. -/
def taken : Expr W2 Register 8 := fresh (Policy.sched (Dispatch.candidateExpr true))

theorem word0_correct (i : Machine.Inputs) (s : State) :
    Policy.values3 values successor word0 taken i s (.input .wire) =
      FetchPolicy.reads Storage.TwoPort.policy (adapt i s.backend) s.reference 0 := by
  simp only [Policy.values3, WithWire.values]
  unfold word0
  rw [Policy.readAt_correct values (fun e => fresh e) _ i s (fun e => by simp only [fresh_correct]),
    address0_correct, Storage.TwoPort.reads0]

theorem taken_correct (i : Machine.Inputs) (s : State) :
    Policy.values3 values successor word0 taken i s .wire =
      Dispatch.candidate (FetchPolicy.feed Storage.TwoPort.policy (adapt i s.backend) s.reference)
        s.reference.machine.core true := by
  simp only [Policy.values3, WithWire.values, taken, fresh_correct, sched_correct,
    Dispatch.candidateExpr_correct]

def regNext : {w : Nat} → Reg w → Expr W3 Register w
  | _, .fetched true => Policy.readAt Policy.leaf (.input .wire)
  | _, .fetched false => .input (.input .wire)
  | _, .startWord => .mux (Policy.leaf Policy.commit) (.input (.input .wire)) (.reg (.extra .startWord))

theorem regNext_correct (i : Machine.Inputs) (s : State) {w : Nat} (x : Reg w) :
    (regNext x).eval (Policy.values3 values successor word0 taken i s) (s.values values) =
      values (Policy.next Storage.TwoPort.policy i s).policy x := by
  have hnext : (Policy.next Storage.TwoPort.policy i s).policy =
      (Storage.TwoPort.next (adapt i s.backend) s.reference).policy := rfl
  cases x with
  | fetched b =>
    show _ = (Policy.next Storage.TwoPort.policy i s).policy.fetched b
    rw [hnext, Storage.TwoPort.next_fetched]
    cases b
    · simp only [regNext, Expr.eval, word0_correct]
      rfl
    · simp only [regNext]
      rw [Policy.readAt_correct values Policy.leaf _ i s
        (fun e => Policy.leaf_correct values successor word0 taken e i s)]
      simp only [Expr.eval, taken_correct]
      rfl
  | startWord =>
    show _ = (Policy.next Storage.TwoPort.policy i s).policy.startWord
    rw [hnext, Storage.TwoPort.next_startWord]
    simp only [regNext, Expr.eval, Policy.leaf_correct, Policy.commit_correct, word0_correct]
    simp only [Policy.State.values, Extended.values, values]
    cases Machine.committing (adapt i s.backend) s.reference.machine <;> first | rfl | simp <;> rfl

def realization : Policy.Realization Storage.TwoPort.policy Reg :=
  Policy.Realization.twoWires values successor word0 taken regNext successor_correct regNext_correct

def netlist : Netlist Register Machine.Output Machine.Input := realization.netlist

def rules : Policy.Rules Storage.TwoPort.correct :=
  Policy.Rules.none Storage.TwoPort.correct (fun _ => trivial)

def Valid (s : State) : Prop := Policy.Valid Storage.TwoPort.correct s

def component : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  Policy.component realization

def completeRefinement : Timed.RuleRefinement component referenceComponent rules.Rule :=
  Policy.completeRefinement realization Storage.TwoPort.correct rules

/-- The emitted netlist's every pre/post-edge observation is the reference machine's. -/
theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    component.trace (s.values values) inputs = referenceComponent.trace s.reference.machine inputs :=
  Policy.trace_correct realization Storage.TwoPort.correct rules s h inputs (fun _ _ => trivial)

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    component.trace (netlist.step i.values (s.values values)) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs :=
  Policy.initialized_trace realization Storage.TwoPort.correct rules s i hi inputs (fun _ _ => trivial)

end Pinwheel.Hardware.Storage.Backend.TwoPort
