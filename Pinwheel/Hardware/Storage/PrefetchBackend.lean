import Pinwheel.Hardware.Storage.Decoupled
import Pinwheel.Hardware.Storage.PolicyBackend

/-! The decoupled (three-port) fetch organization as a structural netlist on
the selected general backend (`Backend.Policy`): two fetched-word registers and
a start-word register in place of the same-edge successor lookup. Shared wires:
the successor fed to the scheduler (a fetched word chosen by the branch bit
while running, the start word at rest) and the two candidate addresses of the
next edge, computed from this edge's dispatch decision; each dictionary read is
addressed by a wire, and the start word reads word 0 on a commit — three read
trees. This file is the policy's structural part only. -/
namespace Pinwheel.Hardware.Storage.Backend.Prefetch
open Loader

/-- The policy's registers. -/
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
abbrev W2 := Policy.W2 8
abbrev W3 := Policy.W3 8 8

/-! ### Level 0: the successor fed to the scheduler -/

def successor : E 64 :=
  .mux Policy.running
    (.mux Policy.branch (.reg (.extra (.fetched true))) (.reg (.extra (.fetched false))))
    (.reg (.extra .startWord))

theorem successor_correct (i : Machine.Inputs) (s : State) :
    successor.eval i.values (s.values values) = Policy.fedWord Decoupled.policy i s := by
  simp only [successor, Expr.eval, Policy.running_correct, Policy.branch_correct]
  simp only [Policy.State.values, Extended.values, values]
  show _ = (if Reactive.runningValue s.reference.machine.core
    then s.policy.fetched (FetchPolicy.branch (adapt i s.backend) s.reference) else s.policy.startWord)
  cases Reactive.runningValue s.reference.machine.core <;>
    cases FetchPolicy.branch (adapt i s.backend) s.reference <;> simp

/-! ### Levels 1 and 2: the candidate wires -/

def taken : Expr W1 Register 8 := Policy.sched (Dispatch.candidateExpr true)

def untaken : Expr W2 Register 8 := fresh (Policy.sched (Dispatch.candidateExpr false))

theorem sched_correct (e : Reactive.E w) (i : Machine.Inputs) (s : State) :
    (Policy.sched e).eval (WithWire.values i.values (successor.eval i.values (s.values values)))
        (s.values values) =
      e.eval (FetchPolicy.feed Decoupled.policy (adapt i s.backend) s.reference).values
        s.reference.machine.core.values := by
  rw [Policy.sched_correct, successor_correct, Policy.fedInputs_feed]

theorem taken_correct (i : Machine.Inputs) (s : State) :
    Policy.values3 values successor taken untaken i s (.input .wire) =
      Dispatch.candidate (FetchPolicy.feed Decoupled.policy (adapt i s.backend) s.reference)
        s.reference.machine.core true := by
  simp only [Policy.values3, WithWire.values, taken, sched_correct, Dispatch.candidateExpr_correct]

theorem untaken_correct (i : Machine.Inputs) (s : State) :
    Policy.values3 values successor taken untaken i s .wire =
      Dispatch.candidate (FetchPolicy.feed Decoupled.policy (adapt i s.backend) s.reference)
        s.reference.machine.core false := by
  simp only [Policy.values3, WithWire.values, untaken, fresh_correct, sched_correct,
    Dispatch.candidateExpr_correct]

/-! ### Level 3: the policy's registers -/

/-- The selected bank's composite read, at a wire-supplied or literal address. -/
def read3 (address : Expr W3 Register 8) : Expr W3 Register 64 := Policy.readAt Policy.leaf address

def regNext : {w : Nat} → Reg w → Expr W3 Register w
  | _, .fetched true => read3 (.input (.input .wire))
  | _, .fetched false => read3 (.input .wire)
  | _, .startWord => .mux (Policy.leaf Policy.commit) (read3 (.lit 0)) (.reg (.extra .startWord))

theorem read3_correct (i : Machine.Inputs) (s : State) (a : Expr W3 Register 8) :
    (read3 a).eval (Policy.values3 values successor taken untaken i s) (s.values values) =
      Loader.Store.read (s.reference.machine.memory (Machine.selected (adapt i s.backend) s.reference.machine))
        (a.eval (Policy.values3 values successor taken untaken i s) (s.values values)) :=
  Policy.readAt_correct values Policy.leaf _ i s
    (fun e => Policy.leaf_correct values successor taken untaken e i s) a

theorem regNext_correct (i : Machine.Inputs) (s : State) {w : Nat} (x : Reg w) :
    (regNext x).eval (Policy.values3 values successor taken untaken i s) (s.values values) =
      values (Policy.next Decoupled.policy i s).policy x := by
  have hnext : (Policy.next Decoupled.policy i s).policy =
      (Decoupled.next (adapt i s.backend) s.reference).policy := rfl
  cases x with
  | fetched b =>
    show _ = (Policy.next Decoupled.policy i s).policy.fetched b
    rw [hnext, Decoupled.next_fetched]
    cases b <;> simp only [regNext, read3_correct, Expr.eval, taken_correct, untaken_correct]
  | startWord =>
    show _ = (Policy.next Decoupled.policy i s).policy.startWord
    rw [hnext, Decoupled.next_startWord]
    simp only [regNext, Expr.eval, Policy.leaf_correct, Policy.commit_correct, read3_correct]
    simp only [Policy.State.values, Extended.values, values]
    cases Machine.committing (adapt i s.backend) s.reference.machine <;> first | rfl | simp <;> rfl

/-! ### The backend -/

def realization : Policy.Realization Decoupled.policy Reg :=
  Policy.Realization.twoWires values successor taken untaken regNext successor_correct regNext_correct

def netlist : Netlist Register Machine.Output Machine.Input := realization.netlist

/-- No rule: the refinement holds on every input history. -/
def rules : Policy.Rules Decoupled.correct := Policy.Rules.none Decoupled.correct (fun _ => trivial)

def Valid (s : State) : Prop := Policy.Valid Decoupled.correct s

def component : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  Policy.component realization

def completeRefinement : Timed.RuleRefinement component referenceComponent rules.Rule :=
  Policy.completeRefinement realization Decoupled.correct rules

theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    component.trace (s.values values) inputs = referenceComponent.trace s.reference.machine inputs :=
  Policy.trace_correct realization Decoupled.correct rules s h inputs (fun _ _ => trivial)

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    component.trace (netlist.step i.values (s.values values)) inputs =
      referenceComponent.trace (Machine.next (capacityInput i s.reference.machine) s.reference.machine) inputs :=
  Policy.initialized_trace realization Decoupled.correct rules s i hi inputs (fun _ _ => trivial)

end Pinwheel.Hardware.Storage.Backend.Prefetch
