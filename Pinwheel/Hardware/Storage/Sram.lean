import Pinwheel.Hardware.Storage.TwoPort

/-! Synchronous response ownership for the hybrid SRAM candidate.

The macro holds Q during a write. A commit reads the new bank's first word;
on the next edge Q bypasses the saved start word, and is saved for subsequent
starts while the inactive bank is being written. This model refines the atomic
machine using the existing two-port invariant. `SramExecution` composes this
response contract with initialized array contents and the shared controller.
The external macro binding and emitted-chip read-back remain separate.
-/
namespace Pinwheel.Hardware.Storage.Sram
open Loader

structure Responses where
  q : Bool → BitVec 64
  startWord : BitVec 64
  pending : Bool

def Responses.start (r : Responses) : BitVec 64 :=
  if r.pending then r.q false else r.startWord

def Responses.view (r : Responses) : Decoupled.Registers := ⟨r.q, r.start⟩

/-- The same bypass expression serves the current start input and the next
saved-start register in the experimental emitter. -/
def startExpr (pending : Expr I R 1) (q saved : Expr I R 64) : Expr I R 64 :=
  .mux pending q saved

def successorExpr (running branch : Expr I R 1) (q : Bool → Expr I R 64)
    (start : Expr I R 64) : Expr I R 64 :=
  .mux running (.mux branch (q true) (q false)) start

theorem startExpr_correct (pending : Expr I R 1) (q saved : Expr I R 64)
    (i : Values I) (s : Values R) (r : Responses)
    (hp : pending.eval i s = BitVec.ofBool r.pending)
    (hq : q.eval i s = r.q false) (hs : saved.eval i s = r.startWord) :
    (startExpr pending q saved).eval i s = r.start := by
  cases hr : r.pending <;> simp [startExpr, Expr.eval, hp, hq, hs, Responses.start, hr]

def Responses.step (r : Responses) (commit read : Bool) (words : Bool → BitVec 64) : Responses :=
  ⟨if read then words else r.q, r.start, commit⟩

/-- The retained/bypassed start word follows the two-port start register even
when unrelated writes disable the SRAM read ports. -/
theorem start_step (r : Responses) (commit read : Bool) (words : Bool → BitVec 64)
    (hc : commit = true → read = true) :
    (r.step commit read words).start = if commit then words false else r.start := by
  cases commit
  all_goals simp_all [Responses.step, Responses.start]

structure State where
  machine : Machine.State
  current : BitVec 64
  responses : Responses

def State.view (s : State) : TwoPort.State :=
  ⟨s.machine, s.current, s.responses.view⟩

/-- Only accepted dictionary writes occupy the hybrid macros. Index/metadata
writes do not prevent reads. Admission is upstream of these machine inputs. -/
def writing (i : Machine.Inputs) (s : Machine.State) : Bool :=
  Loader.push (Machine.controlInput i s) s.control && s.control.cursor.toNat < 32

def next (i : Machine.Inputs) (s : State) : State :=
  let n := TwoPort.next i s.view
  ⟨n.machine, n.current,
    s.responses.step (Machine.committing i s.machine) (!(writing i s.machine)) n.policy.fetched⟩

def Valid (s : State) : Prop := FetchPolicy.Valid TwoPort.correct s.view

theorem writing_no_commit (i : Machine.Inputs) (s : Machine.State)
    (hw : writing i s = true) : Machine.committing i s = false := by
  simp_all [writing, Machine.committing, Loader.commit, Loader.push]

theorem commit_reads (i : Machine.Inputs) (s : Machine.State)
    (hc : Machine.committing i s = true) : Bool.not (writing i s) = true := by
  simp_all [writing, Machine.committing, Loader.commit, Loader.push]

theorem start_next (i : Machine.Inputs) (s : State) :
    (next i s).view.policy.startWord = (TwoPort.next i s.view).policy.startWord := by
  exact start_step s.responses _ _ _ (commit_reads i s.machine)

theorem writing_stops (i : Machine.Inputs) (s : Machine.State)
    (hw : writing i s = true) : Reactive.runningValue (Machine.next i s).core = false := by
  have hb : Reactive.runningValue s.core = false := by
    simp_all [writing, Loader.push, Loader.enabled, Machine.controlInput]
  have hs : (Machine.schedulerInput i s).start = false := by
    simp_all [writing, Loader.push, Machine.controlInput, Machine.schedulerInput,
      Reactive.Fetch.resolve, Machine.baseInput, Loader.start]
  simp only [Machine.next, Reactive.stepValue, hb, hs, Bool.false_eq_true, ite_false]
  split <;> simp_all [Reactive.stopValue, Reactive.runningValue]

theorem machine_next (i : Machine.Inputs) (s : State) (h : Valid s) :
    (next i s).machine = Machine.next i s.machine :=
  FetchPolicy.machine_next TwoPort.correct i s.view h

theorem valid_next (i : Machine.Inputs) (s : State) (h : Valid s) : Valid (next i s) := by
  have hn := FetchPolicy.valid_next TwoPort.correct i s.view h trivial
  refine ⟨hn.1, ?_⟩
  intro hv
  refine ⟨?_, (start_next i s).trans (hn.2 hv).2⟩
  intro hb b
  cases hw : writing i s.machine
  case true =>
    simp only [State.view, machine_next i s h, writing_stops i s.machine hw,
      Bool.false_eq_true] at hb
  case false =>
    simpa only [next, State.view, Responses.view, Responses.step, hw, Bool.not_false,
      ite_true, TwoPort.next] using (hn.2 hv).1 hb b

theorem initialize_machine_next (i : Machine.Inputs) (s : State) (hi : i.init = true) :
    (next i s).machine = Machine.next i s.machine :=
  FetchPolicy.initialize_machine_next i s.view hi

theorem initialize_valid (i : Machine.Inputs) (s : State) (hi : i.init = true) :
    Valid (next i s) := by
  refine ⟨(FetchPolicy.initialize_valid TwoPort.correct i s.view hi).1, ?_⟩
  intro hv
  simp only [State.view, initialize_machine_next i s hi,
    (Machine.initialize_safe i s.machine hi).1, Bool.false_eq_true] at hv

def component : Timed.Component Machine.Inputs State (Values Machine.Output) :=
  ⟨next, fun i s => Cache.circuit.observe i.values s.view.cache.values⟩

/-- Response holding and the delayed start save preserve every reference edge,
without a minimum-duration admission restriction. -/
def refinement : Timed.Refinement component Cache.referenceComponent where
  Rel := fun s t => Valid s ∧ s.machine = t
  step := fun i s t h => ⟨valid_next i s h.1,
    (machine_next i s h.1).trans (congrArg (Machine.next i) h.2)⟩
  observe := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact funext fun w => funext fun o => Cache.output_correct i s.view.cache hv.1 o

theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    component.trace s inputs = Cache.referenceComponent.trace s.machine inputs :=
  refinement.trace_eq s s.machine ⟨h, rfl⟩ inputs

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    component.trace (next i s) inputs =
      Cache.referenceComponent.trace (Machine.next i s.machine) inputs := by
  rw [← initialize_machine_next i s hi]
  exact trace_correct (next i s) (initialize_valid i s hi) inputs

end Pinwheel.Hardware.Storage.Sram
