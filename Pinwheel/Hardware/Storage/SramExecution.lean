import Pinwheel.Hardware.Storage.SramContents

/-! Closed-loop execution of the shared hybrid controller and replicated SRAM
arrays. Read responses come from the arrays; correctness is established by an
invariant connecting their initialized contents to the existing loader image.
The external Verilog macro binding and emitted-chip read-back are separate. -/
namespace Pinwheel.Hardware.Storage.SramExecution
open Pinwheel.Hardware Loader

/-- The backend image is retained as specification bookkeeping. Execution's
successor comes exclusively from array Q or the saved start word. `core_step`
checks the register transition against the shared controller netlist. -/
structure State where
  backend : Backend.State
  extra : Values SramController.Extra
  arrays : Fin 2 → Memory.Sram.State 6 64

def State.q (s : State) (b : Bool) : BitVec 64 := (s.arrays (if b then 1 else 0)).q
def State.inputs (s : State) (i : Machine.Inputs) : Values SramController.Input :=
  SramController.inputValues i s.q
def State.values (s : State) : Values SramController.Register :=
  SramController.registerValues s.backend s.extra
def State.responses (s : State) : Sram.Responses :=
  ⟨s.q, s.extra .startWord, s.extra .startPending == 1⟩
def State.view (s : State) : Sram.State :=
  ⟨s.backend.reference.machine, s.backend.current, s.responses⟩
def State.policy (s : State) : Backend.Policy.State Decoupled.Registers :=
  ⟨s.backend, s.responses.view⟩
def request (i : Machine.Inputs) (s : State) : Memory.Request 6 64 2 :=
  SramController.hybridRequest (s.inputs i) s.values

def next (i : Machine.Inputs) (s : State) : State :=
  ⟨Backend.Policy.fedNext (SramController.successor.eval (s.inputs i) s.values) i s.backend,
    fun r => (SramController.core false).step (s.inputs i) s.values (.extra r),
    Memory.Sram.step (request i s) s.arrays⟩

def Valid (s : State) : Prop :=
  ∃ t, SramCoverage.Covered s.backend.control t ∧
    SramContents.Agrees s.backend.reference.machine.memory t ∧
    Memory.Sram.Related s.arrays t ∧ Sram.Valid s.view

private theorem inject_eval (e : Expr Machine.Input SramController.Register w)
    (i : Machine.Inputs) (s : State) :
    (SramController.inject e).eval (s.inputs i) s.values = e.eval i.values s.values := by
  simp only [SramController.inject, Expr.eval_bind, Expr.eval, State.inputs, SramController.inputValues]
  done

theorem successor_word (i : Machine.Inputs) (s : State) :
    SramController.successor.eval (s.inputs i) s.values =
      Backend.Policy.fedWord TwoPort.policy i s.policy := by
  simp only [SramController.successor, Sram.successorExpr, Sram.startExpr, Expr.eval, inject_eval]
  change (if Backend.Policy.running.eval i.values
      ((⟨s.backend, s.extra⟩ : Backend.Policy.State (Values SramController.Extra)).values (fun x => x)) = 1 then
    (if Backend.Policy.branch.eval i.values
      ((⟨s.backend, s.extra⟩ : Backend.Policy.State (Values SramController.Extra)).values (fun x => x)) = 1
      then s.q true else s.q false)
    else if s.extra .startPending = 1 then s.q false else s.extra .startWord) = _
  simp only [Backend.Policy.running_correct (fun x : Values SramController.Extra => x) i ⟨s.backend, s.extra⟩,
    Backend.Policy.branch_correct (fun x : Values SramController.Extra => x) i ⟨s.backend, s.extra⟩]
  simp [Backend.Policy.fedWord, FetchPolicy.feed, TwoPort.policy, Decoupled.fed,
    Backend.Policy.State.reference, State.policy, State.responses, Sram.Responses.view,
    Sram.Responses.start, FetchPolicy.branch, FetchPolicy.State.cache]
  cases Reactive.Fetch.branchBit ⟨Cache.base (Backend.adapt i s.backend)
    ⟨s.backend.reference.machine, s.backend.current⟩,
    s.backend.reference.machine.core⟩ <;> rfl
  done

theorem backend_next (i : Machine.Inputs) (s : State) :
    (next i s).backend = (Backend.Policy.next TwoPort.policy i s.policy).backend := by
  simp only [next, successor_word, Backend.Policy.next_backend]
  rfl
  done

theorem sched_correct (e : Reactive.E w) (i : Machine.Inputs) (s : State) :
    (SramController.sched e).eval
        (WithWire.values (s.inputs i) (SramController.successor.eval (s.inputs i) s.values)) s.values =
      e.eval (FetchPolicy.feed TwoPort.policy (Backend.adapt i s.backend) s.policy.reference).values
        s.backend.reference.machine.core.values := by
  simp only [SramController.sched, State.inputs, State.values, SramController.liftW_eval,
    Backend.Policy.schedW_correct]
  exact congrArg (fun x => e.eval (Backend.Policy.fedInputs x i s.backend).values
    s.backend.reference.machine.core.values) (successor_word i s)
  done

theorem commit_correct (i : Machine.Inputs) (s : State) :
    SramController.commit.eval (s.inputs i) s.values =
      BitVec.ofBool (Machine.committing (Backend.adapt i s.backend) s.backend.reference.machine) := by
  change Backend.Policy.commit.eval i.values
    ((⟨s.backend, s.extra⟩ : Backend.Policy.State (Values SramController.Extra)).values (fun x => x)) = _
  exact Backend.Policy.commit_correct (fun x : Values SramController.Extra => x) i ⟨s.backend, s.extra⟩
  done

theorem address0_correct (i : Machine.Inputs) (s : State) :
    SramController.address0.eval
        (WithWire.values (s.inputs i) (SramController.successor.eval (s.inputs i) s.values)) s.values =
      TwoPort.address0 (Backend.adapt i s.backend) s.policy.reference := by
  simp only [SramController.address0, Expr.eval, sched_correct, Dispatch.dispatching_correct,
    Dispatch.enteredExpr_correct, Dispatch.heldExpr_correct, Backend.fresh_correct,
    commit_correct, Reactive.bool_one]
  unfold TwoPort.address0
  rw [Dispatch.candidate_split]
  cases hd : Dispatch.dispatching (FetchPolicy.feed TwoPort.policy (Backend.adapt i s.backend) s.policy.reference)
      s.backend.reference.machine.core
  case true =>
    have hc := FetchPolicy.dispatch_no_commit (P := TwoPort.policy)
      (Backend.adapt i s.backend) s.policy.reference hd
    simp_all [State.policy, Backend.Policy.State.reference]
    done
  case false =>
    simp_all [State.policy, Backend.Policy.State.reference]
  done

theorem read_word (i : Machine.Inputs) (s : State) (t : SramCoverage.Model)
    (ha : SramContents.Agrees s.backend.reference.machine.memory t)
    (hc : SramCoverage.Covered s.backend.control t) (hr : Memory.Sram.Related s.arrays t)
    (hv : s.backend.control.valid = true ∨
      Machine.committing (Backend.adapt i s.backend) s.backend.reference.machine = true)
    (hw : (request i s).write.enable = false) (b : Bool) :
    (next i s).q b = (TwoPort.next (Backend.adapt i s.backend) s.policy.reference).policy.fetched b := by
  have h := SramContents.physical_read_word i s.backend s.q s.extra t s.arrays ha hc hr hv hw
    (if b then 1 else 0)
  refine h.trans ?_
  cases b <;> simp only [TwoPort.next_fetched, TwoPort.reads0, SramContents.address,
    Bool.false_eq_true, ite_false, ite_true]
  all_goals apply congrArg (Loader.Store.read
    (s.backend.reference.machine.memory (Machine.selected (Backend.adapt i s.backend) s.backend.reference.machine)))
  case false => exact address0_correct i s
  case true =>
    exact (sched_correct (Dispatch.candidateExpr true) i s).trans (Dispatch.candidateExpr_correct _ _ true)
  done

theorem pending_next (i : Machine.Inputs) (s : State) :
    (next i s).extra .startPending =
      BitVec.ofBool (Machine.committing (Backend.adapt i s.backend) s.backend.reference.machine) := by
  exact commit_correct i s
  done

theorem start_next (i : Machine.Inputs) (s : State) :
    (next i s).extra .startWord = s.responses.start := by
  simp [next, SramController.core, Netlist.step, Circuit.step, SramController.body,
    Sram.startExpr, Expr.eval, WithWire.values, State.inputs, SramController.inputValues,
    State.values, SramController.registerValues, State.responses, Sram.Responses.start]
  rfl
  done

theorem q_next (i : Machine.Inputs) (s : State) (t : SramCoverage.Model)
    (ha : SramContents.Agrees s.backend.reference.machine.memory t)
    (hc : SramCoverage.Covered s.backend.control t) (hr : Memory.Sram.Related s.arrays t)
    (hv : s.backend.control.valid = true ∨
      Machine.committing (Backend.adapt i s.backend) s.backend.reference.machine = true) :
    (next i s).q = if (request i s).write.enable then s.q
      else (TwoPort.next (Backend.adapt i s.backend) s.policy.reference).policy.fetched := by
  funext b
  cases hw : (request i s).write.enable
  case true => simp [next, State.q, Memory.Sram.step, Memory.Sram.State.step, hw]
  case false => simpa only [Bool.false_eq_true, ite_false] using read_word i s t ha hc hr hv hw b
  done

theorem cache_next (i : Machine.Inputs) (s : State) :
    (next i s).view.view.cache = (Sram.next (Backend.adapt i s.backend) s.view).view.cache := by
  change (next i s).backend.reference = (TwoPort.next (Backend.adapt i s.backend) s.policy.reference).cache
  rw [backend_next]
  exact congrArg FetchPolicy.State.cache (Backend.Policy.reference_next TwoPort.policy i s.policy)
  done

theorem responses_next (i : Machine.Inputs) (s : State) (t : SramCoverage.Model)
    (ha : SramContents.Agrees s.backend.reference.machine.memory t)
    (hc : SramCoverage.Covered s.backend.control t) (hr : Memory.Sram.Related s.arrays t)
    (hv : s.backend.control.valid = true ∨
      Machine.committing (Backend.adapt i s.backend) s.backend.reference.machine = true) :
    (next i s).responses = (Sram.next (Backend.adapt i s.backend) s.view).responses := by
  change (⟨(next i s).q, (next i s).extra .startWord,
    (next i s).extra .startPending == 1⟩ : Sram.Responses) = _
  rw [q_next i s t ha hc hr hv, start_next, pending_next]
  simp only [request, State.inputs, State.values, SramController.hybrid_request_enable,
    Sram.next, Sram.Responses.step, State.view]
  simp [Sram.State.view, State.policy, Backend.Policy.State.reference, State.responses]
  cases Sram.writing (Backend.adapt i s.backend) s.backend.reference.machine <;>
    cases Machine.committing (Backend.adapt i s.backend) s.backend.reference.machine <;> simp
  done

theorem view_next (i : Machine.Inputs) (s : State) (t : SramCoverage.Model)
    (ha : SramContents.Agrees s.backend.reference.machine.memory t)
    (hc : SramCoverage.Covered s.backend.control t) (hr : Memory.Sram.Related s.arrays t)
    (hv : s.backend.control.valid = true ∨
      Machine.committing (Backend.adapt i s.backend) s.backend.reference.machine = true) :
    (next i s).view = Sram.next (Backend.adapt i s.backend) s.view := by
  exact congr (congrArg (fun (c : Cache.State) (r : Sram.Responses) => (⟨c.machine, c.current, r⟩ : Sram.State))
    (cache_next i s)) (responses_next i s t ha hc hr hv)
  done

theorem control_next (i : Machine.Inputs) (s : State) :
    (next i s).backend.control =
      Loader.next (Machine.controlInput (Backend.adapt i s.backend) s.backend.reference.machine) s.backend.control := by
  rfl
  done

private theorem valid_source (i : Loader.Inputs) (c : Loader.State)
    (hv : (Loader.next i c).valid = true) : c.valid = true ∨ Loader.commit i c = true := by
  cases hi : i.init
  case true => simp [Loader.next, hi] at hv
  case false =>
    cases hc : Loader.commit i c
    case true => exact Or.inr rfl
    case false => exact Or.inl ((Loader.no_commit_preserves_selection i c hi hc).2.symm.trans hv)
    done
  done

theorem model_valid_next (i : Machine.Inputs) (s : State) (t : SramCoverage.Model)
    (ha : SramContents.Agrees s.backend.reference.machine.memory t)
    (hc : SramCoverage.Covered s.backend.control t) (hr : Memory.Sram.Related s.arrays t)
    (h : Sram.Valid s.view) : Sram.Valid (next i s).view := by
  by_cases hv : (next i s).backend.control.valid = true
  · have hs := valid_source (Machine.controlInput (Backend.adapt i s.backend) s.backend.reference.machine)
      s.backend.control hv
    rw [view_next i s t ha hc hr hs]
    exact Sram.valid_next (Backend.adapt i s.backend) s.view h
    done
  · refine ⟨?_, fun hbad => (hv hbad).elim⟩
    rw [cache_next]
    exact (Sram.valid_next (Backend.adapt i s.backend) s.view h).1
    done
  done

theorem valid_next (i : Machine.Inputs) (s : State) (h : Valid s) : Valid (next i s) := by
  rcases h with ⟨t, hc, ha, hr, hv⟩
  exact ⟨t.step (request i s),
    SramCoverage.controller_covered_next i s.backend s.q s.extra t hc,
    SramContents.controller_agrees_next i s.backend s.q s.extra t ha _,
    Memory.Sram.related_step (request i s) s.arrays t hr,
    model_valid_next i s t ha hc hr hv⟩
  done

theorem initialize_control (i : Machine.Inputs) (s : State) (hi : i.init = true) :
    (next i s).backend.control = {} := by
  rw [control_next]
  simp only [Loader.next, show (Machine.controlInput (Backend.adapt i s.backend)
    s.backend.reference.machine).init = true from hi, ite_true]
  done

theorem initialize_valid (i : Machine.Inputs) (s : State) (hi : i.init = true) : Valid (next i s) := by
  refine ⟨Memory.Sram.Model.initial, ?_, SramContents.agrees_initial _, Memory.Sram.related_initial _, ?_⟩
  · rw [initialize_control i s hi]
    exact SramCoverage.covered_initial _
    done
  · refine ⟨?_, ?_⟩
    · rw [cache_next]
      exact (Sram.initialize_valid (Backend.adapt i s.backend) s.view hi).1
      done
    · intro hv
      change (next i s).backend.control.valid = true at hv
      simp [initialize_control i s hi] at hv
      done
    done
  done

/-- Every controller register follows the shared emitted netlist; array state
is advanced by its actual request ports in `next`. -/
theorem core_step (i : Machine.Inputs) (s : State) (r : SramController.Register w) :
    (SramController.core false).step (s.inputs i) s.values r = (next i s).values r := by
  cases r
  case extra r => rfl
  case inner r =>
    simp only [SramController.core, Netlist.step, Circuit.step, SramController.body,
      State.inputs, State.values, SramController.liftW_eval, SramController.registerValues]
    exact Backend.Policy.core_step _ i s.backend r
    done
  done

theorem machine_next (i : Machine.Inputs) (s : State) (h : Valid s) :
    (next i s).backend.reference.machine =
      Machine.next (Backend.capacityInput i s.backend.reference.machine) s.backend.reference.machine := by
  exact (congrArg Cache.State.machine (cache_next i s)).trans
    (Sram.machine_next (Backend.adapt i s.backend) s.view h.choose_spec.2.2.2)
  done

theorem initialize_machine_next (i : Machine.Inputs) (s : State) (hi : i.init = true) :
    (next i s).backend.reference.machine =
      Machine.next (Backend.capacityInput i s.backend.reference.machine) s.backend.reference.machine := by
  exact (congrArg Cache.State.machine (cache_next i s)).trans
    (Sram.initialize_machine_next (Backend.adapt i s.backend) s.view hi)
  done

theorem output_correct (i : Machine.Inputs) (s : State) (h : Valid s) (o : Machine.Output w) :
    (SramController.core false).observe (s.inputs i) s.values (.base o) =
      Machine.circuit.observe (Backend.capacityInput i s.backend.reference.machine).values
        s.backend.reference.machine.values o := by
  simp only [SramController.core, Netlist.observe, Circuit.observe, SramController.body,
    State.inputs, State.values, SramController.liftW_eval]
  exact (Backend.Policy.core_observe _ i s.backend o).trans
    (Backend.output_correct i s.backend h.choose_spec.2.2.2.1 o)
  done

def component : Timed.Component Machine.Inputs State (Values Machine.Output) :=
  ⟨next, fun i s {w} (o : Machine.Output w) => (SramController.core false).observe (s.inputs i) s.values (.base o)⟩

/-- Closed-loop array execution preserves the existing capacity-adapted
machine edge for edge. No new program-duration or UART admission rule is used. -/
def refinement : Timed.Refinement component Backend.referenceComponent where
  Rel := fun s t => Valid s ∧ s.backend.reference.machine = t
  step := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact ⟨valid_next i s hv, machine_next i s hv⟩
    done
  observe := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact funext fun w => funext fun o => output_correct i s hv o
    done

theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    component.trace s inputs = Backend.referenceComponent.trace s.backend.reference.machine inputs :=
  refinement.trace_eq s s.backend.reference.machine ⟨h, rfl⟩ inputs

/-- A single initializing edge establishes the complete invariant from
arbitrary controller registers, array contents, and held responses. -/
theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    component.trace (next i s) inputs =
      Backend.referenceComponent.trace
        (Machine.next (Backend.capacityInput i s.backend.reference.machine) s.backend.reference.machine) inputs := by
  rw [← initialize_machine_next i s hi]
  exact trace_correct (next i s) (initialize_valid i s hi) inputs
  done

end Pinwheel.Hardware.Storage.SramExecution
