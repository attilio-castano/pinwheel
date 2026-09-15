import Pinwheel.Hardware.Storage.CacheCircuit
import Pinwheel.Hardware.Timed

namespace Pinwheel.Hardware.Storage.Cache
open Loader

/-- Reference and cached components expose every existing output, including
combinational loader responses and diagnostic read addresses. -/
def referenceComponent : Timed.Component Machine.Inputs Machine.State (Values Machine.Output) :=
  ⟨Machine.next, fun i s => Machine.circuit.observe i.values s.values⟩

def component : Timed.Component Machine.Inputs State (Values Machine.Output) :=
  ⟨next, fun i s => circuit.observe i.values s.values⟩

theorem output_correct (i : Machine.Inputs) (s : State) (h : Valid s) (o : Machine.Output w) :
    circuit.observe i.values s.values o = Machine.circuit.observe i.values s.machine.values o := by
  cases o
  all_goals simp only [Circuit.observe, circuit, lift_correct, Machine.circuit, Expr.eval_bind,
    feed_correct_circuit, Machine.scheduler_correct]
  rename_i p
  cases p
  all_goals simp only [Reactive.circuit, coreReg, lift, Expr.eval, State.values,
    Machine.coreReg, Machine.State.values, Reactive.target_correct]
  all_goals simp only [Reactive.running_correct, feed_correct i s h]
  by_cases hb : Reactive.runningValue s.machine.core = true
  · simp [Machine.schedulerInput, Machine.baseInput, busy_selection i s.machine hb, h hb]
  · exact idle_target _ _ (by simpa using hb) _
  done

/-- Initialization establishes the cache invariant even from arbitrary cache bits
and memory contents. No initialized-memory premise is needed. -/
theorem initialize_valid (i : Machine.Inputs) (s : State) (hi : i.init = true) :
    Valid (next i s) := by
  simp [Valid, Reactive.Fetch.CurrentValid, next, feed, base, Machine.baseInput,
    Reactive.stepValue, Reactive.stopValue, Reactive.runningValue, hi]
  done

theorem initialize_machine_next (i : Machine.Inputs) (s : State) (hi : i.init = true) :
    (next i s).machine = Machine.next i s.machine := by
  simp [next, Machine.next, feed, base, Machine.schedulerInput, Machine.baseInput,
    Reactive.stepValue, Reactive.stopValue, hi]
  done

/-- Replacement preserves state and every output on the same clock edge. -/
def refinement : Timed.Refinement component referenceComponent where
  Rel := fun s t => Valid s ∧ s.machine = t
  step := fun i s t h => ⟨valid_next i s h.1,
    (machine_next i s h.1).trans (congrArg (Machine.next i) h.2)⟩
  observe := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact funext fun w => funext fun o => output_correct i s hv o
    done

theorem edge_correct (i : Machine.Inputs) (s : State) (h : Valid s) :
    component.edge i s = referenceComponent.edge i s.machine :=
  refinement.edge_eq s s.machine ⟨h, rfl⟩ i

theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    component.trace s inputs = referenceComponent.trace s.machine inputs :=
  refinement.trace_eq s s.machine ⟨h, rfl⟩ inputs

/-- Execute the structural circuit directly, using its register valuation. -/
def structuralComponent : Timed.Component Machine.Inputs (Values Register) (Values Machine.Output) :=
  ⟨fun i r => circuit.step i.values r, fun i r => circuit.observe i.values r⟩

def structuralRefinement : Timed.Refinement structuralComponent component where
  Rel := fun r s => @r = @State.values s
  step := fun i r s h => by
    subst r
    exact funext fun w => funext fun p => next_correct i s p
  observe := fun _ _ _ h => congrArg _ h

/-- Compose the structural interpretation proof with the cache replacement proof. -/
def completeRefinement : Timed.Refinement structuralComponent referenceComponent :=
  structuralRefinement.trans refinement

theorem structural_trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    structuralComponent.trace s.values inputs = referenceComponent.trace s.machine inputs :=
  completeRefinement.trace_eq s.values s.machine ⟨s, rfl, h, rfl⟩ inputs

end Pinwheel.Hardware.Storage.Cache
