import Pinwheel.Hardware.Storage.PairedPackage

/-! E64 execution through the retained package and result observer.
Loader status and speculative read addresses retain their graph interpretation;
execution state and busy are supplied by the independent instruction model.
The serial-session premise is a digital delivery contract, not an electrical law. -/
namespace Pinwheel.Hardware.Storage.PairedHost
open Pinwheel.Hardware PairedController PairedPackage PairedCertified
open PairedCoverage (Tracked advance graphInputs graph_equations)
open SramController (Out)
set_option backward.isDefEq.respectTransparency false

private theorem bit_get (v : BitVec 1) : BitVec.ofBool v[0] = v := by
  rcases PairedUpload.bit_cases v with h | h <;> simp [h]

def output (s : Tracked) (x : Chip.State) : Values Loader.Machine.Output :=
  fun {_} o => body.observe (graphInputs (decoded x).values s) s.registers (.base o)

/-- The existing loader sideband is explicit; no loader claim is smuggled into E64. -/
def withExecution (o : Values Loader.Machine.Output) (m : Reactive.Model) : Values Loader.Machine.Output
  | _, .core (.state r) => (Reactive.embed m).values r
  | _, .core .busy => BitVec.ofBool (Engine.Reactive.busy m)
  | _, p => o p

structure ReferenceState where
  storage : Tracked
  execution : Reactive.Model
  adapters : Chip.State
  result : HostResult.State

def referenceOutput (s : ReferenceState) : Values Loader.Machine.Output :=
  withExecution (output s.storage s.adapters) s.execution

def reference (p : Execution.Image) : Timed.Component Chip.Pins ReferenceState (Values Chip.Output) where
  step := fun i s => ⟨advance s.storage (decoded s.adapters).values,
    (PairedTimed.reference p).step (decoded s.adapters).values s.execution,
    adaptersNext i s.adapters, HostResult.next i (referenceOutput s) s.result⟩
  observe := fun _ s => HostResult.shown (referenceOutput s) s.result

def Related (p : Execution.Image) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S) (t : ReferenceState) : Prop :=
  PairedCoverage.view memory s.core = t.storage.physical ∧
    PairedTimed.Related p image t.storage t.execution ∧ s.adapters = t.adapters ∧ s.result = t.result

theorem consumed_cons (x : Chip.State) (i : Chip.Pins) (rest : List Chip.Pins) :
    Chip.consumed x (i :: rest) = decoded x :: Chip.consumed (adaptersNext i x) rest := by rfl

theorem output_agrees (p : Execution.Image) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S) (t : ReferenceState)
    (h : Related p image memory s t) :
    (coreOutput memory s : Values Loader.Machine.Output) = (referenceOutput t : Values Loader.Machine.Output) := by
  have ho : (coreOutput memory s : Values Loader.Machine.Output) =
      (output t.storage s.adapters : Values Loader.Machine.Output) :=
    congrArg (fun a : Values Register × Memory.Sram.State 9 64 =>
      ((PairedClosed.model PairedComposition.graph).observe (decoded s.adapters).values a : Values Loader.Machine.Output)) h.1
  rw [ho, h.2.2.1]
  funext w o
  cases o with
  | control r => rfl
  | core o =>
    cases o with
    | readA | readB => rfl
    | busy => exact PairedTimedStep.busy_model _ _ _ (graph_equations (decoded t.adapters).values t.storage) h.2.1.2.2
    | state r =>
      have hv := (PairedTimed.graph_observe _ _ (graph_equations (decoded t.adapters).values t.storage)).trans h.2.1.2.2
      have he := congrArg (fun v : Reactive.State => v.values r) hv
      cases r with
      | sample k =>
        simpa [PairedTimed.observe, Reactive.fromValues, Reactive.State.values,
          output, referenceOutput, withExecution, bit_get] using he
      | _ => exact he
      done

theorem related_next (p : Execution.Image) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S) (t : ReferenceState)
    (h : Related p image memory s t) (i : Chip.Pins) (hi : Rule (decoded t.adapters).values) :
    Related p image memory ((interpreted memory).step i s) ((reference p).step i t) := by
  refine ⟨?_, (PairedTimed.refinement p image).step _ _ _ hi h.2.1,
    congrArg (adaptersNext i) h.2.2.1, ?_⟩
  case refine_1 =>
    simpa only [interpreted, reference, h.2.2.1, PairedTimed.physical_refinement, PairedTimed.tracked, PairedTimed.executable] using
      (PairedTimed.physical_refinement memory).step (decoded t.adapters).values s.core t.storage h.1
  simp only [interpreted, reference, output_agrees p image memory s t h, h.2.2.2]
  done

theorem observe_agrees (p : Execution.Image) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S) (t : ReferenceState)
    (h : Related p image memory s t) (i : Chip.Pins) :
    ((interpreted memory).observe i s : Values Chip.Output) =
      ((reference p).observe i t : Values Chip.Output) := by
  change (HostResult.shown (coreOutput memory s) s.result : Values Chip.Output) =
    (HostResult.shown (referenceOutput t) t.result : Values Chip.Output)
  rw [output_agrees p image memory s t h, h.2.2.2]
  done

theorem interpreted_trace (p : Execution.Image) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S) (t : ReferenceState)
    (h : Related p image memory s t) (pins : List Chip.Pins)
    (hi : ∀ i ∈ Chip.consumed t.adapters pins, Rule i.values) :
    (interpreted memory).trace s pins = (reference p).trace t pins := by
  induction pins generalizing s t with
  | nil => rfl
  | cons i rest ih =>
    have rule := hi (decoded t.adapters) (by rw [consumed_cons]; exact List.mem_cons_self)
    have nextRel := related_next p image memory s t h i rule
    have tailRule : ∀ j ∈ Chip.consumed (adaptersNext i t.adapters) rest, Rule j.values :=
      fun j hj => hi j (by rw [consumed_cons]; exact List.mem_cons_of_mem _ hj)
    simp only [Timed.Component.trace, Timed.Component.edge, observe_agrees p image memory s t h i,
      observe_agrees p image memory _ _ nextRel i, ih _ _ nextRel tailRule]
    done

/-- The package's actual command stream is the existing qualified host stream. -/
def consumed (memory : Memory.SinglePort.Contract S 9 64) :
    PairedPackage.State S → List Chip.Pins → List Loader.Machine.Inputs
  | _, [] => []
  | s, i :: rest => decoded s.adapters :: consumed memory ((interpreted memory).step i s) rest

theorem consumed_eq (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S)
    (pins : List Chip.Pins) : consumed memory s pins = Chip.consumed s.adapters pins := by
  induction pins generalizing s with
  | nil => rfl
  | cons i rest ih => simp only [consumed, consumed_cons, ih]; rfl

theorem run_storage (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S)
    (storage : Tracked) (hs : PairedCoverage.view memory s.core = storage.physical) (pins : List Chip.Pins) :
    PairedCoverage.view memory ((interpreted memory).run s pins).core =
      ((Chip.consumed s.adapters pins).foldl (fun t i => advance t i.values) storage).physical := by
  induction pins generalizing s storage with
  | nil => exact hs
  | cons i rest ih =>
    simpa only [Timed.Component.run, consumed_cons, List.foldl_cons, interpreted] using
      ih ((interpreted memory).step i s) (advance storage (decoded s.adapters).values)
        ((PairedTimed.physical_refinement memory).step _ s.core storage hs)

/-- Three sampled reset-low edges establish the storage/runtime invariant
from arbitrary adapter registers, controller state, SRAM contents and Q. -/
theorem reset_initializes (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S)
    (resetPin : Chip.Pins) (hr : resetPin.rstN = false) :
    ∃ storage : Tracked,
      PairedCoverage.view memory ((interpreted memory).run s [resetPin, resetPin, resetPin]).core = storage.physical ∧
        PairedRuntime.Invariant storage := by
  let initial : Tracked := ⟨s.core.1, memory.view s.core.2, {}⟩
  refine ⟨(Chip.consumed s.adapters [resetPin, resetPin, resetPin]).foldl
    (fun t i => advance t i.values) initial, run_storage memory s initial rfl _, ?_⟩
  apply PairedRuntime.invariant_initialize
  change BitVec.ofBool (!resetPin.rstN) = 1
  simp [hr]
  done

theorem invariant_run (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S)
    (storage : Tracked) (hs : PairedCoverage.view memory s.core = storage.physical)
    (h : PairedRuntime.Invariant storage) (pins : List Chip.Pins) :
    ∃ t : Tracked, PairedCoverage.view memory ((interpreted memory).run s pins).core = t.physical ∧
      PairedRuntime.Invariant t := by
  refine ⟨(Chip.consumed s.adapters pins).foldl (fun t i => advance t i.values) storage,
    run_storage memory s storage hs pins, ?_⟩
  simpa only [List.foldl_map] using PairedRuntime.invariant_run
    ((Chip.consumed s.adapters pins).map fun i => (i.values : Values Loader.Machine.Input)) storage h

theorem session_delivers (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S)
    (hcount : s.adapters.receiver.count = 0) (hfire : s.adapters.receiver.fire = false)
    (hfirst : Serial.Idle s.adapters.first) (hsecond : Serial.Idle s.adapters.second)
    (pins : List Chip.Pins) (a b : Chip.Pins) (cs : List (BitVec 3 × BitVec 64))
    (hs : Serial.Session (pins.map Chip.wired) cs) :
    Loader.Machine.Delivers (consumed memory s (pins ++ [a, b])) cs := by
  rw [consumed_eq]
  exact Chip.session_delivers s.adapters hcount hfire hfirst hsecond pins a b cs hs

/-- A certified accepted commit establishes the reference relation in the
package, preserving the existing mailbox contents and adapter pipeline. -/
theorem after_commit (p : Execution.Image) (image : PairedImage.Image)
    (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S) (storage : Tracked)
    (hs : PairedCoverage.view memory s.core = storage.physical) (h : PairedRuntime.Invariant storage)
    (i : Chip.Pins) (hc : PairedLifecycle.Accepted storage (decoded s.adapters).values)
    (hp : PairedImage.check p image storage.ledger.staged = true) :
    Related p image memory ((interpreted memory).step i s)
      ⟨advance storage (decoded s.adapters).values, Engine.Reactive.reset p,
        adaptersNext i s.adapters, ((interpreted memory).step i s).result⟩ := by
  exact ⟨(PairedTimed.physical_refinement memory).step _ s.core storage hs,
    PairedLifecycle.after_commit p image storage _ h hc hp, rfl, rfl⟩

/-- The existing commit/start lifecycle, including certified replacements.
All three package output ports agree before and after every subsequent edge.
No extra reset is inserted, and the prior mailbox need not be empty. -/
theorem retained_commit_segment (p : Execution.Image) (image : PairedImage.Image)
    (n : Netlist Register (Out Loader.Machine.Output) Input) (hn : PairedValidation.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (s : PairedPackage.State S) (storage : Tracked)
    (hs : PairedCoverage.view memory s.core = storage.physical) (h : PairedRuntime.Invariant storage)
    (commitPin : Chip.Pins) (hc : PairedLifecycle.Accepted storage (decoded s.adapters).values)
    (hp : PairedImage.check p image storage.ledger.staged = true) (pins : List Chip.Pins)
    (hi : ∀ i ∈ Chip.consumed (adaptersNext commitPin s.adapters) pins, Rule i.values) :
    (executable (PairedComposition.package n).component memory).trace
        ((executable (PairedComposition.package n).component memory).step commitPin s.physical) pins =
      (reference p).trace
        ⟨advance storage (decoded s.adapters).values, Engine.Reactive.reset p,
          adaptersNext commitPin s.adapters, ((interpreted memory).step commitPin s).result⟩ pins := by
  rw [PairedComposition.retained_package_correct n hn, step_physical,
    ← PairedComposition.retained_package_correct n hn, PairedPackage.retained_trace n hn]
  exact interpreted_trace p image memory _ _ (after_commit p image memory s storage hs h commitPin hc hp) pins hi
  done

/-- Initialization, arbitrary host history, accepted certified commit, then
execution: one conditional package theorem, with the ledger constructed by the
actual accepted writes. The upload prefix can contain earlier executions and
replacements. The theorem does not assume every offered word is admitted. -/
theorem retained_initialized_commit_segment (p : Execution.Image) (image : PairedImage.Image)
    (n : Netlist Register (Out Loader.Machine.Output) Input) (hn : PairedValidation.core = .ok n)
    (memory : Memory.SinglePort.Contract S 9 64) (initial : PairedPackage.State S)
    (resetPin : Chip.Pins) (hr : resetPin.rstN = false) (uploadPins : List Chip.Pins) :
    let resetState := (interpreted memory).run initial [resetPin, resetPin, resetPin]
    let prepared := (interpreted memory).run resetState uploadPins
    ∃ storage : Tracked, PairedCoverage.view memory prepared.core = storage.physical ∧
      PairedRuntime.Invariant storage ∧
      ∀ (commitPin : Chip.Pins) (pins : List Chip.Pins),
        PairedLifecycle.Accepted storage (decoded prepared.adapters).values →
        PairedImage.check p image storage.ledger.staged = true →
        (∀ i ∈ Chip.consumed (adaptersNext commitPin prepared.adapters) pins, Rule i.values) →
        (executable (PairedComposition.package n).component memory).trace
          ((executable (PairedComposition.package n).component memory).step commitPin
            ((executable (PairedComposition.package n).component memory).run
              ((executable (PairedComposition.package n).component memory).run initial.physical
                [resetPin, resetPin, resetPin]) uploadPins)) pins =
          (reference p).trace
            ⟨advance storage (decoded prepared.adapters).values, Engine.Reactive.reset p,
              adaptersNext commitPin prepared.adapters, ((interpreted memory).step commitPin prepared).result⟩ pins := by
  obtain ⟨resetStorage, hs, h⟩ := reset_initializes memory initial resetPin hr
  obtain ⟨storage, hview, hinv⟩ := invariant_run memory _ resetStorage hs h uploadPins
  refine ⟨storage, hview, hinv, ?_⟩
  intro commitPin pins hc hp hi
  simpa only [PairedPackage.retained_run n hn] using
    retained_commit_segment p image n hn memory _ storage hview hinv commitPin hc hp pins hi
  done

end Pinwheel.Hardware.Storage.PairedHost
