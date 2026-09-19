import Pinwheel.Hardware.Storage.CacheContract
import Pinwheel.Hardware.Storage.CacheProofs
import Pinwheel.Hardware.Reactive.FetchChoice
import Pinwheel.Hardware.Storage.MemoryView

/-! The machine against a memory of latency one. The scheduler enters an
instruction's successor on the edge that finishes it, and which successor is
only known on that edge (the branch bit is a terminal capture of the pins). A
synchronous memory cannot serve that read. This machine therefore reads, on
every edge, the words at *both* candidate addresses of the next edge — computed
from the next-state values, not from the pins — and keeps them in two registers;
the edge that dispatches selects one. With the current-word cache this is the
whole "successor availability" obligation of the SRAM review. The machine
refines the atomic reference machine exactly, edge for edge, with two read ports
on the selected bank and no added cycle. -/
namespace Pinwheel.Hardware.Storage.Prefetch
open Loader

structure State where
  machine : Machine.State
  current : BitVec 64
  /-- The word at the candidate address for a taken (`true`) or untaken (`false`)
  branch, read on the previous edge from the bank selected then. -/
  fetched : Bool → BitVec 64

def State.cache (s : State) : Cache.State := ⟨s.machine, s.current⟩

/-- The candidate addresses of an edge, from the core state and current word that
edge sees; the input-dependent choice between them is `branch`. -/
def candidate (core : Reactive.State) (current : BitVec 64) (b : Bool) : BitVec 8 :=
  let d := Execution.unpack current
  if Reactive.runningValue core then
    if core.mode != 3 || d.finish == 0 then core.pc - 255
    else if d.finish = 1 then d.yes
    else if b then d.yes else d.no
  else 0

theorem candidate_correct (ctx : Reactive.Inputs) (core : Reactive.State) (b : Bool) :
    Reactive.Fetch.candidateAddress ⟨ctx, core⟩ b = candidate core ctx.current b := by
  simp [Reactive.Fetch.candidateAddress, candidate, Reactive.sequentialValue]

def branch (i : Machine.Inputs) (s : State) : Bool :=
  Reactive.Fetch.branchBit ⟨Cache.base i s.cache, s.machine.core⟩

def feed (i : Machine.Inputs) (s : State) : Reactive.Inputs :=
  {Cache.base i s.cache with successor := s.fetched (branch i s)}

/-- The request the machine puts to the selected bank on an edge: no write (the
loader owns the write port), and both candidates of the next edge on two read ports. -/
def request (core : Reactive.State) (current : BitVec 64) : Memory.Request 8 64 2 :=
  ⟨⟨false, 0, 0⟩, fun port => candidate core current (port = 0)⟩

def next (i : Machine.Inputs) (s : State) : State :=
  let core := Reactive.stepValue (feed i s) s.machine.core
  let current := if !Reactive.runningValue s.machine.core || core.pc != s.machine.core.pc
    then (feed i s).successor else s.current
  { machine := {Machine.next i s.machine with core := core}
    current := current
    fetched := fun b => Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
      (candidate core current b) }

/-- The two fetched words are the two read ports of the selected bank's composite
memory, requested with the next edge's candidates: exactly what a memory of
latency one (`Memory.spec 8 64 2 1`) has pending after this edge. -/
theorem fetched_reads (i : Machine.Inputs) (s : State) (b : Bool) :
    (next i s).fetched b = (Loader.Store.composite (s.machine.memory (Machine.selected i s.machine))).reads
      (request (next i s).machine.core (next i s).current) (if b then 0 else 1) := by
  cases b <;> rfl

/-- The invariant: while an image is committed, the fetched words are the words
of the active bank at this edge's candidate addresses. -/
def Prefetched (s : State) : Prop :=
  s.machine.control.valid = true → ∀ b,
    s.fetched b = Loader.Store.read (s.machine.memory s.machine.control.active) (candidate s.machine.core s.current b)

def Valid (s : State) : Prop := Cache.Valid s.cache ∧ Prefetched s

theorem base_reset (i : Machine.Inputs) (s : State) :
    (Cache.base i s.cache).reset =
      (i.init || i.reset || !s.machine.control.valid || Machine.committing i s.machine) := by
  rfl

/-- With an image committed and no commit on this edge, the selected word is
the word the reference reads: the branch bit chooses between the candidates. -/
theorem successor_eq (i : Machine.Inputs) (s : State) (h : Valid s)
    (hv : s.machine.control.valid = true) (hc : Machine.committing i s.machine = false) :
    s.fetched (branch i s) = Loader.Store.read (s.cache.machine.memory (Machine.selected i s.cache.machine))
      (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.cache.machine.core⟩) := by
  have hsel : Machine.selected i s.machine = s.machine.control.active := by
    simp [Machine.selected, hc]
  have hf := h.2 hv (branch i s)
  change s.fetched (branch i s) = Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
    (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.machine.core⟩)
  rw [hf, hsel, Reactive.Fetch.address_choice ⟨Cache.base i s.cache, s.machine.core⟩,
    candidate_correct, candidate_correct]
  have hcur : (Cache.base i s.cache).current = s.current := rfl
  rw [hcur]
  unfold branch
  cases Reactive.Fetch.branchBit ⟨Cache.base i s.cache, s.machine.core⟩ <;> rfl

theorem feed_eq (i : Machine.Inputs) (s : State) (h : Valid s)
    (hv : s.machine.control.valid = true) (hc : Machine.committing i s.machine = false) :
    feed i s = Cache.feed i s.cache := by
  simp only [feed, Cache.feed, Reactive.Fetch.resolve, successor_eq i s h hv hc]

theorem step_eq (i : Machine.Inputs) (s : State) (h : Valid s) :
    Reactive.stepValue (feed i s) s.machine.core = Reactive.stepValue (Cache.feed i s.cache) s.machine.core := by
  by_cases hv : s.machine.control.valid = true
  · by_cases hc : Machine.committing i s.machine = false
    · rw [feed_eq i s h hv hc]
    · have hr : (Cache.base i s.cache).reset = true := by
        simp [base_reset, show Machine.committing i s.machine = true by simpa using hc]
      simp [Reactive.stepValue, hr, Reactive.stopValue, feed, Cache.feed, Reactive.Fetch.resolve]
  · have hr : (Cache.base i s.cache).reset = true := by
      simp [base_reset, show s.machine.control.valid = false by simpa using hv]
    simp [Reactive.stepValue, hr, Reactive.stopValue, feed, Cache.feed, Reactive.Fetch.resolve]

theorem core_next (i : Machine.Inputs) (s : State) (h : Valid s) :
    (next i s).machine.core = (Cache.next i s.cache).machine.core := by
  simp only [next, Cache.next, step_eq i s h]
  rfl

/-- The prefetch machine's control, core and memory follow the reference exactly. -/
theorem machine_next (i : Machine.Inputs) (s : State) (h : Valid s) :
    (next i s).machine = Machine.next i s.machine := by
  have hc := core_next i s h
  rw [Cache.machine_next i s.cache h.1] at hc
  simp only [next] at hc ⊢
  rw [hc]
  rfl

/-- When the core runs after this edge, the cache and the reference's cache agree. -/
theorem cache_next (i : Machine.Inputs) (s : State) (h : Valid s)
    (hb : Reactive.runningValue (next i s).machine.core = true) :
    (next i s).cache = Cache.next i s.cache := by
  have hr := Cache.running_reset (feed i s) s.machine.core (by simpa [next] using hb)
  have hvc : s.machine.control.valid = true ∧ Machine.committing i s.machine = false := by
    simp only [feed, base_reset, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hr
    exact ⟨hr.1.2, hr.2⟩
  have hf := feed_eq i s h hvc.1 hvc.2
  simp only [State.cache, next, Cache.next, hf]
  rfl

theorem cache_valid_next (i : Machine.Inputs) (s : State) (h : Valid s) : Cache.Valid (next i s).cache := by
  by_cases hb : Reactive.runningValue (next i s).machine.core = true
  · rw [cache_next i s h hb]
    exact Cache.valid_next i s.cache h.1
  · exact Cache.idle_valid _ (show Reactive.runningValue (next i s).machine.core = false by simpa using hb)

/-- The bank read on this edge is the bank active on the next edge, unchanged:
the loader never writes the selected bank, and a commit writes nothing. -/
theorem selected_memory (i : Machine.Inputs) (s : Machine.State)
    (hv : (Machine.next i s).control.valid = true) (r : Store.Register w) :
    s.memory (Machine.selected i s) r = (Machine.next i s).memory (Machine.next i s).control.active r := by
  by_cases hi : i.init = true
  · exfalso
    have : (Machine.next i s).control = {} := (Machine.initialize_safe i s hi).1
    simp [this] at hv
  by_cases hc : Machine.committing i s = true
  · have hn := Machine.commit_switches_image i s hc r
    have hsel : Machine.selected i s = !s.control.active := by simp [Machine.selected, hc]
    rw [hsel]
    exact hn.2.symm
  · have hc' : Machine.committing i s = false := by simpa using hc
    have hsel : Machine.selected i s = s.control.active := by simp [Machine.selected, hc']
    have ha := (Loader.no_commit_preserves_selection (Machine.controlInput i s) s.control
      (by simpa [Machine.controlInput] using hi) hc').1
    rw [hsel]
    change s.memory s.control.active r =
      (Machine.next i s).memory (Loader.next (Machine.controlInput i s) s.control).active r
    rw [ha]
    exact (Machine.active_memory_preserved i s r).symm

theorem prefetched_next (i : Machine.Inputs) (s : State) (h : Valid s) : Prefetched (next i s) := by
  intro hv b
  have hm := machine_next i s h
  rw [hm] at hv
  show Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
    (candidate (next i s).machine.core (next i s).current b) = _
  rw [hm]
  simp only [Loader.Store.read, selected_memory i s.machine hv]

theorem valid_next (i : Machine.Inputs) (s : State) (h : Valid s) : Valid (next i s) :=
  ⟨cache_valid_next i s h, prefetched_next i s h⟩

/-- Initialization establishes the invariant from any state: the core stops and
no image is committed, so nothing is owed until the next commit refills the
fetched words from the newly selected bank. -/
theorem initialize_valid (i : Machine.Inputs) (s : State) (hi : i.init = true) : Valid (next i s) := by
  have hr : (Cache.base i s.cache).reset = true := by simp [base_reset, hi]
  constructor
  · apply Cache.idle_valid
    show Reactive.runningValue (Reactive.stepValue (feed i s) s.machine.core) = false
    simp [Reactive.stepValue, feed, hr, Reactive.stopValue, Reactive.runningValue]
  · intro hv
    exfalso
    have : (Machine.next i s.machine).control = {} := (Machine.initialize_safe i s.machine hi).1
    simp [next, this] at hv

/-- Outputs are the cache machine's: none of them reads the fetched words. -/
def component : Timed.Component Machine.Inputs State (Values Machine.Output) :=
  ⟨next, fun i s => Cache.circuit.observe i.values s.cache.values⟩

def refinement : Timed.Refinement component Cache.referenceComponent where
  Rel := fun s t => Valid s ∧ s.machine = t
  step := fun i s t h => ⟨valid_next i s h.1,
    (machine_next i s h.1).trans (congrArg (Machine.next i) h.2)⟩
  observe := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact funext fun w => funext fun o => Cache.output_correct i s.cache hv.1 o

theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    component.trace s inputs = Cache.referenceComponent.trace s.machine inputs :=
  refinement.trace_eq s s.machine ⟨h, rfl⟩ inputs

/-- On an initializing edge the machine part follows the reference without any
invariant: the core stops whatever the fetched words hold. -/
theorem initialize_machine_next (i : Machine.Inputs) (s : State) (hi : i.init = true) :
    (next i s).machine = Machine.next i s.machine := by
  simp only [next, Machine.next, Reactive.stepValue, feed, base_reset, hi, Machine.schedulerInput,
    Machine.baseInput, Reactive.Fetch.resolve, Bool.true_or, if_true, Reactive.stopValue,
    Machine.State.mk.injEq, and_true, true_and]
  rfl

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    component.trace (next i s) inputs = Cache.referenceComponent.trace (Machine.next i s.machine) inputs := by
  rw [← initialize_machine_next i s hi]
  exact trace_correct (next i s) (initialize_valid i s hi) inputs

end Pinwheel.Hardware.Storage.Prefetch
