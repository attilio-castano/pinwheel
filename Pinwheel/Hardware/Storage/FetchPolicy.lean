import Pinwheel.Hardware.Storage.Dispatch
import Pinwheel.Hardware.TimedRule

/-! Fetch organizations against a memory of latency one, as a parameter.

The scheduler consumes a successor word only on the edge that dispatches. A
memory of latency one cannot serve that read on the same edge, so the machine
reads ahead; *how* — how many read ports, which addresses on which edge, which
registers hold the words — is a `Policy`. The policy sees the scheduler's
inputs, its state and whether the edge commits, never the memory: it puts
addresses on `p` read ports of the selected bank and receives the `p` words,
which it may only register. The word it feeds the scheduler comes from its
registers alone — that is latency one — and `p` is the number of read trees,
by construction.

A policy is correct (`Correct`) when it supplies an invariant, possibly a rule on
inputs, and three facts: on a dispatching edge the fed word is the word the
reference reads (`covers`), the invariant survives an edge (`preserved`), and
initialization establishes it (`initial`). From these the machine refines the
atomic reference edge for edge (`trace_correct`, `refinement`), proved once.
The rest of the file is what two-candidate policies share. -/
namespace Pinwheel.Hardware.Storage.FetchPolicy
open Loader

/-- A fetch organization with `p` read ports and registers `σ`. `fed` is the
successor given to the scheduler, from the scheduler's inputs, its state and the
policy's registers. `address` and `step` additionally see the fed inputs and
whether this edge commits; `step` receives the words behind the ports. -/
structure Policy (p : Nat) (σ : Type) where
  fed : Reactive.Inputs → Reactive.State → σ → BitVec 64
  address : Reactive.Inputs → Reactive.State → Bool → σ → Fin p → BitVec 8
  step : Reactive.Inputs → Reactive.State → Bool → σ → (Fin p → BitVec 64) → σ

structure State (σ : Type) where
  machine : Machine.State
  current : BitVec 64
  policy : σ

def State.cache (s : State σ) : Cache.State := ⟨s.machine, s.current⟩

section Machine
variable {p : Nat} {σ : Type} (P : Policy p σ)

def feed (i : Machine.Inputs) (s : State σ) : Reactive.Inputs :=
  {Cache.base i s.cache with successor := P.fed (Cache.base i s.cache) s.machine.core s.policy}

def addresses (i : Machine.Inputs) (s : State σ) : Fin p → BitVec 8 :=
  P.address (feed P i s) s.machine.core (Machine.committing i s.machine) s.policy

/-- What the machine asks of the selected bank on an edge: no write (the loader
owns the write port) and the policy's addresses on `p` read ports. -/
def request (i : Machine.Inputs) (s : State σ) : Memory.Request 8 64 p :=
  ⟨⟨false, 0, 0⟩, addresses P i s⟩

/-- The words behind the ports: the read ports of the selected bank's composite
memory. Registered by the policy, they are what a memory of latency one
(`Memory.spec 8 64 p 1`) has pending after this edge. -/
def reads (i : Machine.Inputs) (s : State σ) : Fin p → BitVec 64 :=
  (Loader.Store.composite (s.machine.memory (Machine.selected i s.machine))).reads (request P i s)

theorem reads_eq (i : Machine.Inputs) (s : State σ) (port : Fin p) :
    reads P i s port =
      Loader.Store.read (s.machine.memory (Machine.selected i s.machine)) (addresses P i s port) := rfl

/-- The cached word loads the fed successor on a dispatch or at rest; control,
core and memory are the reference's with the core stepped on the fed inputs. -/
def next (i : Machine.Inputs) (s : State σ) : State σ :=
  -- Shared values, so that executing the machine does not re-derive the feed
  -- inside the words' closures; `next_policy` restates the policy step on `reads`.
  let f := feed P i s
  let committing := Machine.committing i s.machine
  let address := P.address f s.machine.core committing s.policy
  let read := Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
  { machine := {Machine.next i s.machine with core := Reactive.stepValue f s.machine.core}
    current := if Dispatch.dispatching f s.machine.core || !Reactive.runningValue s.machine.core
      then f.successor else s.current
    policy := P.step f s.machine.core committing s.policy (fun port => read (address port)) }

theorem next_policy (i : Machine.Inputs) (s : State σ) :
    (next P i s).policy =
      P.step (feed P i s) s.machine.core (Machine.committing i s.machine) s.policy (reads P i s) := rfl

/-- What a policy owes. -/
structure Correct (P : Policy p σ) where
  Inv : State σ → Prop
  /-- A condition on inputs the invariant's preservation may assume. -/
  Rule : Machine.Inputs → Prop
  /-- On a dispatching edge the fed word is the word the reference reads. -/
  covers : ∀ (i : Machine.Inputs) (s : State σ), Cache.Valid s.cache → Inv s →
    s.machine.control.valid = true → Machine.committing i s.machine = false →
    Dispatch.dispatching (feed P i s) s.machine.core = true →
    (feed P i s).successor = Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
      (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.machine.core⟩)
  preserved : ∀ (i : Machine.Inputs) (s : State σ), Cache.Valid s.cache → Inv s → Rule i →
    (next P i s).machine = Machine.next i s.machine → Inv (next P i s)
  initial : ∀ (i : Machine.Inputs) (s : State σ), i.init = true →
    (next P i s).machine = Machine.next i s.machine → Inv (next P i s)

variable {P}

def Valid (C : Correct P) (s : State σ) : Prop := Cache.Valid s.cache ∧ C.Inv s

theorem base_reset (i : Machine.Inputs) (s : State σ) :
    (Cache.base i s.cache).reset =
      (i.init || i.reset || !s.machine.control.valid || Machine.committing i s.machine) := rfl

theorem dispatching_feed (i : Machine.Inputs) (s : State σ) :
    Dispatch.dispatching (feed P i s) s.machine.core =
      Dispatch.dispatching (Cache.feed i s.cache) s.machine.core := rfl

/-- A commit edge resets the scheduler: it does not dispatch. -/
theorem dispatch_no_commit (i : Machine.Inputs) (s : State σ)
    (hd : Dispatch.dispatching (feed P i s) s.machine.core = true) :
    Machine.committing i s.machine = false := by
  cases hc : Machine.committing i s.machine
  · rfl
  · have hr : (feed P i s).reset = true := by
      show (Cache.base i s.cache).reset = true
      simp [base_reset, hc]
    simp [Dispatch.dispatching, hr] at hd

/-- The scheduler steps as the reference's: a dispatch is covered, and without
one the successor is not consulted. -/
theorem step_eq (C : Correct P) (i : Machine.Inputs) (s : State σ) (h : Valid C s) :
    Reactive.stepValue (feed P i s) s.machine.core =
      Reactive.stepValue (Cache.feed i s.cache) s.machine.core := by
  by_cases hv : s.machine.control.valid = true
  · by_cases hc : Machine.committing i s.machine = false
    · by_cases hd : Dispatch.dispatching (feed P i s) s.machine.core = true
      · have hs := C.covers i s h.1 h.2 hv hc hd
        have : feed P i s = Cache.feed i s.cache := by
          simp only [feed] at hs ⊢
          simp only [Cache.feed, Reactive.Fetch.resolve, hs]
          rfl
        rw [this]
      · have hd' : Dispatch.dispatching (Cache.feed i s.cache) s.machine.core = false := by
          rw [← dispatching_feed (P := P)]; simpa using hd
        have : feed P i s = {Cache.feed i s.cache with successor := (feed P i s).successor} := by
          simp only [feed, Cache.feed, Reactive.Fetch.resolve]
        rw [this, Dispatch.step_successor_irrelevant _ _ _ hd']
    · have hr : (Cache.base i s.cache).reset = true := by
        simp [base_reset, show Machine.committing i s.machine = true by simpa using hc]
      simp [Reactive.stepValue, hr, Reactive.stopValue, feed, Cache.feed, Reactive.Fetch.resolve]
  · have hr : (Cache.base i s.cache).reset = true := by
      simp [base_reset, show s.machine.control.valid = false by simpa using hv]
    simp [Reactive.stepValue, hr, Reactive.stopValue, feed, Cache.feed, Reactive.Fetch.resolve]

theorem core_next (C : Correct P) (i : Machine.Inputs) (s : State σ) (h : Valid C s) :
    (next P i s).machine.core = (Cache.next i s.cache).machine.core := by
  simp only [next, Cache.next, step_eq C i s h]
  rfl

/-- Control, core and memory follow the reference exactly. -/
theorem machine_next (C : Correct P) (i : Machine.Inputs) (s : State σ) (h : Valid C s) :
    (next P i s).machine = Machine.next i s.machine := by
  have hc := core_next C i s h
  rw [Cache.machine_next i s.cache h.1] at hc
  simp only [next] at hc ⊢
  rw [hc]
  rfl

/-- Facts available on an edge after which the machine runs. -/
theorem running_facts (i : Machine.Inputs) (s : State σ)
    (hm : (next P i s).machine = Machine.next i s.machine)
    (hb : Reactive.runningValue (Reactive.stepValue (feed P i s) s.machine.core) = true) :
    s.machine.control.valid = true ∧ Machine.committing i s.machine = false ∧
      Machine.selected i s.machine = s.machine.control.active ∧
      (Machine.next i s.machine).control.active = s.machine.control.active := by
  have hr := Cache.running_reset (feed P i s) s.machine.core hb
  have hvc : s.machine.control.valid = true ∧ Machine.committing i s.machine = false := by
    simp only [feed, base_reset, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hr
    exact ⟨hr.1.2, hr.2⟩
  have hsel : Machine.selected i s.machine = s.machine.control.active := by
    simp [Machine.selected, hvc.2]
  have hactive := (Cache.running_selection i s.machine (by rw [← hm]; exact hb)).1
  exact ⟨hvc.1, hvc.2, hsel, hactive⟩

/-- The active bank is untouched by an edge after which the machine runs. -/
theorem running_memory (i : Machine.Inputs) (s : State σ)
    (hm : (next P i s).machine = Machine.next i s.machine)
    (hb : Reactive.runningValue (Reactive.stepValue (feed P i s) s.machine.core) = true)
    {w : Nat} (r : Store.Register w) :
    (next P i s).machine.memory (next P i s).machine.control.active r =
      s.machine.memory s.machine.control.active r := by
  obtain ⟨_, _, _, hactive⟩ := running_facts i s hm hb
  rw [hm, hactive]
  exact Machine.active_memory_preserved i s.machine r

/-- Running after the edge, the cached word is the word at the new address. -/
theorem cache_valid_next (C : Correct P) (i : Machine.Inputs) (s : State σ) (h : Valid C s) :
    Cache.Valid (next P i s).cache := by
  intro hb
  have hb' : Reactive.runningValue (Reactive.stepValue (feed P i s) s.machine.core) = true := hb
  have hm := machine_next C i s h
  obtain ⟨hv, hc, hsel, _⟩ := running_facts i s hm hb'
  obtain ⟨hd, hs⟩ := Dispatch.step_structure (feed P i s) s.machine.core hb'
  have hpc' : (next P i s).machine.core.pc = (Reactive.stepValue (feed P i s) s.machine.core).pc := rfl
  show (next P i s).current =
    Loader.Store.read ((next P i s).machine.memory (next P i s).machine.control.active) (next P i s).machine.core.pc
  simp only [Loader.Store.read, running_memory i s hm hb', hpc']
  by_cases hdis : Dispatch.dispatching (feed P i s) s.machine.core = true
  · obtain ⟨hpc, _⟩ := hd hdis
    have hsucc := C.covers i s h.1 h.2 hv hc hdis
    rw [hsel] at hsucc
    show (if (Dispatch.dispatching (feed P i s) s.machine.core || !Reactive.runningValue s.machine.core) = true
      then (feed P i s).successor else s.current) = _
    rw [if_pos (by rw [hdis]; simp), hpc]
    exact hsucc
  · have hdis' : Dispatch.dispatching (feed P i s) s.machine.core = false := by simpa using hdis
    obtain ⟨hpc, _, hrun⟩ := hs hdis'
    show (if (Dispatch.dispatching (feed P i s) s.machine.core || !Reactive.runningValue s.machine.core) = true
      then (feed P i s).successor else s.current) = _
    rw [if_neg (by rw [hdis', hrun]; decide), hpc]
    exact h.1 hrun

theorem valid_next (C : Correct P) (i : Machine.Inputs) (s : State σ) (h : Valid C s) (hr : C.Rule i) :
    Valid C (next P i s) :=
  ⟨cache_valid_next C i s h, C.preserved i s h.1 h.2 hr (machine_next C i s h)⟩

/-- On an initializing edge the machine part follows the reference without any
invariant: the core stops whatever the policy feeds. -/
theorem initialize_machine_next (i : Machine.Inputs) (s : State σ) (hi : i.init = true) :
    (next P i s).machine = Machine.next i s.machine := by
  simp only [next, Machine.next, Reactive.stepValue, feed, base_reset, hi, Machine.schedulerInput,
    Machine.baseInput, Reactive.Fetch.resolve, Bool.true_or, if_true, Reactive.stopValue,
    Machine.State.mk.injEq, and_true, true_and]
  rfl

/-- Initialization establishes validity from any state. -/
theorem initialize_valid (C : Correct P) (i : Machine.Inputs) (s : State σ) (hi : i.init = true) :
    Valid C (next P i s) := by
  have hr : (Cache.base i s.cache).reset = true := by simp [base_reset, hi]
  refine ⟨?_, C.initial i s hi (initialize_machine_next i s hi)⟩
  apply Cache.idle_valid
  show Reactive.runningValue (Reactive.stepValue (feed P i s) s.machine.core) = false
  simp [Reactive.stepValue, feed, hr, Reactive.stopValue, Reactive.runningValue]

variable (P) in
/-- Outputs are the cache machine's: none of them reads the policy's registers. -/
def component : Timed.Component Machine.Inputs (State σ) (Values Machine.Output) :=
  ⟨next P, fun i s => Cache.circuit.observe i.values s.cache.values⟩

/-- The machine refines the atomic reference edge for edge, on inputs that
satisfy the policy's rule. -/
def ruleRefinement (C : Correct P) :
    Timed.RuleRefinement (component P) Cache.referenceComponent C.Rule where
  Rel := fun s t => Valid C s ∧ s.machine = t
  step := fun i s t hr h => ⟨valid_next C i s h.1 hr,
    (machine_next C i s h.1).trans (congrArg (Machine.next i) h.2)⟩
  observe := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact funext fun w => funext fun o => Cache.output_correct i s.cache hv.1 o

/-- Every pre/post-edge observation is the reference machine's, on any history
whose inputs satisfy the policy's rule. -/
theorem trace_correct (C : Correct P) (s : State σ) (h : Valid C s) (inputs : List Machine.Inputs)
    (hr : ∀ i ∈ inputs, C.Rule i) :
    (component P).trace s inputs = Cache.referenceComponent.trace s.machine inputs :=
  (ruleRefinement C).trace_eq s s.machine ⟨h, rfl⟩ inputs hr

/-- A policy without a rule is a refinement in the timed sense. -/
def refinement (C : Correct P) (hrule : ∀ i, C.Rule i) :
    Timed.Refinement (component P) Cache.referenceComponent where
  Rel := fun s t => Valid C s ∧ s.machine = t
  step := fun i s t h => ⟨valid_next C i s h.1 (hrule i),
    (machine_next C i s h.1).trans (congrArg (Machine.next i) h.2)⟩
  observe := fun i s t h => by
    rcases h with ⟨hv, rfl⟩
    exact funext fun w => funext fun o => Cache.output_correct i s.cache hv.1 o

theorem initialized_trace (C : Correct P) (s : State σ) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) (hr : ∀ j ∈ inputs, C.Rule j) :
    (component P).trace (next P i s) inputs =
      Cache.referenceComponent.trace (Machine.next i s.machine) inputs := by
  rw [← initialize_machine_next (P := P) i s hi]
  exact trace_correct C (next P i s) (initialize_valid C i s hi) inputs hr

end Machine

/-! ### Two-candidate policies

The scheduler's next consumption is one of two words, chosen by the branch bit:
the words of the active bank at the canonical candidate addresses. At rest both
are word 0. What follows is what policies built on the decision-based candidates
(`Dispatch.candidate`) share. -/

section Candidates
variable {p : Nat} {σ : Type} {P : Policy p σ}

/-- The word consumed at the next dispatch if the branch bit is `b`. -/
def canonical (m : Machine.State) (current : BitVec 64) (b : Bool) : BitVec 64 :=
  Loader.Store.read (m.memory m.control.active) (Prefetch.candidate m.core current b)

def branch (i : Machine.Inputs) (s : State σ) : Bool :=
  Reactive.Fetch.branchBit ⟨Cache.base i s.cache, s.machine.core⟩

/-- Without a commit, the word the reference reads is the canonical word the
branch bit selects. -/
theorem reference_word (i : Machine.Inputs) (s : State σ) (hc : Machine.committing i s.machine = false) :
    Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
      (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.machine.core⟩) =
        canonical s.machine s.current (branch i s) := by
  have hsel : Machine.selected i s.machine = s.machine.control.active := by
    simp [Machine.selected, hc]
  rw [hsel, Reactive.Fetch.address_choice ⟨Cache.base i s.cache, s.machine.core⟩,
    Prefetch.candidate_correct, Prefetch.candidate_correct]
  have hcur : (Cache.base i s.cache).current = s.current := rfl
  rw [hcur]
  unfold canonical branch
  cases Reactive.Fetch.branchBit ⟨Cache.base i s.cache, s.machine.core⟩ <;> rfl

theorem canonical_rest (m : Machine.State) (current : BitVec 64) (b : Bool)
    (hr : Reactive.runningValue m.core = false) :
    canonical m current b = Loader.Store.read (m.memory m.control.active) 0 := by
  simp [canonical, Prefetch.candidate, hr]

/-- The word read this edge at a decision-based candidate is the next state's
canonical word, when the machine runs after the edge. -/
theorem read_next (i : Machine.Inputs) (s : State σ)
    (hm : (next P i s).machine = Machine.next i s.machine)
    (hb : Reactive.runningValue (Reactive.stepValue (feed P i s) s.machine.core) = true) (b : Bool) :
    Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
        (Dispatch.candidate (feed P i s) s.machine.core b) =
      canonical (next P i s).machine (next P i s).current b := by
  obtain ⟨_, _, hsel, _⟩ := running_facts i s hm hb
  have hcore : (next P i s).machine.core = Reactive.stepValue (feed P i s) s.machine.core := rfl
  have hcur : (next P i s).current =
      (if (Dispatch.dispatching (feed P i s) s.machine.core || !Reactive.runningValue s.machine.core) = true
        then (feed P i s).successor else (feed P i s).current) := rfl
  unfold canonical
  rw [hsel, hcore, hcur, Dispatch.candidate_correct (feed P i s) s.machine.core b hb]
  simp only [Loader.Store.read, running_memory i s hm hb]

/-- Without a dispatch the canonical words do not move. -/
theorem stay (i : Machine.Inputs) (s : State σ)
    (hm : (next P i s).machine = Machine.next i s.machine)
    (hb : Reactive.runningValue (Reactive.stepValue (feed P i s) s.machine.core) = true)
    (hdis : Dispatch.dispatching (feed P i s) s.machine.core = false) (b : Bool) :
    canonical s.machine s.current b = canonical (next P i s).machine (next P i s).current b := by
  obtain ⟨_, hs⟩ := Dispatch.step_structure (feed P i s) s.machine.core hb
  obtain ⟨hpc, hmode, hrun⟩ := hs hdis
  have hcore : (next P i s).machine.core = Reactive.stepValue (feed P i s) s.machine.core := rfl
  have hcur : (next P i s).current =
      (if (Dispatch.dispatching (feed P i s) s.machine.core || !Reactive.runningValue s.machine.core) = true
        then (feed P i s).successor else s.current) := rfl
  unfold canonical
  rw [hcore, hcur, if_neg (by rw [hdis, hrun]; decide), Dispatch.candidate_congr _ _ _ _ hmode hpc]
  simp only [Loader.Store.read, running_memory i s hm hb]

/-- A start-word register loaded on commit with word 0 of the selected bank
holds word 0 of the active bank while an image is committed. -/
theorem start_word_next (i : Machine.Inputs) (s : State σ)
    (hm : (next P i s).machine = Machine.next i s.machine) (w : BitVec 64)
    (hw : s.machine.control.valid = true →
      w = Loader.Store.read (s.machine.memory s.machine.control.active) 0)
    (hv : (next P i s).machine.control.valid = true) :
    (if Machine.committing i s.machine then
        Loader.Store.read (s.machine.memory (Machine.selected i s.machine)) 0 else w) =
      Loader.Store.read ((next P i s).machine.memory (next P i s).machine.control.active) 0 := by
  rw [hm] at hv ⊢
  by_cases hc : Machine.committing i s.machine = true
  · simp only [hc, if_true, Loader.Store.read, Prefetch.selected_memory i s.machine hv]
  · have hc' : Machine.committing i s.machine = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, if_false]
    by_cases hi : i.init = true
    · exfalso
      have : (Machine.next i s.machine).control = {} := (Machine.initialize_safe i s.machine hi).1
      simp [this] at hv
    · have ha := (Loader.no_commit_preserves_selection (Machine.controlInput i s.machine) s.machine.control
        (by simpa [Machine.controlInput] using hi) hc')
      have hact : (Machine.next i s.machine).control.active = s.machine.control.active := ha.1
      have hv0 : s.machine.control.valid = true := by
        have hvalid : (Machine.next i s.machine).control.valid = s.machine.control.valid := ha.2
        rw [hvalid] at hv
        exact hv
      have hmem : ∀ {w : Nat} (r : Store.Register w),
          (Machine.next i s.machine).memory (Machine.next i s.machine).control.active r =
            s.machine.memory s.machine.control.active r := by
        intro w r
        rw [hact]
        exact Machine.active_memory_preserved i s.machine r
      rw [hw hv0]
      simp only [Loader.Store.read, hmem]

end Candidates

end Pinwheel.Hardware.Storage.FetchPolicy
