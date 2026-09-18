import Pinwheel.Hardware.Storage.Prefetch

/-! The prefetch machine with its addresses decoupled from the next-state decode.

`Prefetch` computes the next edge's candidate addresses from the next-state
values of the core, so structurally its address path waits for the fetched
word's validity decode. This machine computes them from what the scheduler
decides on the current edge — *whether* it dispatches, and the target address —
and from the fields of the word being entered; when the machine is about to
stop, the addresses are irrelevant and are allowed to be anything. A start-word
register, loaded on commit with word 0 of the newly selected bank, serves the
`start` edge, on which no candidate has been fetched. It refines the atomic
reference machine edge for edge. -/
namespace Pinwheel.Hardware.Storage.Decoupled
open Loader

structure State where
  machine : Machine.State
  current : BitVec 64
  fetched : Bool → BitVec 64
  /-- Word 0 of the active bank, loaded on commit. -/
  startWord : BitVec 64

def State.cache (s : State) : Cache.State := ⟨s.machine, s.current⟩

/-- The scheduler enters a successor on this edge, before validity, halt and the
range check are known: the cases of `advanceValue` that reach `dispatchValue`,
or a start from rest. -/
def advancing (i : Reactive.Inputs) (s : Reactive.State) : Bool :=
  let kind := (Execution.unpack i.current).kind
  if s.mode = 1 then s.remaining = 0
  else if s.mode = 2 then kind == 1 && Reactive.readyValue i
  else if s.mode = 3 then kind == 2 && Reactive.guardValue i && s.remaining = 0
  else kind == 3 && Reactive.guardValue i && s.remaining = 0

def dispatching (i : Reactive.Inputs) (s : Reactive.State) : Bool :=
  !i.reset && (if Reactive.runningValue s then advancing i s else i.start)

/-- The candidates of the next edge, from this edge's decision: after a dispatch
the successors of the word being entered at the target; otherwise those of the
current word at the current address. Meaningful only when the machine keeps
running. -/
def candidate (i : Reactive.Inputs) (s : Reactive.State) (b : Bool) : BitVec 8 :=
  if dispatching i s then
    let d := Execution.unpack i.successor
    if d.kind != 2 || d.finish == 0 then Reactive.targetValue i s - 255
    else if d.finish = 1 then d.yes else if b then d.yes else d.no
  else
    let d := Execution.unpack i.current
    if s.mode != 3 || d.finish == 0 then s.pc - 255
    else if d.finish = 1 then d.yes else if b then d.yes else d.no

def branch (i : Machine.Inputs) (s : State) : Bool :=
  Reactive.Fetch.branchBit ⟨Cache.base i s.cache, s.machine.core⟩

def feed (i : Machine.Inputs) (s : State) : Reactive.Inputs :=
  {Cache.base i s.cache with
    successor := if Reactive.runningValue s.machine.core then s.fetched (branch i s) else s.startWord}

def next (i : Machine.Inputs) (s : State) : State :=
  let f := feed i s
  let core := Reactive.stepValue f s.machine.core
  let read := Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
  { machine := {Machine.next i s.machine with core := core}
    current := if dispatching f s.machine.core || !Reactive.runningValue s.machine.core
      then f.successor else s.current
    fetched := fun b => read (candidate f s.machine.core b)
    startWord := if Machine.committing i s.machine then read 0 else s.startWord }

/-- The invariant: while running, the fetched words are the active bank's words
at this edge's canonical candidate addresses; while an image is committed, the
start word is its word 0. -/
def Prefetched (s : State) : Prop :=
  s.machine.control.valid = true →
    (Reactive.runningValue s.machine.core = true → ∀ b,
      s.fetched b = Loader.Store.read (s.machine.memory s.machine.control.active)
        (Storage.Prefetch.candidate s.machine.core s.current b)) ∧
    s.startWord = Loader.Store.read (s.machine.memory s.machine.control.active) 0

def Valid (s : State) : Prop := Cache.Valid s.cache ∧ Prefetched s

/-! ### What the scheduler does on an edge it keeps running -/

theorem modeOf_three (k : BitVec 3) :
    ((if k = 0#3 then (1#3) else if k = 1#3 then 2#3 else if k = 2#3 then 3#3 else 4#3) = 3#3) ↔ k = 2#3 := by
  by_cases h0 : k = 0#3 <;> by_cases h1 : k = 1#3 <;> by_cases h2 : k = 2#3 <;> simp [h0, h1, h2]

/-- Entering a word that keeps the machine running sets the target as the
address and a mode of 3 exactly for a `checked` word. -/
theorem entry_structure (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.entryValue i s) = true) :
    (Reactive.entryValue i s).pc = Reactive.targetValue i s ∧
      ((Reactive.entryValue i s).mode = 3 ↔ (Execution.unpack i.successor).kind = 2) := by
  simp only [Reactive.entryValue, Reactive.enterValue] at h ⊢
  by_cases hv : Execution.validValue i.successor = true
  · by_cases hk : (Execution.unpack i.successor).kind = 4
    · simp [hv, hk, Reactive.stopValue, Reactive.runningValue] at h
    · rw [if_pos hv, if_neg hk]
      exact ⟨rfl, modeOf_three _⟩
  · simp [hv, Reactive.stopValue, Reactive.runningValue] at h

theorem dispatch_structure (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.dispatchValue i s) = true) :
    Reactive.dispatchValue i s = Reactive.entryValue i s := by
  simp only [Reactive.dispatchValue] at h ⊢
  by_cases hr : Reactive.rangeValue i s = true
  · simp [hr]
  · simp [hr, Reactive.stopValue, Reactive.runningValue] at h

/-- On an edge that keeps the machine running, `advanceValue` dispatches exactly
when `advancing` says so, and otherwise keeps the address and the mode. -/
theorem advance_structure (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.advanceValue i s) = true) :
    (advancing i s = true → Reactive.advanceValue i s = Reactive.dispatchValue i s) ∧
    (advancing i s = false → (Reactive.advanceValue i s).pc = s.pc ∧ (Reactive.advanceValue i s).mode = s.mode) := by
  simp only [Reactive.advanceValue, Reactive.currentKindValue, advancing] at h ⊢
  by_cases m1 : s.mode = 1
  · by_cases hr : s.remaining = 0 <;> simp_all [Reactive.decrementValue]
  by_cases m2 : s.mode = 2
  · by_cases hv : Execution.validValue i.current = true <;>
      by_cases hk : (Execution.unpack i.current).kind = 1 <;>
      by_cases hready : Reactive.readyValue i = true <;>
      by_cases hr : s.remaining = 0 <;>
      simp_all [Reactive.decrementValue, Reactive.stopValue, Reactive.runningValue]
  by_cases m3 : s.mode = 3
  · by_cases hv : Execution.validValue i.current = true <;>
      by_cases hk : (Execution.unpack i.current).kind = 2 <;>
      by_cases hg : Reactive.guardValue i = true <;>
      by_cases hr : s.remaining = 0 <;>
      simp_all [Reactive.decrementValue, Reactive.stopValue, Reactive.runningValue]
  · by_cases hv : Execution.validValue i.current = true <;>
      by_cases hk : (Execution.unpack i.current).kind = 3 <;>
      by_cases hg : Reactive.guardValue i = true <;>
      by_cases hr : s.remaining = 0 <;>
      by_cases hw : s.waitLeft = 0 <;>
      simp_all [Reactive.progressValue, Reactive.retryValue, Reactive.stopValue, Reactive.runningValue]

/-- The crux: on an edge that keeps the machine running, a dispatch enters the
successor at the target with the mode its kind determines, and no dispatch keeps
the address, the mode and the current word. -/
theorem step_structure (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.stepValue i s) = true) :
    (dispatching i s = true →
      (Reactive.stepValue i s).pc = Reactive.targetValue i s ∧
      ((Reactive.stepValue i s).mode = 3 ↔ (Execution.unpack i.successor).kind = 2)) ∧
    (dispatching i s = false →
      (Reactive.stepValue i s).pc = s.pc ∧ (Reactive.stepValue i s).mode = s.mode ∧
      Reactive.runningValue s = true) := by
  have hr : i.reset = false := Cache.running_reset i s h
  simp only [Reactive.stepValue, hr, Bool.false_eq_true, if_false] at h ⊢
  by_cases hb : Reactive.runningValue s = true
  · simp only [hb, if_true] at h ⊢
    obtain ⟨hd, hs⟩ := advance_structure i s h
    simp only [dispatching, hr, hb, Bool.not_false, Bool.true_and, if_true]
    refine ⟨fun ha => ?_, fun ha => ⟨(hs ha).1, (hs ha).2, by first | trivial | exact hb⟩⟩
    rw [hd ha] at h ⊢
    have hd' := dispatch_structure i s h
    rw [hd'] at h ⊢
    exact entry_structure i s h
  · have hb' : Reactive.runningValue s = false := by simpa using hb
    simp only [hb', Bool.false_eq_true, if_false] at h ⊢
    simp only [dispatching, hr, hb', Bool.not_false, Bool.true_and]
    by_cases hs : i.start = true
    · simp only [hs, if_true] at h ⊢
      exact ⟨fun _ => entry_structure i s h, fun h' => by simp at h'⟩
    · simp only [hs, Bool.false_eq_true, if_false] at h
      exact absurd h (by simpa using hb)

/-- Hence the decoupled candidates are the canonical ones of the next state
whenever the machine keeps running. -/
theorem candidate_correct (i : Reactive.Inputs) (s : Reactive.State) (b : Bool)
    (h : Reactive.runningValue (Reactive.stepValue i s) = true) :
    candidate i s b = Storage.Prefetch.candidate (Reactive.stepValue i s)
      (if dispatching i s || !Reactive.runningValue s then i.successor else i.current) b := by
  obtain ⟨hd, hs⟩ := step_structure i s h
  by_cases hdis : dispatching i s = true
  · obtain ⟨hpc, hmode⟩ := hd hdis
    simp only [candidate, Storage.Prefetch.candidate, hdis, if_true, Bool.true_or, h, hpc]
    by_cases hk : (Execution.unpack i.successor).kind = 2#3
    · have hm3 : (Reactive.stepValue i s).mode = 3#3 := hmode.mpr hk
      simp [hk, hm3]
    · have hm3 : ¬ (Reactive.stepValue i s).mode = 3#3 := fun h3 => hk (hmode.mp h3)
      simp [hk, hm3]
  · have hdis' : dispatching i s = false := by simpa using hdis
    obtain ⟨hpc, hmode, hrun⟩ := hs hdis'
    simp only [candidate, Storage.Prefetch.candidate, hdis', Bool.false_or, hrun, Bool.not_true,
      Bool.false_eq_true, if_false, h, if_true, hpc, hmode]

/-! ### Refinement -/

theorem base_reset (i : Machine.Inputs) (s : State) :
    (Cache.base i s.cache).reset =
      (i.init || i.reset || !s.machine.control.valid || Machine.committing i s.machine) := rfl

/-- With an image committed and no commit on this edge, the fed successor is the
word the reference reads: a fetched word while running, the start word at rest. -/
theorem successor_eq (i : Machine.Inputs) (s : State) (h : Valid s)
    (hv : s.machine.control.valid = true) (hc : Machine.committing i s.machine = false) :
    (feed i s).successor =
      Loader.Store.read (s.cache.machine.memory (Machine.selected i s.cache.machine))
        (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.cache.machine.core⟩) := by
  have hsel : Machine.selected i s.machine = s.machine.control.active := by
    simp [Machine.selected, hc]
  obtain ⟨hf, hw⟩ := h.2 hv
  change (if Reactive.runningValue s.machine.core then s.fetched (branch i s) else s.startWord) =
    Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
      (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.machine.core⟩)
  rw [hsel]
  by_cases hr : Reactive.runningValue s.machine.core = true
  · rw [if_pos hr, hf hr (branch i s), Reactive.Fetch.address_choice ⟨Cache.base i s.cache, s.machine.core⟩,
      Storage.Prefetch.candidate_correct, Storage.Prefetch.candidate_correct]
    have hcur : (Cache.base i s.cache).current = s.current := rfl
    rw [hcur]
    unfold branch
    cases Reactive.Fetch.branchBit ⟨Cache.base i s.cache, s.machine.core⟩ <;> rfl
  · have hr' : Reactive.runningValue s.machine.core = false := by simpa using hr
    rw [if_neg (by simp [hr']), hw]
    simp [Reactive.Fetch.Request.address, Reactive.targetValue, hr']

theorem feed_eq (i : Machine.Inputs) (s : State) (h : Valid s)
    (hv : s.machine.control.valid = true) (hc : Machine.committing i s.machine = false) :
    feed i s = Cache.feed i s.cache := by
  have hs := successor_eq i s h hv hc
  simp only [feed] at hs ⊢
  simp only [Cache.feed, Reactive.Fetch.resolve, hs]

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

theorem machine_next (i : Machine.Inputs) (s : State) (h : Valid s) :
    (next i s).machine = Machine.next i s.machine := by
  have hc := core_next i s h
  rw [Cache.machine_next i s.cache h.1] at hc
  simp only [next] at hc ⊢
  rw [hc]
  rfl

/-- Running after the edge: the feed was the reference's, and the cached word is
the word at the new address. -/
theorem cache_valid_next (i : Machine.Inputs) (s : State) (h : Valid s) : Cache.Valid (next i s).cache := by
  intro hb
  have hb' : Reactive.runningValue (Reactive.stepValue (feed i s) s.machine.core) = true := hb
  have hr := Cache.running_reset (feed i s) s.machine.core hb'
  have hvc : s.machine.control.valid = true ∧ Machine.committing i s.machine = false := by
    simp only [feed, base_reset, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hr
    exact ⟨hr.1.2, hr.2⟩
  have hf := feed_eq i s h hvc.1 hvc.2
  have hsel : Machine.selected i s.machine = s.machine.control.active := by
    simp [Machine.selected, hvc.2]
  have hm := machine_next i s h
  have hactive := (Cache.running_selection i s.machine (by rw [← hm]; exact hb)).1
  obtain ⟨hd, hs⟩ := step_structure (feed i s) s.machine.core hb'
  have hpc' : (next i s).machine.core.pc = (Reactive.stepValue (feed i s) s.machine.core).pc := rfl
  have hmem : ∀ {w : Nat} (r : Store.Register w),
      (next i s).machine.memory (next i s).machine.control.active r = s.machine.memory s.machine.control.active r := by
    intro w r
    rw [hm, hactive]
    exact Machine.active_memory_preserved i s.machine r
  show (next i s).current = Loader.Store.read ((next i s).machine.memory (next i s).machine.control.active)
    (next i s).machine.core.pc
  simp only [Loader.Store.read, hmem, hpc']
  by_cases hdis : dispatching (feed i s) s.machine.core = true
  · obtain ⟨hpc, _⟩ := hd hdis
    have hsucc : (feed i s).successor =
        Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
          (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.machine.core⟩) :=
      successor_eq i s h hvc.1 hvc.2
    rw [hsel] at hsucc
    show (if (dispatching (feed i s) s.machine.core || !Reactive.runningValue s.machine.core) = true
      then (feed i s).successor else s.current) = _
    rw [if_pos (by rw [hdis]; simp), hpc]
    exact hsucc
  · have hdis' : dispatching (feed i s) s.machine.core = false := by simpa using hdis
    obtain ⟨hpc, _, hrun⟩ := hs hdis'
    show (if (dispatching (feed i s) s.machine.core || !Reactive.runningValue s.machine.core) = true
      then (feed i s).successor else s.current) = _
    rw [if_neg (by rw [hdis', hrun]; decide), hpc]
    exact h.1 hrun

theorem prefetched_next (i : Machine.Inputs) (s : State) (h : Valid s) : Prefetched (next i s) := by
  intro hv
  have hm := machine_next i s h
  rw [hm] at hv
  constructor
  · intro hb b
    have hb' : Reactive.runningValue (Reactive.stepValue (feed i s) s.machine.core) = true := hb
    have hcore : (next i s).machine.core = Reactive.stepValue (feed i s) s.machine.core := rfl
    have hcur : (next i s).current =
        (if (dispatching (feed i s) s.machine.core || !Reactive.runningValue s.machine.core) = true
          then (feed i s).successor else (feed i s).current) := rfl
    have hmem : ∀ {w : Nat} (r : Store.Register w),
        (next i s).machine.memory (next i s).machine.control.active r =
          s.machine.memory (Machine.selected i s.machine) r := by
      intro w r
      rw [hm]
      exact (Storage.Prefetch.selected_memory i s.machine hv r).symm
    show Loader.Store.read (s.machine.memory (Machine.selected i s.machine)) (candidate (feed i s) s.machine.core b) =
      Loader.Store.read ((next i s).machine.memory (next i s).machine.control.active)
        (Storage.Prefetch.candidate (next i s).machine.core (next i s).current b)
    rw [hcore, hcur, candidate_correct (feed i s) s.machine.core b hb']
    simp only [Loader.Store.read, hmem]
  · show (if Machine.committing i s.machine then
        Loader.Store.read (s.machine.memory (Machine.selected i s.machine)) 0 else s.startWord) =
      Loader.Store.read ((next i s).machine.memory (next i s).machine.control.active) 0
    rw [hm]
    by_cases hc : Machine.committing i s.machine = true
    · simp only [hc, if_true, Loader.Store.read, Storage.Prefetch.selected_memory i s.machine hv]
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
        have hmem2 : ∀ {w : Nat} (r : Store.Register w),
            (Machine.next i s.machine).memory (Machine.next i s.machine).control.active r =
              s.machine.memory s.machine.control.active r := by
          intro w r
          rw [hact]
          exact Machine.active_memory_preserved i s.machine r
        rw [(h.2 hv0).2]
        simp only [Loader.Store.read, hmem2]

theorem valid_next (i : Machine.Inputs) (s : State) (h : Valid s) : Valid (next i s) :=
  ⟨cache_valid_next i s h, prefetched_next i s h⟩

theorem initialize_machine_next (i : Machine.Inputs) (s : State) (hi : i.init = true) :
    (next i s).machine = Machine.next i s.machine := by
  simp only [next, Machine.next, Reactive.stepValue, feed, base_reset, hi, Machine.schedulerInput,
    Machine.baseInput, Reactive.Fetch.resolve, Bool.true_or, if_true, Reactive.stopValue,
    Machine.State.mk.injEq, and_true, true_and]
  rfl

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

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    component.trace (next i s) inputs = Cache.referenceComponent.trace (Machine.next i s.machine) inputs := by
  rw [← initialize_machine_next i s hi]
  exact trace_correct (next i s) (initialize_valid i s hi) inputs

/-! ### The decision and the candidates as scheduler expressions

Structural forms over the scheduler's own inputs and registers, for the
netlist: the word being entered is the `successor` input. -/

def kindIs (k : BitVec 3) : Reactive.E 1 := .equal (Reactive.current .kind) (.lit k)

def advancingExpr : Reactive.E 1 :=
  .mux (Reactive.isMode 1) (.zero (.reg .remaining))
    (.mux (Reactive.isMode 2) (.band (kindIs 1) Reactive.ready)
      (.mux (Reactive.isMode 3) (.band (kindIs 2) (.band Reactive.guarded (.zero (.reg .remaining))))
        (.band (kindIs 3) (.band Reactive.guarded (.zero (.reg .remaining))))))

def dispatchingExpr : Reactive.E 1 :=
  .band (.inv (.input .reset)) (.mux Reactive.running advancingExpr (.input .start))

def candidateExpr (b : Bool) : Reactive.E 8 :=
  .mux dispatchingExpr
    (.mux (Execution.bor (.inv (.equal (Reactive.successor .kind) (.lit 2))) (.zero (Reactive.successor .finish)))
      (.sub Reactive.target (.lit 255))
      (.mux (.equal (Reactive.successor .finish) (.lit 1)) (Reactive.successor .yes)
        (if b then Reactive.successor .yes else Reactive.successor .no)))
    (.mux (Execution.bor (.inv (Reactive.isMode 3)) (.zero (Reactive.current .finish)))
      (.sub (.reg .pc) (.lit 255))
      (.mux (.equal (Reactive.current .finish) (.lit 1)) (Reactive.current .yes)
        (if b then Reactive.current .yes else Reactive.current .no)))

theorem kindIs_correct (k : BitVec 3) (i : Reactive.Inputs) (s : Reactive.State) :
    (kindIs k).eval i.values s.values = BitVec.ofBool ((Execution.unpack i.current).kind == k) := by
  simp [kindIs, Expr.eval, Reactive.current_correct, Execution.value, Execution.fieldValue,
    Bool.beq_eq_decide_eq]

private theorem one_and (x : BitVec 1) : 1#1 &&& x = x := by
  revert x
  decide

theorem advancing_correct (i : Reactive.Inputs) (s : Reactive.State) :
    advancingExpr.eval i.values s.values = BitVec.ofBool (advancing i s) := by
  simp only [advancingExpr, Expr.eval, Reactive.isMode, Reactive.State.values, kindIs_correct,
    Reactive.ready_correct, Reactive.guard_correct, advancing, BitVec.ofBool_and_ofBool,
    Reactive.bool_one, Bool.and_assoc]
  by_cases m1 : s.mode = 1 <;> by_cases m2 : s.mode = 2 <;> by_cases m3 : s.mode = 3 <;>
    (simp only [m1, m2, m3, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]; try rfl)

theorem dispatching_correct (i : Reactive.Inputs) (s : Reactive.State) :
    dispatchingExpr.eval i.values s.values = BitVec.ofBool (dispatching i s) := by
  simp only [dispatchingExpr, Expr.eval, Reactive.running_correct, advancing_correct,
    Reactive.Inputs.values, dispatching]
  cases hr : i.reset <;> cases hb : Reactive.runningValue s <;> simp [one_and]

private theorem and_one (x : BitVec 1) : x &&& 1#1 = x := by
  revert x
  decide

set_option linter.unusedSimpArgs false in
theorem candidateExpr_correct (i : Reactive.Inputs) (s : Reactive.State) (b : Bool) :
    (candidateExpr b).eval i.values s.values = candidate i s b := by
  simp only [candidateExpr, Expr.eval, dispatching_correct, Execution.bor, Reactive.successor_correct,
    Reactive.current_correct, Reactive.target_correct, Reactive.isMode, Reactive.State.values,
    Execution.value, Execution.fieldValue, candidate]
  cases hd : dispatching i s
  · simp only [Bool.false_eq_true, ↓reduceIte, Reactive.bool_one]
    by_cases m3 : s.mode = 3#3 <;> by_cases f0 : (Execution.unpack i.current).finish = 0#2 <;>
      by_cases f1 : (Execution.unpack i.current).finish = 1#2 <;> cases b <;>
      simp [m3, f0, f1, one_and, and_one, Reactive.current_correct, Execution.value, Execution.fieldValue]
  · simp only [↓reduceIte, Reactive.bool_one]
    by_cases k2 : (Execution.unpack i.successor).kind = 2#3 <;>
      by_cases f0 : (Execution.unpack i.successor).finish = 0#2 <;>
      by_cases f1 : (Execution.unpack i.successor).finish = 1#2 <;> cases b <;>
      simp [k2, f0, f1, one_and, and_one, Reactive.successor_correct, Execution.value, Execution.fieldValue]

end Pinwheel.Hardware.Storage.Decoupled
