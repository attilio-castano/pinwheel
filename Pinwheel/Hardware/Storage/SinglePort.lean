import Pinwheel.Hardware.Storage.Decoupled

/-! The decoupled prefetch machine with one read port.

The two candidates of a word differ only for a branching `checked` record. With
one port the machine reads the untaken candidate on the edge that enters a word
and the taken one on the following edge, so a branch can be served on the second
edge after entry at the earliest. That is a condition on programs, not on the
machine: a branching record must not have a zero duration field (`Ready`). Under
that condition on every word ever pushed, the machine refines the atomic
reference edge for edge. The condition is checkable per program; the I²C
programs satisfy it whenever a phase lasts at least two cycles, the UART
receiver does not. -/
namespace Pinwheel.Hardware.Storage.SinglePort
open Loader

/-- A branching record with a zero duration could dispatch on the edge after its
entry, before its taken candidate has been read. -/
def Ready (word : BitVec 64) : Bool :=
  let d := Execution.unpack word
  !(d.kind == 2 && d.finish == 2 && d.duration == 0)

/-- The two candidates of the current word can differ only here. -/
def branching (core : Reactive.State) (word : BitVec 64) : Bool :=
  let d := Execution.unpack word
  core.mode == 3 && !(d.finish == 0) && !(d.finish == 1)

theorem candidate_nonbranching (core : Reactive.State) (word : BitVec 64)
    (h : branching core word = false) :
    Storage.Prefetch.candidate core word true = Storage.Prefetch.candidate core word false := by
  by_cases m3 : core.mode = 3#3 <;> by_cases f0 : (Execution.unpack word).finish = 0#2 <;>
    by_cases f1 : (Execution.unpack word).finish = 1#2 <;>
    simp_all [branching, Storage.Prefetch.candidate]

structure State where
  machine : Machine.State
  current : BitVec 64
  fetched : Bool → BitVec 64
  startWord : BitVec 64
  /-- The current word was entered on the previous edge: its taken candidate is
  not fetched yet. -/
  second : Bool

def State.cache (s : State) : Cache.State := ⟨s.machine, s.current⟩

def branch (i : Machine.Inputs) (s : State) : Bool :=
  Reactive.Fetch.branchBit ⟨Cache.base i s.cache, s.machine.core⟩

/-- Feed the taken word only for a branching word with the branch bit set. -/
def choose (i : Machine.Inputs) (s : State) : Bool := branching s.machine.core s.current && branch i s

def feed (i : Machine.Inputs) (s : State) : Reactive.Inputs :=
  {Cache.base i s.cache with
    successor := if Reactive.runningValue s.machine.core then s.fetched (choose i s) else s.startWord}

/-- The port reads the taken candidate on the edge after a dispatch and the
untaken one on every other edge. -/
def readTaken (f : Reactive.Inputs) (core : Reactive.State) (second : Bool) : Bool :=
  !Storage.Decoupled.dispatching f core && second

def next (i : Machine.Inputs) (s : State) : State :=
  let f := feed i s
  let core := Reactive.stepValue f s.machine.core
  let read := Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
  let taken := readTaken f s.machine.core s.second
  { machine := {Machine.next i s.machine with core := core}
    current := if Storage.Decoupled.dispatching f s.machine.core || !Reactive.runningValue s.machine.core
      then f.successor else s.current
    fetched := fun b => if b == taken then read (Storage.Decoupled.candidate f s.machine.core b) else s.fetched b
    startWord := if Machine.committing i s.machine then read 0 else s.startWord
    second := Storage.Decoupled.dispatching f s.machine.core }

/-! ### Invariants -/

def PrefixReady (m : Store.Image) (n : Nat) : Prop :=
  ∀ k : BitVec 6, k.toNat < n → Ready (m (.word k)) = true

/-- Every word of a committed image, and every word pushed so far, is ready. -/
def ReadyImages (s : Machine.State) : Prop :=
  (s.control.valid = true → PrefixReady (s.memory s.control.active) 64) ∧
  (s.control.pending = true → PrefixReady (s.memory (!s.control.active)) s.control.cursor.toNat)

def Prefetched (s : State) : Prop :=
  s.machine.control.valid = true →
    (Reactive.runningValue s.machine.core = true →
      s.fetched false = Loader.Store.read (s.machine.memory s.machine.control.active)
        (Storage.Prefetch.candidate s.machine.core s.current false) ∧
      (s.second = false → s.fetched true = Loader.Store.read (s.machine.memory s.machine.control.active)
        (Storage.Prefetch.candidate s.machine.core s.current true)) ∧
      (s.second = true → branching s.machine.core s.current = true → s.machine.core.remaining ≠ 0)) ∧
    s.startWord = Loader.Store.read (s.machine.memory s.machine.control.active) 0

def Valid (s : State) : Prop :=
  Cache.Valid s.cache ∧ Machine.Valid s.machine ∧ ReadyImages s.machine ∧ Prefetched s

/-! ### Scheduler facts -/

/-- Without a dispatch, the successor input is not consulted. -/
theorem step_successor_irrelevant (i : Reactive.Inputs) (s : Reactive.State) (x : BitVec 64)
    (h : Storage.Decoupled.dispatching i s = false) :
    Reactive.stepValue {i with successor := x} s = Reactive.stepValue i s := by
  simp only [Storage.Decoupled.dispatching, Bool.and_eq_false_iff, Bool.not_eq_false'] at h
  cases hr : i.reset
  · simp only [hr, Bool.false_eq_true, false_or] at h
    cases hb : Reactive.runningValue s
    · simp only [hb, Bool.false_eq_true, if_false] at h
      simp [Reactive.stepValue, hr, hb, h]
    · simp only [hb, if_true] at h
      simp only [Reactive.stepValue, hr, hb, Bool.false_eq_true, if_false, if_true]
      simp only [Reactive.advanceValue, Reactive.currentKindValue, Storage.Decoupled.advancing] at h ⊢
      by_cases m1 : s.mode = 1
      · by_cases hrem : s.remaining = 0 <;> simp_all [Reactive.decrementValue]
      by_cases m2 : s.mode = 2
      · by_cases hk : (Execution.unpack i.current).kind = 1 <;>
          by_cases hready : Reactive.readyValue i = true <;>
          by_cases hrem : s.remaining = 0 <;>
          simp_all [Reactive.decrementValue, Reactive.stopValue, Reactive.readyValue]
      by_cases m3 : s.mode = 3
      · by_cases hk : (Execution.unpack i.current).kind = 2 <;>
          by_cases hg : Reactive.guardValue i = true <;>
          by_cases hrem : s.remaining = 0 <;>
          simp_all [Reactive.decrementValue, Reactive.stopValue, Reactive.guardValue]
      · by_cases hk : (Execution.unpack i.current).kind = 3 <;>
          by_cases hg : Reactive.guardValue i = true <;>
          by_cases hrem : s.remaining = 0 <;>
          by_cases hw : s.waitLeft = 0 <;>
          simp_all [Reactive.progressValue, Reactive.retryValue, Reactive.stopValue, Reactive.guardValue]
  · simp [Reactive.stepValue, hr, Reactive.stopValue]

/-- A dispatch that keeps the machine running entered a valid word, with the
word's duration as the remaining count. -/
theorem dispatch_entered (i : Reactive.Inputs) (s : Reactive.State)
    (h : Reactive.runningValue (Reactive.stepValue i s) = true)
    (hd : Storage.Decoupled.dispatching i s = true) :
    (Reactive.stepValue i s).remaining = (Execution.unpack i.successor).duration ∧
      Execution.validValue i.successor = true := by
  have hr : i.reset = false := Cache.running_reset i s h
  have entered : Reactive.stepValue i s = Reactive.entryValue i s := by
    simp only [Reactive.stepValue, hr, Bool.false_eq_true, if_false] at h ⊢
    simp only [Storage.Decoupled.dispatching, hr, Bool.not_false, Bool.true_and] at hd
    by_cases hb : Reactive.runningValue s = true
    · simp only [hb, if_true] at h hd ⊢
      have hA := (Storage.Decoupled.advance_structure i s h).1 hd
      rw [hA] at h ⊢
      exact Storage.Decoupled.dispatch_structure i s h
    · have hb' : Reactive.runningValue s = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, if_false] at h hd ⊢
      simp [hd]
  rw [entered] at h ⊢
  simp only [Reactive.entryValue, Reactive.enterValue] at h ⊢
  by_cases hv : Execution.validValue i.successor = true
  · by_cases hk : (Execution.unpack i.successor).kind = 4
    · simp [hv, hk, Reactive.stopValue, Reactive.runningValue] at h
    · rw [if_pos hv, if_neg hk]
      exact ⟨rfl, hv⟩
  · simp [hv, Reactive.stopValue, Reactive.runningValue] at h

/-- A valid `checked` record's finish field is a sequential, jump or branch tag. -/
theorem valid_finish (w : BitVec 64) (hv : Execution.validValue w = true)
    (hk : (Execution.unpack w).kind = 2) : (Execution.unpack w).finish ≠ 3 := by
  intro hf
  simp [Execution.validValue, hk, hf] at hv

/-- A dispatch out of a branching word needs its remaining count at zero. -/
theorem branching_dispatch (i : Reactive.Inputs) (s : Reactive.State)
    (ha : Storage.Decoupled.advancing i s = true) (hb : branching s i.current = true) :
    s.remaining = 0 := by
  simp only [branching, Bool.and_eq_true, beq_iff_eq] at hb
  have ha' := ha
  simp [Storage.Decoupled.advancing, hb.1.1] at ha'
  exact ha'.2

/-! ### Readiness of the images -/

theorem prefix_ready_push (m : Store.Image) (c : BitVec 9) (data : BitVec 64)
    (hp : PrefixReady m c.toNat) (hr : Ready data = true) :
    PrefixReady (Store.tick ⟨true, c, data, 0⟩ m) (c.toNat + 1) := by
  intro k hk
  simp only [Store.tick, Store.offset, Bool.true_and, beq_iff_eq]
  split
  · simpa using hr
  · rename_i he
    apply hp k
    have bound := k.isLt
    have hn : c.toNat ≠ k.toNat := by
      intro hn
      apply he
      apply BitVec.eq_of_toNat_eq
      simpa [Nat.mod_eq_of_lt (by omega : k.toNat < 512)] using hn
    omega

theorem ready_push (i : Machine.Inputs) (s : Machine.State) (h : ReadyImages s)
    (hr : Ready i.data = true)
    (hp : Loader.push (Machine.controlInput i s) s.control = true) : ReadyImages (Machine.next i s) := by
  rcases Loader.push_requires_valid (Machine.controlInput i s) s.control hp with ⟨_, _, _, _, ho, hc, _⟩
  simp only [ReadyImages, Machine.next, Loader.push_next _ _ hp]
  rw [Loader.cursor_increment _ hc]
  refine ⟨?_, ?_⟩
  · simpa [PrefixReady, Machine.memoryInput, Store.tick] using h.1
  · simpa [Machine.memoryInput, hp, ho] using
      prefix_ready_push (s.memory (!s.control.active)) s.control.cursor i.data (h.2 ho) hr

theorem ready_commit (i : Machine.Inputs) (s : Machine.State) (h : ReadyImages s)
    (hc : Machine.committing i s = true) : ReadyImages (Machine.next i s) := by
  rcases Loader.commit_requires_complete (Machine.controlInput i s) s.control hc with ⟨_, _, _, _, ho, he⟩
  simp only [ReadyImages, Machine.next, Loader.commit_next _ _ hc]
  refine ⟨?_, by simp⟩
  intro _ k hk
  change Ready ((Machine.next i s).memory (!s.control.active) (.word k)) = true
  rw [Machine.commit_does_not_write i s hc]
  exact h.2 ho k (by simpa [he] using Nat.lt_trans hk (by decide : 64 < 322))

theorem ready_next (i : Machine.Inputs) (s : Machine.State) (h : ReadyImages s)
    (hr : Ready i.data = true) : ReadyImages (Machine.next i s) := by
  by_cases hp : Loader.push (Machine.controlInput i s) s.control = true
  · exact ready_push i s h hr hp
  by_cases hc : Machine.committing i s = true
  · exact ready_commit i s h hc
  simp only [ReadyImages, Machine.next, Loader.next, hp,
    show ¬Loader.commit (Machine.controlInput i s) s.control = true from hc, Bool.false_eq_true, ↓reduceIte]
  repeat' (first | (split <;> try simp_all [PrefixReady, Machine.memoryInput, Store.tick, ReadyImages]) | assumption)

/-- Every word of the active bank is ready while an image is committed. -/
theorem read_ready (s : Machine.State) (h : ReadyImages s) (hv : s.control.valid = true) (a : BitVec 8) :
    Ready (Loader.Store.read (s.memory s.control.active) a) = true :=
  h.1 hv _ (s.memory s.control.active (.index a)).isLt

/-! ### Refinement -/

theorem base_reset (i : Machine.Inputs) (s : State) :
    (Cache.base i s.cache).reset =
      (i.init || i.reset || !s.machine.control.valid || Machine.committing i s.machine) := rfl

theorem dispatching_feed (i : Machine.Inputs) (s : State) :
    Storage.Decoupled.dispatching (feed i s) s.machine.core =
      Storage.Decoupled.dispatching (Cache.feed i s.cache) s.machine.core := by
  rfl

/-- On a dispatching edge with an image committed and no commit, the fed successor
is the word the reference reads. -/
theorem successor_eq (i : Machine.Inputs) (s : State) (h : Valid s)
    (hv : s.machine.control.valid = true) (hc : Machine.committing i s.machine = false)
    (hd : Storage.Decoupled.dispatching (feed i s) s.machine.core = true) :
    (feed i s).successor =
      Loader.Store.read (s.cache.machine.memory (Machine.selected i s.cache.machine))
        (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.cache.machine.core⟩) := by
  have hsel : Machine.selected i s.machine = s.machine.control.active := by
    simp [Machine.selected, hc]
  obtain ⟨hf, hw⟩ := h.2.2.2 hv
  change (if Reactive.runningValue s.machine.core then s.fetched (choose i s) else s.startWord) =
    Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
      (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.machine.core⟩)
  rw [hsel, Reactive.Fetch.address_choice ⟨Cache.base i s.cache, s.machine.core⟩,
    Storage.Prefetch.candidate_correct, Storage.Prefetch.candidate_correct]
  have hcur : (Cache.base i s.cache).current = s.current := rfl
  rw [hcur]
  by_cases hr : Reactive.runningValue s.machine.core = true
  · rw [if_pos hr]
    obtain ⟨h0, h1, h2⟩ := hf hr
    have hadv : Storage.Decoupled.advancing (feed i s) s.machine.core = true := by
      have hd' := hd
      simp only [Storage.Decoupled.dispatching, hr, if_true, Bool.and_eq_true] at hd'
      exact hd'.2
    have hbranch : Reactive.Fetch.branchBit ⟨Cache.base i s.cache, s.machine.core⟩ = branch i s := rfl
    rw [hbranch]
    by_cases hb : branching s.machine.core s.current = true
    · have hsecond : s.second = false := by
        cases hs : s.second
        · rfl
        · exact absurd (branching_dispatch (feed i s) s.machine.core hadv hb) (h2 hs hb)
      cases hbr : branch i s
      · simp [choose, hbr, h0]
      · simp [choose, hb, hbr, h1 hsecond]
    · have hb' : branching s.machine.core s.current = false := by simpa using hb
      cases hbr : branch i s
      · simp [choose, hbr, h0]
      · simp [choose, hb', hbr, h0, candidate_nonbranching s.machine.core s.current hb']
  · have hr' : Reactive.runningValue s.machine.core = false := by simpa using hr
    rw [if_neg (by simp [hr']), hw]
    simp [Storage.Prefetch.candidate, hr']

theorem step_eq (i : Machine.Inputs) (s : State) (h : Valid s) :
    Reactive.stepValue (feed i s) s.machine.core = Reactive.stepValue (Cache.feed i s.cache) s.machine.core := by
  by_cases hv : s.machine.control.valid = true
  · by_cases hc : Machine.committing i s.machine = false
    · by_cases hd : Storage.Decoupled.dispatching (feed i s) s.machine.core = true
      · have hs := successor_eq i s h hv hc hd
        have : feed i s = Cache.feed i s.cache := by
          simp only [feed] at hs ⊢
          simp only [Cache.feed, Reactive.Fetch.resolve, hs]
        rw [this]
      · have hd' : Storage.Decoupled.dispatching (Cache.feed i s.cache) s.machine.core = false := by
          rw [← dispatching_feed]; simpa using hd
        have : feed i s = {Cache.feed i s.cache with successor := (feed i s).successor} := by
          simp only [feed, Cache.feed, Reactive.Fetch.resolve]
        rw [this, step_successor_irrelevant _ _ _ hd']
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

/-- Facts available on an edge after which the machine runs. -/
theorem running_facts (i : Machine.Inputs) (s : State) (h : Valid s)
    (hb : Reactive.runningValue (Reactive.stepValue (feed i s) s.machine.core) = true) :
    s.machine.control.valid = true ∧ Machine.committing i s.machine = false ∧
      Machine.selected i s.machine = s.machine.control.active ∧
      (Machine.next i s.machine).control.active = s.machine.control.active := by
  have hr := Cache.running_reset (feed i s) s.machine.core hb
  have hvc : s.machine.control.valid = true ∧ Machine.committing i s.machine = false := by
    simp only [feed, base_reset, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hr
    exact ⟨hr.1.2, hr.2⟩
  have hsel : Machine.selected i s.machine = s.machine.control.active := by
    simp [Machine.selected, hvc.2]
  have hm := machine_next i s h
  have hactive := (Cache.running_selection i s.machine (by rw [← hm]; exact hb)).1
  exact ⟨hvc.1, hvc.2, hsel, hactive⟩

theorem cache_valid_next (i : Machine.Inputs) (s : State) (h : Valid s) : Cache.Valid (next i s).cache := by
  intro hb
  have hb' : Reactive.runningValue (Reactive.stepValue (feed i s) s.machine.core) = true := hb
  obtain ⟨hv, hc, hsel, hactive⟩ := running_facts i s h hb'
  have hm := machine_next i s h
  obtain ⟨hd, hs⟩ := Storage.Decoupled.step_structure (feed i s) s.machine.core hb'
  have hpc' : (next i s).machine.core.pc = (Reactive.stepValue (feed i s) s.machine.core).pc := rfl
  have hmem : ∀ {w : Nat} (r : Store.Register w),
      (next i s).machine.memory (next i s).machine.control.active r = s.machine.memory s.machine.control.active r := by
    intro w r
    rw [hm, hactive]
    exact Machine.active_memory_preserved i s.machine r
  show (next i s).current = Loader.Store.read ((next i s).machine.memory (next i s).machine.control.active)
    (next i s).machine.core.pc
  simp only [Loader.Store.read, hmem, hpc']
  by_cases hdis : Storage.Decoupled.dispatching (feed i s) s.machine.core = true
  · obtain ⟨hpc, _⟩ := hd hdis
    have hsucc : (feed i s).successor =
        Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
          (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.machine.core⟩) :=
      successor_eq i s h hv hc hdis
    rw [hsel] at hsucc
    show (if (Storage.Decoupled.dispatching (feed i s) s.machine.core || !Reactive.runningValue s.machine.core) = true
      then (feed i s).successor else s.current) = _
    rw [if_pos (by rw [hdis]; simp), hpc]
    exact hsucc
  · have hdis' : Storage.Decoupled.dispatching (feed i s) s.machine.core = false := by simpa using hdis
    obtain ⟨hpc, _, hrun⟩ := hs hdis'
    show (if (Storage.Decoupled.dispatching (feed i s) s.machine.core || !Reactive.runningValue s.machine.core) = true
      then (feed i s).successor else s.current) = _
    rw [if_neg (by rw [hdis', hrun]; decide), hpc]
    exact h.1 hrun

/-- The canonical candidates depend on the core only through its mode and address. -/
theorem candidate_congr (core core' : Reactive.State) (word : BitVec 64) (b : Bool)
    (hmode : core'.mode = core.mode) (hpc : core'.pc = core.pc) :
    Storage.Prefetch.candidate core' word b = Storage.Prefetch.candidate core word b := by
  have hrun : Reactive.runningValue core' = Reactive.runningValue core := by
    simp [Reactive.runningValue, hmode]
  simp only [Storage.Prefetch.candidate, hrun, hmode, hpc]

/-- The word a dispatching edge enters is a word of the active bank. -/
theorem entered_word (i : Machine.Inputs) (s : State) (h : Valid s)
    (hv : s.machine.control.valid = true)
    (hd : Storage.Decoupled.dispatching (feed i s) s.machine.core = true) :
    ∃ a, (feed i s).successor = Loader.Store.read (s.machine.memory s.machine.control.active) a := by
  obtain ⟨hf, hw⟩ := h.2.2.2 hv
  change (∃ a, (if Reactive.runningValue s.machine.core then s.fetched (choose i s) else s.startWord) =
    Loader.Store.read (s.machine.memory s.machine.control.active) a)
  by_cases hr : Reactive.runningValue s.machine.core = true
  · obtain ⟨h0, h1, h2⟩ := hf hr
    have hadv : Storage.Decoupled.advancing (feed i s) s.machine.core = true := by
      have hd' := hd
      simp only [Storage.Decoupled.dispatching, hr, if_true, Bool.and_eq_true] at hd'
      exact hd'.2
    rw [if_pos hr]
    cases hch : choose i s
    · exact ⟨_, h0⟩
    · have hb : branching s.machine.core s.current = true := by
        have hch' := hch
        simp only [choose, Bool.and_eq_true] at hch'
        exact hch'.1
      have hsecond : s.second = false := by
        cases hs : s.second
        · rfl
        · exact absurd (branching_dispatch (feed i s) s.machine.core hadv hb) (h2 hs hb)
      exact ⟨_, h1 hsecond⟩
  · have hr' : Reactive.runningValue s.machine.core = false := by simpa using hr
    rw [if_neg (by simp [hr'])]
    exact ⟨0, hw⟩

theorem prefetched_next (i : Machine.Inputs) (s : State) (h : Valid s) : Prefetched (next i s) := by
  intro hv'
  have hm := machine_next i s h
  rw [hm] at hv'
  constructor
  · intro hb
    have hb' : Reactive.runningValue (Reactive.stepValue (feed i s) s.machine.core) = true := hb
    obtain ⟨hv, hc, hsel, hactive⟩ := running_facts i s h hb'
    obtain ⟨hd, hs⟩ := Storage.Decoupled.step_structure (feed i s) s.machine.core hb'
    have hmem : ∀ {w : Nat} (r : Store.Register w),
        (next i s).machine.memory (next i s).machine.control.active r =
          s.machine.memory s.machine.control.active r := by
      intro w r
      rw [hm, hactive]
      exact Machine.active_memory_preserved i s.machine r
    have hcore : (next i s).machine.core = Reactive.stepValue (feed i s) s.machine.core := rfl
    have hcur : (next i s).current =
        (if (Storage.Decoupled.dispatching (feed i s) s.machine.core || !Reactive.runningValue s.machine.core) = true
          then (feed i s).successor else (feed i s).current) := rfl
    have hcand := Storage.Decoupled.candidate_correct (feed i s) s.machine.core
    -- the read of this edge, as the next state's canonical candidate
    have hread : ∀ b, Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
        (Storage.Decoupled.candidate (feed i s) s.machine.core b) =
        Loader.Store.read ((next i s).machine.memory (next i s).machine.control.active)
          (Storage.Prefetch.candidate (next i s).machine.core (next i s).current b) := by
      intro b
      rw [hsel, hcore, hcur, hcand b hb']
      simp only [Loader.Store.read, hmem]
    -- without a dispatch the canonical candidates do not move
    have hstay : Storage.Decoupled.dispatching (feed i s) s.machine.core = false →
        ∀ b, Loader.Store.read (s.machine.memory s.machine.control.active)
          (Storage.Prefetch.candidate s.machine.core s.current b) =
        Loader.Store.read ((next i s).machine.memory (next i s).machine.control.active)
          (Storage.Prefetch.candidate (next i s).machine.core (next i s).current b) := by
      intro hdis b
      obtain ⟨hpc, hmode, hrun⟩ := hs hdis
      rw [hcore, hcur, if_neg (by rw [hdis, hrun]; decide), candidate_congr _ _ _ _ hmode hpc]
      simp only [Loader.Store.read, hmem]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · -- the untaken word
      show (if (false == readTaken (feed i s) s.machine.core s.second) then
        Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
          (Storage.Decoupled.candidate (feed i s) s.machine.core false) else s.fetched false) = _
      by_cases ht : readTaken (feed i s) s.machine.core s.second = true
      · rw [if_neg (by simp [ht])]
        have hdis : Storage.Decoupled.dispatching (feed i s) s.machine.core = false := by
          have ht' := ht
          simp only [readTaken, Bool.and_eq_true, Bool.not_eq_true'] at ht'
          exact ht'.1
        have hrun := (hs hdis).2.2
        rw [((h.2.2.2 hv).1 hrun).1]
        exact hstay hdis false
      · rw [if_pos (by simpa using ht)]
        exact hread false
    · -- the taken word, once fetched
      intro hsecond
      have hdis : Storage.Decoupled.dispatching (feed i s) s.machine.core = false := hsecond
      have hrun := (hs hdis).2.2
      obtain ⟨h0, h1, h2⟩ := (h.2.2.2 hv).1 hrun
      show (if (true == readTaken (feed i s) s.machine.core s.second) then
        Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
          (Storage.Decoupled.candidate (feed i s) s.machine.core true) else s.fetched true) = _
      cases hsec : s.second
      · rw [if_neg (by simp [readTaken, hdis]), h1 hsec]
        exact hstay hdis true
      · rw [if_pos (by simp [readTaken, hdis])]
        exact hread true
    · -- a branching word just entered still has its duration to count
      intro hsecond hbranch
      have hdis : Storage.Decoupled.dispatching (feed i s) s.machine.core = true := hsecond
      obtain ⟨hrem, hvalid⟩ := dispatch_entered (feed i s) s.machine.core hb' hdis
      have hmode := (hd hdis).2
      rw [hcur, if_pos (by rw [hdis]; simp)] at hbranch
      simp only [branching, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hbranch
      obtain ⟨⟨hm3, hf0⟩, hf1⟩ := hbranch
      have hk : (Execution.unpack (feed i s).successor).kind = 2 := hmode.mp (by rw [← hcore]; exact hm3)
      have hf3 := valid_finish _ hvalid hk
      have hf2 : (Execution.unpack (feed i s).successor).finish = 2 := by
        generalize (Execution.unpack (feed i s).successor).finish = f at hf0 hf1 hf3
        revert f
        decide
      obtain ⟨a, ha⟩ := entered_word i s h hv hdis
      have hready := read_ready s.machine h.2.2.1 hv a
      rw [← ha] at hready
      simp only [Ready, hk, hf2, Bool.not_eq_true', beq_self_eq_true, Bool.true_and,
        beq_eq_false_iff_ne] at hready
      rw [hcore, hrem]
      simpa using hready
  · show (if Machine.committing i s.machine then
        Loader.Store.read (s.machine.memory (Machine.selected i s.machine)) 0 else s.startWord) =
      Loader.Store.read ((next i s).machine.memory (next i s).machine.control.active) 0
    rw [hm]
    by_cases hc : Machine.committing i s.machine = true
    · simp only [hc, if_true, Loader.Store.read, Storage.Prefetch.selected_memory i s.machine hv']
    · have hc' : Machine.committing i s.machine = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, if_false]
      by_cases hi : i.init = true
      · exfalso
        have : (Machine.next i s.machine).control = {} := (Machine.initialize_safe i s.machine hi).1
        simp [this] at hv'
      · have ha := (Loader.no_commit_preserves_selection (Machine.controlInput i s.machine) s.machine.control
          (by simpa [Machine.controlInput] using hi) hc')
        have hact : (Machine.next i s.machine).control.active = s.machine.control.active := ha.1
        have hv0 : s.machine.control.valid = true := by
          have hvalid : (Machine.next i s.machine).control.valid = s.machine.control.valid := ha.2
          rw [hvalid] at hv'
          exact hv'
        have hmem2 : ∀ {w : Nat} (r : Store.Register w),
            (Machine.next i s.machine).memory (Machine.next i s.machine).control.active r =
              s.machine.memory s.machine.control.active r := by
          intro w r
          rw [hact]
          exact Machine.active_memory_preserved i s.machine r
        rw [(h.2.2.2 hv0).2]
        simp only [Loader.Store.read, hmem2]

theorem valid_next (i : Machine.Inputs) (s : State) (h : Valid s) (hr : Ready i.data = true) :
    Valid (next i s) := by
  have hm := machine_next i s h
  refine ⟨cache_valid_next i s h, ?_, ?_, prefetched_next i s h⟩
  · rw [hm]
    exact Machine.valid_next i s.machine h.2.1
  · rw [hm]
    exact ready_next i s.machine h.2.2.1 hr

theorem initialize_machine_next (i : Machine.Inputs) (s : State) (hi : i.init = true) :
    (next i s).machine = Machine.next i s.machine := by
  simp only [next, Machine.next, Reactive.stepValue, feed, base_reset, hi, Machine.schedulerInput,
    Machine.baseInput, Reactive.Fetch.resolve, Bool.true_or, if_true, Reactive.stopValue,
    Machine.State.mk.injEq, and_true, true_and]
  rfl

theorem initialize_valid (i : Machine.Inputs) (s : State) (hi : i.init = true) : Valid (next i s) := by
  have hr : (Cache.base i s.cache).reset = true := by simp [base_reset, hi]
  have hm := initialize_machine_next i s hi
  have hctl : (Machine.next i s.machine).control = {} := (Machine.initialize_safe i s.machine hi).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Cache.idle_valid
    show Reactive.runningValue (Reactive.stepValue (feed i s) s.machine.core) = false
    simp [Reactive.stepValue, feed, hr, Reactive.stopValue, Reactive.runningValue]
  · rw [hm]
    exact Machine.initialize_valid i s.machine hi
  · rw [hm]
    simp [ReadyImages, hctl]
  · intro hv
    exfalso
    rw [hm, hctl] at hv
    simp at hv

def component : Timed.Component Machine.Inputs State (Values Machine.Output) :=
  ⟨next, fun i s => Cache.circuit.observe i.values s.cache.values⟩

/-- One edge of two traces agrees when both observations and the tails do. -/
theorem trace_cons {I S T O : Type} (impl : Timed.Component I S O) (spec : Timed.Component I T O)
    (i : I) (s : S) (t : T) (rest : List I)
    (h1 : impl.observe i s = spec.observe i t)
    (h2 : impl.observe i (impl.step i s) = spec.observe i (spec.step i t))
    (h3 : impl.trace (impl.step i s) rest = spec.trace (spec.step i t) rest) :
    impl.trace s (i :: rest) = spec.trace t (i :: rest) := by
  simp only [Timed.Component.trace, Timed.Component.edge, h1, h2, h3]

/-- Every pre/post-edge observation is the reference machine's, on any history
whose pushed words are ready. -/
theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs)
    (hr : ∀ i ∈ inputs, Ready i.data = true) :
    component.trace s inputs = Cache.referenceComponent.trace s.machine inputs := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have hi := hr i (List.mem_cons_self ..)
    have hv := valid_next i s h hi
    have hm := machine_next i s h
    refine trace_cons component Cache.referenceComponent i s s.machine rest ?_ ?_ ?_
    · funext w o
      exact Cache.output_correct i s.cache h.1 o
    · funext w o
      exact (Cache.output_correct i (next i s).cache hv.1 o).trans
        (congrArg (fun m : Machine.State => Machine.circuit.observe i.values m.values o) hm)
    · exact (ih (next i s) hv (fun j hj => hr j (List.mem_cons_of_mem i hj))).trans
        (congrArg (fun m => Cache.referenceComponent.trace m rest) hm)

end Pinwheel.Hardware.Storage.SinglePort
