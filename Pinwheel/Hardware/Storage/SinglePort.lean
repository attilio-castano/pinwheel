import Pinwheel.Hardware.Storage.FetchPolicy
import Pinwheel.Hardware.Storage.ImageRule
import Pinwheel.Hardware.Storage.Admission

/-! The decoupled prefetch organization with one read port.

The two candidates of a word differ only for a branching `checked` record
(`Dispatch.candidate_nonbranching`). With one port the policy reads the untaken
candidate on the edge that enters a word and the taken one on the following
edge, so a branch can be served on the second edge after entry at the earliest.
A commit edge resets the scheduler, so the same port reads word 0 for the start
word then: one read tree in all. The price is a condition on programs, not on
the machine: a branching record must not have a zero duration field (`Ready`).
It is the policy's `Rule`, carried by the loader as an `ImageRule`; under it the
generic refinement applies. The I²C programs satisfy it whenever a phase lasts
at least two cycles, the UART receiver as compiled does not. -/
namespace Pinwheel.Hardware.Storage.SinglePort
open Loader

/-- A branching record with a zero duration could dispatch on the edge after its
entry, before its taken candidate has been read. -/
def Ready (word : BitVec 64) : Bool :=
  let d := Execution.unpack word
  !(d.kind == 2 && d.finish == 2 && d.duration == 0)

structure Registers where
  fetched : Bool → BitVec 64
  startWord : BitVec 64
  /-- The current word was entered on the previous edge: its taken candidate is
  not fetched yet. -/
  second : Bool

/-- The port reads the taken candidate on the edge after a dispatch and the
untaken one on every other edge. -/
def readTaken (f : Reactive.Inputs) (core : Reactive.State) (st : Registers) : Bool :=
  !Dispatch.dispatching f core && st.second

/-- Feed the taken word only for a branching word with the branch bit set. -/
def choose (base : Reactive.Inputs) (core : Reactive.State) : Bool :=
  Dispatch.branching core base.current && Reactive.Fetch.branchBit ⟨base, core⟩

def policy : FetchPolicy.Policy 1 Registers where
  fed base core st := if Reactive.runningValue core then st.fetched (choose base core) else st.startWord
  address f core committing st _ :=
    if committing then 0 else Dispatch.candidate f core (readTaken f core st)
  step f core committing st reads :=
    { fetched := fun b => if b == readTaken f core st then reads 0 else st.fetched b
      startWord := if committing then reads 0 else st.startWord
      second := Dispatch.dispatching f core }

/-- The untaken word is always owed while running, the taken one once the word
has been current for an edge; a branching word entered on the previous edge
still has its duration to count, so it does not dispatch before that. -/
def Owed (s : FetchPolicy.State Registers) : Prop :=
  s.machine.control.valid = true →
    (Reactive.runningValue s.machine.core = true →
      s.policy.fetched false = FetchPolicy.canonical s.machine s.current false ∧
      (s.policy.second = false →
        s.policy.fetched true = FetchPolicy.canonical s.machine s.current true) ∧
      (s.policy.second = true → Dispatch.branching s.machine.core s.current = true →
        s.machine.core.remaining ≠ 0)) ∧
    s.policy.startWord = Loader.Store.read (s.machine.memory s.machine.control.active) 0

def Inv (s : FetchPolicy.State Registers) : Prop := ImageRule.Images Ready s.machine ∧ Owed s

/-- A dispatch out of a branching word happens with its taken word fetched. -/
theorem covers (i : Machine.Inputs) (s : FetchPolicy.State Registers) (h : Inv s)
    (hv : s.machine.control.valid = true) (hc : Machine.committing i s.machine = false)
    (hd : Dispatch.dispatching (FetchPolicy.feed policy i s) s.machine.core = true) :
    (FetchPolicy.feed policy i s).successor =
      Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
        (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.machine.core⟩) := by
  rw [FetchPolicy.reference_word i s hc]
  obtain ⟨hf, hw⟩ := h.2 hv
  show (if Reactive.runningValue s.machine.core
    then s.policy.fetched (Dispatch.branching s.machine.core s.current && FetchPolicy.branch i s)
    else s.policy.startWord) = _
  by_cases hr : Reactive.runningValue s.machine.core = true
  · rw [if_pos hr]
    obtain ⟨h0, h1, h2⟩ := hf hr
    have hadv : Dispatch.advancing (FetchPolicy.feed policy i s) s.machine.core = true := by
      have hd' := hd
      simp only [Dispatch.dispatching, hr, if_true, Bool.and_eq_true] at hd'
      exact hd'.2
    by_cases hb : Dispatch.branching s.machine.core s.current = true
    · have hsecond : s.policy.second = false := by
        cases hs : s.policy.second
        · rfl
        · exact absurd (Dispatch.branching_dispatch (FetchPolicy.feed policy i s) s.machine.core hadv hb)
            (h2 hs hb)
      cases hbr : FetchPolicy.branch i s
      · simp [hb, h0]
      · simp [hb, h1 hsecond]
    · have hb' : Dispatch.branching s.machine.core s.current = false := by simpa using hb
      have hsame : FetchPolicy.canonical s.machine s.current true =
          FetchPolicy.canonical s.machine s.current false := by
        unfold FetchPolicy.canonical
        rw [Dispatch.candidate_nonbranching s.machine.core s.current hb']
      cases hbr : FetchPolicy.branch i s
      · simp [hb', h0]
      · simp [hb', h0, hsame]
  · have hr' : Reactive.runningValue s.machine.core = false := by simpa using hr
    rw [if_neg (by simp [hr']), hw]
    exact (FetchPolicy.canonical_rest _ _ _ hr').symm

theorem preserved (i : Machine.Inputs) (s : FetchPolicy.State Registers)
    (h : Inv s) (hrule : i.command = 2 → Ready i.data = true)
    (hm : (FetchPolicy.next policy i s).machine = Machine.next i s.machine) :
    Inv (FetchPolicy.next policy i s) := by
  refine ⟨by rw [hm]; exact ImageRule.preserved Ready i s.machine h.1 hrule, ?_⟩
  intro hv'
  -- what the single port delivers on an edge that does not commit
  have hport : Machine.committing i s.machine = false →
      FetchPolicy.reads policy i s 0 =
        Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
          (Dispatch.candidate (FetchPolicy.feed policy i s) s.machine.core
            (readTaken (FetchPolicy.feed policy i s) s.machine.core s.policy)) := by
    intro hc
    rw [FetchPolicy.reads_eq]
    show Loader.Store.read _ (if Machine.committing i s.machine then 0 else _) = _
    rw [hc]
    rfl
  refine ⟨fun hb => ?_, ?_⟩
  · have hb' : Reactive.runningValue
        (Reactive.stepValue (FetchPolicy.feed policy i s) s.machine.core) = true := hb
    obtain ⟨hv, hc, hsel, _⟩ := FetchPolicy.running_facts i s hm hb'
    obtain ⟨hd, hs⟩ := Dispatch.step_structure (FetchPolicy.feed policy i s) s.machine.core hb'
    have hread := FetchPolicy.read_next i s hm hb'
    have hstay := FetchPolicy.stay i s hm hb'
    refine ⟨?_, ?_, ?_⟩
    · -- the untaken word
      show (if (false == readTaken (FetchPolicy.feed policy i s) s.machine.core s.policy)
        then FetchPolicy.reads policy i s 0 else s.policy.fetched false) = _
      by_cases ht : readTaken (FetchPolicy.feed policy i s) s.machine.core s.policy = true
      · rw [if_neg (by simp [ht])]
        have hdis : Dispatch.dispatching (FetchPolicy.feed policy i s) s.machine.core = false := by
          have ht' := ht
          simp only [readTaken, Bool.and_eq_true, Bool.not_eq_true'] at ht'
          exact ht'.1
        have hrun := (hs hdis).2.2
        rw [((h.2 hv).1 hrun).1]
        exact hstay hdis false
      · have ht' : readTaken (FetchPolicy.feed policy i s) s.machine.core s.policy = false := by
          simpa using ht
        rw [if_pos (by simp [ht']), hport hc, ht']
        exact hread false
    · -- the taken word, once fetched
      intro hsecond
      have hdis : Dispatch.dispatching (FetchPolicy.feed policy i s) s.machine.core = false := hsecond
      have hrun := (hs hdis).2.2
      obtain ⟨_, h1, _⟩ := (h.2 hv).1 hrun
      show (if (true == readTaken (FetchPolicy.feed policy i s) s.machine.core s.policy)
        then FetchPolicy.reads policy i s 0 else s.policy.fetched true) = _
      cases hsec : s.policy.second
      · rw [if_neg (by simp [readTaken, hdis, hsec]), h1 hsec]
        exact hstay hdis true
      · have ht : readTaken (FetchPolicy.feed policy i s) s.machine.core s.policy = true := by
          simp [readTaken, hdis, hsec]
        rw [if_pos (by simp [ht]), hport hc, ht]
        exact hread true
    · -- a branching word just entered still has its duration to count
      intro hsecond hbranch
      have hdis : Dispatch.dispatching (FetchPolicy.feed policy i s) s.machine.core = true := hsecond
      obtain ⟨hrem, hvalid⟩ := Dispatch.dispatch_entered (FetchPolicy.feed policy i s) s.machine.core hb' hdis
      have hmode := (hd hdis).2
      have hcore : (FetchPolicy.next policy i s).machine.core =
          Reactive.stepValue (FetchPolicy.feed policy i s) s.machine.core := rfl
      have hcur : (FetchPolicy.next policy i s).current = (FetchPolicy.feed policy i s).successor := by
        show (if (Dispatch.dispatching (FetchPolicy.feed policy i s) s.machine.core ||
          !Reactive.runningValue s.machine.core) = true then _ else _) = _
        rw [if_pos (by rw [hdis]; simp)]
      rw [hcur] at hbranch
      simp only [Dispatch.branching, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
        beq_eq_false_iff_ne] at hbranch
      obtain ⟨⟨hm3, hf0⟩, hf1⟩ := hbranch
      have hk : (Execution.unpack (FetchPolicy.feed policy i s).successor).kind = 2 :=
        hmode.mp (by rw [← hcore]; exact hm3)
      have hf3 := Dispatch.valid_finish _ hvalid hk
      have hf2 : (Execution.unpack (FetchPolicy.feed policy i s).successor).finish = 2 := by
        generalize (Execution.unpack (FetchPolicy.feed policy i s).successor).finish = f at hf0 hf1 hf3
        revert f
        decide
      -- the entered word is a word of the active bank, hence ready
      have hword := covers i s h hv hc hdis
      rw [hsel] at hword
      have hready := ImageRule.read_satisfies Ready s.machine h.1 hv
        (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.machine.core⟩)
      rw [← hword] at hready
      simp only [Ready, hk, hf2, Bool.not_eq_true', beq_self_eq_true, Bool.true_and,
        beq_eq_false_iff_ne] at hready
      rw [hcore, hrem]
      simpa using hready
  · -- the start word: the port reads word 0 on a commit
    have hstart : (FetchPolicy.next policy i s).policy.startWord =
        (if Machine.committing i s.machine then
          Loader.Store.read (s.machine.memory (Machine.selected i s.machine)) 0 else s.policy.startWord) := by
      show (if Machine.committing i s.machine then FetchPolicy.reads policy i s 0 else _) = _
      cases hcm : Machine.committing i s.machine
      · rfl
      · simp only [if_true]
        rw [FetchPolicy.reads_eq]
        show Loader.Store.read _ (if Machine.committing i s.machine then 0 else _) = _
        rw [hcm]
        rfl
    rw [hstart]
    exact FetchPolicy.start_word_next i s hm s.policy.startWord (fun hv0 => (h.2 hv0).2) hv'

theorem initial (i : Machine.Inputs) (s : FetchPolicy.State Registers) (hi : i.init = true)
    (hm : (FetchPolicy.next policy i s).machine = Machine.next i s.machine) :
    Inv (FetchPolicy.next policy i s) := by
  refine ⟨by rw [hm]; exact ImageRule.initialized Ready i s.machine hi, ?_⟩
  intro hv
  exfalso
  rw [hm, (Machine.initialize_safe i s.machine hi).1] at hv
  simp at hv

def correct : FetchPolicy.Correct policy where
  Inv := Inv
  Rule := fun i => i.command = 2 → Ready i.data = true
  covers := fun i s _ h hv hc hd => covers i s h hv hc hd
  preserved := fun i s _ h hr hm => preserved i s h hr hm
  initial := initial

/-! ### The machine and its contract, by name -/

abbrev State := FetchPolicy.State Registers

def next : Machine.Inputs → State → State := FetchPolicy.next policy

def component : Timed.Component Machine.Inputs State (Values Machine.Output) :=
  FetchPolicy.component policy

def Valid (s : State) : Prop := FetchPolicy.Valid correct s

/-! The register updates, for a netlist to be compared against. -/

theorem next_fetched (i : Machine.Inputs) (s : State) (b : Bool) :
    (next i s).policy.fetched b =
      if b == readTaken (FetchPolicy.feed policy i s) s.machine.core s.policy
      then FetchPolicy.reads policy i s 0 else s.policy.fetched b := rfl

theorem next_startWord (i : Machine.Inputs) (s : State) :
    (next i s).policy.startWord =
      if Machine.committing i s.machine then FetchPolicy.reads policy i s 0 else s.policy.startWord := rfl

theorem next_second (i : Machine.Inputs) (s : State) :
    (next i s).policy.second = Dispatch.dispatching (FetchPolicy.feed policy i s) s.machine.core := rfl

/-- Every pre/post-edge observation is the reference machine's, on any history
whose pushed words are ready. -/
theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs)
    (hr : ∀ i ∈ inputs, i.command = 2 → Ready i.data = true) :
    component.trace s inputs = Cache.referenceComponent.trace s.machine inputs :=
  FetchPolicy.trace_correct correct s h inputs hr

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) (hr : ∀ j ∈ inputs, j.command = 2 → Ready j.data = true) :
    component.trace (next i s) inputs = Cache.referenceComponent.trace (Machine.next i s.machine) inputs :=
  FetchPolicy.initialized_trace correct s i hi inputs hr

/-- Behind a push filter that rejects unready words — as the capacity check rejects
words that do not fit — the machine refines the reference behind the same filter
for every input history. -/
def admitted : Timed.Refinement (component.precompose (Admission.admit Ready))
    (Cache.referenceComponent.precompose (Admission.admit Ready)) :=
  Admission.discharge Ready (FetchPolicy.ruleRefinement correct)

end Pinwheel.Hardware.Storage.SinglePort
