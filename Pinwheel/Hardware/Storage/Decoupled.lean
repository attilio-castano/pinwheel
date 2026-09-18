import Pinwheel.Hardware.Storage.FetchPolicy

/-! The prefetch machine with its addresses decoupled from the next-state decode,
as a fetch policy with three read ports.

`Prefetch` computes the next edge's candidate addresses from the next-state
values of the core, so structurally its address path waits for the fetched
word's validity decode. This organization computes them from what the scheduler
decides on the current edge (`Dispatch.candidate`); when the machine is about to
stop, the addresses are irrelevant and are allowed to be anything. A start-word
register, loaded on commit with word 0 of the newly selected bank, serves the
`start` edge, on which no candidate has been fetched. That read is a third port:
the policy is `Policy 3`, two candidates and word 0.

The refinement of the atomic reference is the generic one (`FetchPolicy`); this
file supplies the policy, its invariant and the three obligations. -/
namespace Pinwheel.Hardware.Storage.Decoupled
open Loader

/-- Two fetched words and the start word. -/
structure Registers where
  /-- The word at the candidate address for a taken (`true`) or untaken (`false`) branch. -/
  fetched : Bool → BitVec 64
  /-- Word 0 of the active bank, loaded on commit. -/
  startWord : BitVec 64

/-- A fetched word chosen by the branch bit while running, the start word at rest. -/
def fed (base : Reactive.Inputs) (core : Reactive.State) (st : Registers) : BitVec 64 :=
  if Reactive.runningValue core then st.fetched (Reactive.Fetch.branchBit ⟨base, core⟩) else st.startWord

def policy : FetchPolicy.Policy 3 Registers where
  fed := fed
  address f core _ _ port :=
    if port = 0 then Dispatch.candidate f core false
    else if port = 1 then Dispatch.candidate f core true else 0
  step _ _ committing st reads :=
    ⟨fun b => reads (if b then 1 else 0), if committing then reads 2 else st.startWord⟩

/-- The invariant: while running, the fetched words are the canonical words of
this edge; while an image is committed, the start word is its word 0. -/
def Owed (s : FetchPolicy.State Registers) : Prop :=
  s.machine.control.valid = true →
    (Reactive.runningValue s.machine.core = true →
      ∀ b, s.policy.fetched b = FetchPolicy.canonical s.machine s.current b) ∧
    s.policy.startWord = Loader.Store.read (s.machine.memory s.machine.control.active) 0

/-- Any policy feeding `fed` covers every dispatch under `Owed`, whatever its ports. -/
theorem covers {p : Nat} (P : FetchPolicy.Policy p Registers) (hfed : P.fed = fed)
    (i : Machine.Inputs) (s : FetchPolicy.State Registers) (h : Owed s)
    (hv : s.machine.control.valid = true) (hc : Machine.committing i s.machine = false) :
    (FetchPolicy.feed P i s).successor =
      Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
        (Reactive.Fetch.Request.address ⟨Cache.base i s.cache, s.machine.core⟩) := by
  rw [FetchPolicy.reference_word i s hc]
  obtain ⟨hf, hw⟩ := h hv
  show P.fed (Cache.base i s.cache) s.machine.core s.policy = _
  rw [hfed]
  unfold fed
  by_cases hr : Reactive.runningValue s.machine.core = true
  · rw [if_pos hr]
    exact hf hr _
  · have hr' : Reactive.runningValue s.machine.core = false := by simpa using hr
    rw [if_neg (by simp [hr']), hw]
    exact (FetchPolicy.canonical_rest _ _ _ hr').symm

theorem preserved (i : Machine.Inputs) (s : FetchPolicy.State Registers) (h : Owed s)
    (hm : (FetchPolicy.next policy i s).machine = Machine.next i s.machine) :
    Owed (FetchPolicy.next policy i s) := by
  intro hv
  refine ⟨fun hb b => ?_, ?_⟩
  · have hread := FetchPolicy.read_next i s hm hb b
    cases b <;> exact hread
  · exact FetchPolicy.start_word_next i s hm s.policy.startWord (fun hv0 => (h hv0).2) hv

theorem initial (i : Machine.Inputs) (s : FetchPolicy.State Registers) (hi : i.init = true)
    (hm : (FetchPolicy.next policy i s).machine = Machine.next i s.machine) :
    Owed (FetchPolicy.next policy i s) := by
  intro hv
  exfalso
  rw [hm, (Machine.initialize_safe i s.machine hi).1] at hv
  simp at hv

def correct : FetchPolicy.Correct policy where
  Inv := Owed
  Rule := fun _ => True
  covers := fun i s _ h hv hc _ => covers policy rfl i s h hv hc
  preserved := fun i s _ h _ hm => preserved i s h hm
  initial := initial

/-! ### The machine and its contract, by name -/

abbrev State := FetchPolicy.State Registers

def next : Machine.Inputs → State → State := FetchPolicy.next policy

def component : Timed.Component Machine.Inputs State (Values Machine.Output) :=
  FetchPolicy.component policy

def Valid (s : State) : Prop := FetchPolicy.Valid correct s

/-- It refines the atomic reference edge for edge, for every input history. -/
def refinement : Timed.Refinement component Cache.referenceComponent :=
  FetchPolicy.refinement correct (fun _ => trivial)

theorem trace_correct (s : State) (h : Valid s) (inputs : List Machine.Inputs) :
    component.trace s inputs = Cache.referenceComponent.trace s.machine inputs :=
  refinement.trace_eq s s.machine ⟨h, rfl⟩ inputs

theorem initialized_trace (s : State) (i : Machine.Inputs) (hi : i.init = true)
    (inputs : List Machine.Inputs) :
    component.trace (next i s) inputs = Cache.referenceComponent.trace (Machine.next i s.machine) inputs :=
  FetchPolicy.initialized_trace correct s i hi inputs (fun _ _ => trivial)

/-! The register updates, for a netlist to be compared against. -/

theorem next_fetched (i : Machine.Inputs) (s : State) (b : Bool) :
    (next i s).policy.fetched b =
      Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
        (Dispatch.candidate (FetchPolicy.feed policy i s) s.machine.core b) := by
  cases b <;> rfl

theorem next_startWord (i : Machine.Inputs) (s : State) :
    (next i s).policy.startWord =
      if Machine.committing i s.machine then
        Loader.Store.read (s.machine.memory (Machine.selected i s.machine)) 0
      else s.policy.startWord := rfl

end Pinwheel.Hardware.Storage.Decoupled
