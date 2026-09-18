import Pinwheel.Hardware.Storage.Decoupled

/-! The decoupled organization with two read ports.

`Decoupled` spends a third port on the start word. A commit edge resets the
scheduler, so nothing is consumed on the next edge from the candidates read
then: port 0 can read word 0 on a commit instead. The registers, the fed word,
the invariant and the coverage argument are `Decoupled`'s; only the addresses
and the register update differ, and only the preservation of the invariant has
to be shown again. Two read trees instead of three. -/
namespace Pinwheel.Hardware.Storage.TwoPort
open Loader

def policy : FetchPolicy.Policy 2 Decoupled.Registers where
  fed := Decoupled.fed
  address f core committing _ port :=
    if port = 0 then (if committing then 0 else Dispatch.candidate f core false)
    else Dispatch.candidate f core true
  step _ _ committing st reads :=
    ⟨fun b => reads (if b then 1 else 0), if committing then reads 0 else st.startWord⟩

theorem preserved (i : Machine.Inputs) (s : FetchPolicy.State Decoupled.Registers) (h : Decoupled.Owed s)
    (hm : (FetchPolicy.next policy i s).machine = Machine.next i s.machine) :
    Decoupled.Owed (FetchPolicy.next policy i s) := by
  intro hv
  refine ⟨fun hb b => ?_, ?_⟩
  · obtain ⟨_, hc, _, _⟩ := FetchPolicy.running_facts i s hm hb
    have hread := FetchPolicy.read_next i s hm hb b
    cases b
    · show Loader.Store.read _ (if Machine.committing i s.machine then 0 else _) = _
      rw [hc]
      exact hread
    · exact hread
  · have hstart : (FetchPolicy.next policy i s).policy.startWord =
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
    exact FetchPolicy.start_word_next i s hm s.policy.startWord (fun hv0 => (h hv0).2) hv

def correct : FetchPolicy.Correct policy where
  Inv := Decoupled.Owed
  Rule := fun _ => True
  covers := fun i s _ h hv hc _ => Decoupled.covers policy rfl i s h hv hc
  preserved := fun i s _ h _ hm => preserved i s h hm
  initial := fun i s hi hm => by
    intro hv
    exfalso
    rw [hm, (Machine.initialize_safe i s.machine hi).1] at hv
    simp at hv

/-- It refines the atomic reference edge for edge, for every input history. -/
def refinement : Timed.Refinement (FetchPolicy.component policy) Cache.referenceComponent :=
  FetchPolicy.refinement correct (fun _ => trivial)

/-! ### The machine by name, and its register updates for a netlist -/

abbrev State := FetchPolicy.State Decoupled.Registers

def next : Machine.Inputs → State → State := FetchPolicy.next policy

/-- Port 0: word 0 on a commit, the untaken candidate otherwise. -/
def address0 (i : Machine.Inputs) (s : State) : BitVec 8 :=
  if Machine.committing i s.machine then 0
  else Dispatch.candidate (FetchPolicy.feed policy i s) s.machine.core false

theorem reads0 (i : Machine.Inputs) (s : State) :
    FetchPolicy.reads policy i s 0 =
      Loader.Store.read (s.machine.memory (Machine.selected i s.machine)) (address0 i s) := rfl

theorem next_fetched (i : Machine.Inputs) (s : State) (b : Bool) :
    (next i s).policy.fetched b =
      if b then Loader.Store.read (s.machine.memory (Machine.selected i s.machine))
        (Dispatch.candidate (FetchPolicy.feed policy i s) s.machine.core true)
      else FetchPolicy.reads policy i s 0 := by
  cases b <;> rfl

theorem next_startWord (i : Machine.Inputs) (s : State) :
    (next i s).policy.startWord =
      if Machine.committing i s.machine then FetchPolicy.reads policy i s 0 else s.policy.startWord := rfl

end Pinwheel.Hardware.Storage.TwoPort
