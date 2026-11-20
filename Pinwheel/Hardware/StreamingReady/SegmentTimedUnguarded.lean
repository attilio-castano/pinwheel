import Pinwheel.Hardware.StreamingReady.SegmentHostService
import Pinwheel.Hardware.StreamingReady.SegmentUnguardedTransaction

/-! Schedule unguarded stream slots on the original finite clock trace.
    Bounded host credit selects admission. The instruction fixes both dwells. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTimedUnguarded

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentUnguardedReceive
open SegmentHostService (BoundedCredit reserve_within)
open ProtocolOwnership (DrainInput)
open SegmentTiming (run)
open Pinwheel.Program.StreamingReady (Cell)

private theorem noReset {i : Values Core.Input} (ordinary : DrainInput i) : NoReset i :=
  ⟨ordinary.1, by simp [ordinary.2.1]⟩

private theorem split_clock (inputs : List (Values Core.Input)) (n : Nat) (room : n < inputs.length) :
    ∃ (before : List (Values Core.Input)) (edge : Values Core.Input) (rest : List (Values Core.Input)),
      inputs = before ++ @edge :: rest ∧ before.length = n := by
  induction n generalizing inputs with
  | zero =>
    cases inputs with
    | nil => simp at room
    | cons edge rest => exact ⟨[], edge, rest, rfl, rfl⟩
  | succ n ih =>
    cases inputs with
    | nil => simp at room
    | cons head tail =>
      obtain ⟨before, edge, rest, split, length⟩ := ih tail (by simpa using room)
      exact ⟨@head :: before, edge, rest,
        congrArg (List.cons (α := Values Core.Input) head) split, by simp [length]⟩

/-- Conservative room for one unguarded slot and its longest credit park. -/
def slotBudget (cell : Cell) (parkBound : Nat) : Nat :=
  parkBound + 3 + cell.lowDuration.val + cell.highDuration.val

/-- Derive both dwell boundaries and the sample edge from the first actual
    credit opportunity. An RX drain may occur on any clock. -/
theorem slot_from_clocks (registered : Bool) (s : Values (Register a)) (cell : Cell)
    (entry : AtReservation rows pc cell none previous s)
    (inputs : List (Values Core.Input)) (parkBound : Nat) (room : slotBudget cell parkBound ≤ inputs.length)
    (ordinary : ∀ i ∈ inputs, DrainInput i) (service : BoundedCredit registered s inputs parkBound) :
    ∃ (slot : SlotPlan) (rest : List (Values Core.Input)),
      inputs = slot.inputs ++ rest ∧ slot.inputs.length ≤ slotBudget cell parkBound ∧
      slot.Served registered cell s := by
  obtain ⟨parks, admit, afterAdmit, split, within, history, _, _, clean, credit, _⟩ :=
    reserve_within registered s inputs parkBound entry (fun i hi => noReset (ordinary i hi)) service
  rw [split, List.length_append, List.length_cons] at room
  simp only [slotBudget] at room
  have enoughLow : cell.lowDuration.val < afterAdmit.length := by omega
  obtain ⟨low, aperture, afterAperture, splitLow, lowTicks⟩ := split_clock afterAdmit cell.lowDuration.val enoughLow
  have enoughHigh : cell.highDuration.val < afterAperture.length := by
    rw [splitLow, List.length_append, List.length_cons, lowTicks] at room
    omega
  obtain ⟨high, leave, rest, splitHigh, highTicks⟩ := split_clock afterAperture cell.highDuration.val enoughHigh
  let slot : SlotPlan := ⟨admit, low, aperture, high, leave, parks⟩
  have partition : inputs = slot.inputs ++ rest := by
    rw [split, splitLow, splitHigh]
    simp only [slot, SlotPlan.inputs, List.append_assoc, List.cons_append, List.nil_append]
  have beforeRest : ∀ i ∈ slot.inputs, DrainInput i := by
    intro i hi
    apply ordinary i
    rw [partition]
    exact List.mem_append_left rest hi
  have length : slot.inputs.length ≤ slotBudget cell parkBound := by
    simp only [slot, SlotPlan.inputs, List.length_append, List.length_cons, List.length_nil, slotBudget,
      lowTicks, highTicks]
    omega
  refine ⟨slot, rest, partition, length, ⟨history, clean, credit, lowTicks, ?_, ?_, highTicks, ?_, ?_⟩⟩
  · intro i hi
    exact beforeRest i (by simp [slot, SlotPlan.inputs, hi])
  · exact noReset (beforeRest aperture (by simp [slot, SlotPlan.inputs]))
  · intro i hi
    exact noReset (beforeRest i (by simp [slot, SlotPlan.inputs, hi]))
  · exact noReset (beforeRest leave (by simp [slot, SlotPlan.inputs]))

/-- A bound on host credit at any reservation cut reached along the input
    tape. Each suffix keeps the same bound. -/
def CreditFrom (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (parkBound : Nat) : Prop :=
  ∀ (before rest : List (Values Core.Input)), inputs = before ++ rest →
    run registered s before (.base .phase) = 2#3 →
    BoundedCredit registered (run registered s before) rest parkBound

theorem CreditFrom.here {s : Values (Register a)}
    (service : CreditFrom registered s inputs parkBound) (entry : s (.base .phase) = 2#3) :
    BoundedCredit registered s inputs parkBound := service [] inputs rfl entry

theorem CreditFrom.suffix {s : Values (Register a)} (service : CreditFrom registered s inputs parkBound)
    (split : inputs = before ++ rest) : CreditFrom registered (run registered s before) rest parkBound := by
  intro elapsed remaining later entry
  have full : inputs = (before ++ elapsed) ++ remaining := by rw [split, later, List.append_assoc]
  rw [← SegmentTiming.run_append] at entry ⊢
  exact service (before ++ elapsed) remaining full entry

/-- A counted stream consumes a bounded tape prefix. The next slot's credit
    promise is inherited on the suffix of the original trace. -/
theorem slots_from_clocks (registered : Bool) (s : Values (Register a)) (cell : Cell)
    (entry : AtReservation rows pc cell none previous s) (inBounds : pc < rows.length)
    (slots : Nat) (count : (s (.base .remaining)).toNat = slots)
    (inputs : List (Values Core.Input)) (parkBound : Nat)
    (room : slots * slotBudget cell parkBound ≤ inputs.length) (ordinary : ∀ i ∈ inputs, DrainInput i)
    (service : CreditFrom registered s inputs parkBound) :
    ∃ (plans : List SlotPlan) (rest : List (Values Core.Input)), plans.length = slots ∧
      inputs = plans.flatMap SlotPlan.inputs ++ rest ∧
      (plans.flatMap SlotPlan.inputs).length ≤ slots * slotBudget cell parkBound ∧
      Served registered cell s plans := by
  induction slots generalizing s previous inputs with
  | zero => exact ⟨[], inputs, rfl, rfl, Nat.zero_le _, trivial⟩
  | succ slots ih =>
    have roomSlot : slotBudget cell parkBound ≤ inputs.length := by
      rw [Nat.succ_mul] at room
      omega
    obtain ⟨plan, afterSlot, split, slotLength, served⟩ := slot_from_clocks registered s cell entry inputs parkBound
      roomSlot ordinary (service.here entry.phase)
    cases slots with
    | zero =>
      exact ⟨[plan], afterSlot, rfl, by simpa using split, by simpa using slotLength, ⟨served, trivial⟩⟩
    | succ slots =>
      have positive : 0 < (s (.base .remaining)).toNat := by rw [count]; omega
      have repeats : 1 < (s (.base .remaining)).toNat := by rw [count]; omega
      obtain ⟨step, _⟩ := run_slot registered cell plan s entry inBounds positive served
      have left : ((plan.after registered s) (.base .remaining)).toNat = slots + 1 := by
        rw [step.remaining, count]
        omega
      have roomRest : (slots + 1) * slotBudget cell parkBound ≤ afterSlot.length := by
        rw [Nat.succ_mul, split, List.length_append] at room
        omega
      have quietRest : ∀ i ∈ afterSlot, DrainInput i := by
        intro i hi
        apply ordinary i
        rw [split]
        exact List.mem_append_right _ hi
      have suffix := service.suffix split
      rw [plan.run_inputs] at suffix
      obtain ⟨nextPlans, rest, nextCount, nextSplit, nextLength, nextServed⟩ :=
        ih (plan.after registered s) (step.repeatCell repeats) left afterSlot roomRest quietRest suffix
      refine ⟨plan :: nextPlans, rest, by simp [nextCount], ?_, ?_, ⟨served, nextServed⟩⟩
      · rw [split, nextSplit]
        simp only [List.flatMap_cons, List.append_assoc]
      · rw [List.flatMap_cons, List.length_append, Nat.succ_mul]
        omega

/-- The installed stream's FETCH, counted dwell intervals and first-credit
    reservations are all taken from the same input tape. -/
theorem from_clocks (registered : Bool) (cell : Cell) (s : Values (Register a))
    (cut : SegmentTransaction.Cut registered rows cursor previous s)
    (row : rows[cursor.pc]? = some (.cell (.stream cell none)))
    (checked : Pinwheel.Program.StreamingReadySegments.successors rows budget cursor = some (.next following))
    (budgetFits : budget < 65536) (slots : Nat) (armed : cursor.slots = some slots)
    (inputs : List (Values Core.Input)) (parkBound : Nat)
    (room : 1 + slots * slotBudget cell parkBound ≤ inputs.length) (ordinary : ∀ i ∈ inputs, DrainInput i)
    (service : CreditFrom registered s inputs parkBound) :
    ∃ (used rest : List (Values Core.Input)) (bit : Option Bool), inputs = used ++ rest ∧
      used.length ≤ 1 + slots * slotBudget cell parkBound ∧
      SegmentTransaction.ServiceSpan registered rows following bit s used := by
  cases inputs with
  | nil => simp at room
  | cons fetch clocks =>
    have fetchInput := noReset (ordinary fetch (by simp))
    have positive : 0 < slots := by
      cases slots with
      | zero => simp [Pinwheel.Program.StreamingReadySegments.successors, row, armed] at checked
      | succ n => exact Nat.zero_lt_succ n
    have count := cut.slots slots armed
    have nonzero : s (.base .remaining) ≠ 0#16 := by
      intro zero
      simp [zero] at count
      omega
    obtain ⟨entry, remaining, _, _⟩ := load_row registered cell s fetch cut.boundary fetchInput row nonzero
    let live : Values (Register a) := (circuit a registered).step fetch s
    have credit : CreditFrom registered live clocks parkBound := service.suffix (before := [@fetch]) rfl
    have enough : slots * slotBudget cell parkBound ≤ clocks.length := by
      simp only [List.length_cons] at room
      omega
    have ordinaryClocks : ∀ i ∈ clocks, DrainInput i := fun i hi =>
      ordinary i (List.mem_cons_of_mem (α := Values Core.Input) fetch hi)
    obtain ⟨plans, rest, complete, split, length, served⟩ := slots_from_clocks registered live cell entry
      (List.getElem?_eq_some_iff.mp row).1 slots ((congrArg BitVec.toNat remaining).trans count)
      clocks parkBound enough ordinaryClocks credit
    have span := SegmentUnguardedTransaction.service_stream registered cell s fetch plans cut row checked
      budgetFits (by rw [complete]; exact armed) fetchInput served
    refine ⟨@fetch :: plans.flatMap SlotPlan.inputs, rest, _, ?_, ?_, span⟩
    · simpa only [List.cons_append] using congrArg (List.cons (α := Values Core.Input) fetch) split
    · simp only [List.length_cons]
      omega

end Pinwheel.Hardware.StreamingReady.SegmentTimedUnguarded
