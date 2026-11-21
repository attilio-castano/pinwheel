import Pinwheel.Hardware.StreamingReady.SegmentTimedGuarded

/-! Service peer-paced guarded streams. The external response bound
    supplies runway for progress while the encoded guard remains unbounded. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentEventStream

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTiming SegmentGuardedTransaction
open Pinwheel.Program.StreamingReady (Cell Guard encode)
open Pinwheel.Program.StreamingReadySegments (Row Successors successors)
open SegmentUnguardedReceive (AtReservation)
open SegmentHostService (BoundedCredit reserve_within)
open SegmentRawAperture (LoadedGuard samples)
open SegmentTimedGuarded (split_dwell)
open SegmentTransaction (Cut ServiceSpan)
open ProtocolOwnership (DrainInput)

def slotBudget (cell : Cell) (peerBound creditBound : Nat) : Nat :=
  creditBound + cell.lowDuration.val + peerBound + cell.highDuration.val + 4

def eventWithin (s : Values (Register a)) (g : Guard) (clocks : List (Values Core.Input)) (bound : Nat) : Prop :=
  (samples (s (.base .stage2)) (s (.base .stage1)) (clocks.take (bound + 1))).any g.matches = true

/-- The host supplies the clock inputs and bounded credit. The peer need
    only provide a matching sample by the specified response bound. -/
structure SupplyFrom (registered : Bool) (s : Values (Register a)) (clocks : List (Values Core.Input))
    (cell : Cell) (g : Guard) (peerBound creditBound : Nat) : Prop where
  drain : ∀ i ∈ clocks, DrainInput i
  credit : ∀ (before rest : List (Values Core.Input)), clocks = before ++ rest →
    (run registered s before) (.base .phase) = 2#3 →
    slotBudget cell peerBound creditBound ≤ rest.length →
    BoundedCredit registered (run registered s before) rest creditBound
  arrives : ∀ (before rest : List (Values Core.Input)), clocks = before ++ rest →
    (run registered s before) (.base .phase) = 7#3 →
    (run registered s before) (.base .currentWord) = encode (.stream cell (some g)) →
    eventWithin (run registered s before) g rest peerBound

theorem SupplyFrom.suffix {s : Values (Register a)} (policy : SupplyFrom registered s clocks cell g peerBound creditBound)
    {before rest : List (Values Core.Input)} (split : clocks = before ++ rest) :
    SupplyFrom registered (run registered s before) rest cell g peerBound creditBound := by
  constructor
  · intro i hi
    apply policy.drain i
    rw [split]
    exact List.mem_append_right _ hi
  · intro elapsed later shape boundary room
    rw [← run_append] at boundary ⊢
    exact policy.credit (before ++ elapsed) later (by rw [split, shape, List.append_assoc]) boundary room
  · intro elapsed later shape waiting row
    rw [← run_append] at waiting row ⊢
    exact policy.arrives (before ++ elapsed) later (by rw [split, shape, List.append_assoc]) waiting row

private theorem noReset {i : Values Core.Input} (drain : DrainInput i) : NoReset i :=
  ⟨drain.1, by simp [drain.2.1]⟩

theorem slot_from_clocks (registered : Bool) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (limit : g.limit = .unbounded) (clocks : List (Values Core.Input))
    (entry : AtReservation rows pc cell (some g) previous s)
    (policy : SupplyFrom registered s clocks cell g peerBound creditBound)
    (room : slotBudget cell peerBound creditBound ≤ clocks.length) :
    ∃ (plan : SlotPlan) (rest : List (Values Core.Input)), clocks = plan.inputs ++ rest ∧
      plan.inputs.length ≤ slotBudget cell peerBound creditBound ∧ plan.Served registered cell g .unbounded s := by
  obtain ⟨parks, admit, rest, split, within, history, parked, _, admitInput, credit, reserve⟩ :=
    reserve_within registered s clocks creditBound entry (fun i hi => noReset (policy.drain i hi))
      (policy.credit [] clocks rfl entry.phase room)
  have enough : cell.lowDuration.val + peerBound + cell.highDuration.val + 3 ≤ rest.length := by
    rw [split] at room
    simp only [slotBudget, List.length_append, List.length_cons] at room
    omega
  obtain ⟨low, arm, afterArm, tailSplit, lowLength⟩ := split_dwell rest cell.lowDuration.val (by omega)
  let before := parks ++ @admit :: (low ++ [@arm])
  have armSplit : clocks = before ++ afterArm := by simp [before, split, tailSplit, List.append_assoc]
  have drainAfter : ∀ i ∈ afterArm, DrainInput i := fun i hi => policy.drain i (armSplit.symm ▸ List.mem_append_right _ hi)
  have lowInput : ∀ i ∈ low, DrainInput i := by
    intro i hi
    apply policy.drain i
    rw [split, tailSplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
  have armInput : DrainInput arm := policy.drain arm (by rw [split, tailSplit]; simp)
  let reserved : Values (Register a) := (circuit a registered).step admit (run registered s parks)
  let lowEnd : Values (Register a) := run registered reserved low
  let entered : Values (Register a) := (circuit a registered).step arm lowEnd
  have enteredEq : @run a registered s before = @entered := by
    unfold before
    rw [run_append]
    change @run a registered reserved (low ++ [@arm]) = @entered
    rw [run_append]
    rfl
  have timer : (reserved (.base .countdown)).toNat = low.length := by
    have programmed := congrArg BitVec.toNat reserve.countdown
    change (reserved (.base .countdown)).toNat = (BitVec.ofNat 8 cell.lowDuration.val).toNat at programmed
    simpa [Nat.mod_eq_of_lt cell.lowDuration.isLt, lowLength] using programmed
  have lowSpan : SegmentStreamStep.LowSpan reserved lowEnd low.length :=
    SegmentStreamStep.low_span registered reserved low reserve.phase (Nat.le_of_eq timer.symm) lowInput
  have lowElapsed : lowEnd (.base .countdown) = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    rw [lowSpan.countdown, timer, Nat.sub_self, BitVec.toNat_zero]
  have lowWord : lowEnd (.base .currentWord) = encode (.stream cell (some g)) :=
    lowSpan.pose.current.trans (reserve.current.trans parked.ready.current)
  have armed := enter_guarded_aperture registered arm lowEnd cell g armInput lowSpan.phase lowElapsed lowWord
  have loaded : LoadedGuard g entered := LoadedGuard.stream cell g (armed.current.trans lowWord)
  have event := policy.arrives before afterArm armSplit
    (by rw [enteredEq]; exact armed.phase) (by rw [enteredEq]; exact armed.current.trans lowWord)
  rw [enteredEq] at event
  let old := entered (.base .stage2)
  let recent := entered (.base .stage1)
  let offered := afterArm.take (peerBound + 1)
  rcases SegmentEventWait.select_first g old recent offered with absent | ⟨misses, poll, tail, offeredEq, missed, matched⟩
  · change (samples old recent offered).any g.matches = true at event
    simp [absent] at event
  · let afterPoll := tail ++ afterArm.drop (peerBound + 1)
    have pollSplit : afterArm = misses ++ @poll :: afterPoll := by
      calc
        afterArm = offered ++ afterArm.drop (peerBound + 1) := (List.take_append_drop _ _).symm
        _ = _ := by rw [offeredEq]; simp [afterPoll, List.append_assoc]
    have withinPoll : misses.length ≤ peerBound := by
      have len : offered.length ≤ peerBound + 1 := by
        simp only [offered, List.length_take]
        exact Nat.min_le_left _ _
      rw [offeredEq, List.length_append, List.length_cons] at len
      omega
    have window := SegmentEventWait.first_qualified registered entered g old recent misses poll rfl rfl
      (fun i hi => drainAfter i (pollSplit.symm ▸ List.mem_append_left _ hi)) armed.phase loaded limit missed matched
    have pollInput : DrainInput poll := drainAfter poll (by rw [pollSplit]; simp)
    let aperture : AperturePlan := ⟨admit, low, arm, misses, poll, parks⟩
    have qualified : g.matches (aperture.beforePoll registered s (.base .stage2)) = true :=
      (congrArg g.matches window.sample).trans matched
    have highRoom : cell.highDuration.val < afterPoll.length := by
      rw [tailSplit, pollSplit] at enough
      simp only [List.length_append, List.length_cons, lowLength] at enough
      omega
    obtain ⟨high, leave, tail, highSplit, highLength⟩ := split_dwell afterPoll cell.highDuration.val highRoom
    let plan : SlotPlan := ⟨aperture, high, leave⟩
    have whole : clocks = plan.inputs ++ tail := by
      rw [armSplit, pollSplit, highSplit]
      simp [plan, aperture, SlotPlan.inputs, AperturePlan.prefix, before, List.append_assoc]
    have highInputs : ∀ i ∈ high, NoReset i := by
      intro i hi
      apply noReset (drainAfter i ?_)
      rw [pollSplit, highSplit]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
    have leaveInput : NoReset leave := noReset (drainAfter leave (by rw [pollSplit, highSplit]; simp))
    refine ⟨plan, tail, whole, ?_, ⟨⟨history, admitInput, credit, lowLength, lowInput, armInput,
      window.misses, trivial, pollInput⟩, qualified, highLength, highInputs, leaveInput⟩⟩
    simp only [plan, aperture, SlotPlan.inputs, AperturePlan.prefix, List.length_append,
      List.length_cons, List.length_nil, lowLength, highLength, slotBudget]
    omega

private theorem slots_from_clocks (registered : Bool) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (limit : g.limit = .unbounded) (receive : cell.receive = true)
    (entry : AtReservation rows pc cell (some g) previous s) (inBounds : pc < rows.length)
    (count : Nat) (slots : (s (.base .remaining)).toNat = count) (clocks : List (Values Core.Input))
    (room : count * slotBudget cell peerBound creditBound ≤ clocks.length)
    (policy : SupplyFrom registered s clocks cell g peerBound creditBound) :
    ∃ (plans : List SlotPlan) (rest : List (Values Core.Input)), plans.length = count ∧
      clocks = plans.flatMap SlotPlan.inputs ++ rest ∧ Served registered cell g .unbounded s plans := by
  induction count generalizing s previous clocks with
  | zero => exact ⟨[], clocks, rfl, rfl, trivial⟩
  | succ count ih =>
    have slotRoom : slotBudget cell peerBound creditBound ≤ clocks.length := by rw [Nat.succ_mul] at room; omega
    obtain ⟨plan, afterSlot, split, used, service⟩ :=
      slot_from_clocks registered s cell g limit clocks entry policy slotRoom
    cases count with
    | zero => exact ⟨[plan], afterSlot, rfl, by simpa using split, ⟨service, trivial⟩⟩
    | succ count =>
      have repeats : 1 < (s (.base .remaining)).toNat := by rw [slots]; omega
      obtain ⟨step, _⟩ := run_slot registered cell g .unbounded limit receive plan s entry inBounds
        (Nat.lt_trans Nat.zero_lt_one repeats) service
      have left : ((plan.after registered s) (.base .remaining)).toNat = count + 1 := by
        rw [step.remaining, slots]
        omega
      have nextRoom : (count + 1) * slotBudget cell peerBound creditBound ≤ afterSlot.length := by
        rw [Nat.succ_mul, split, List.length_append] at room
        omega
      have nextPolicy := policy.suffix split
      rw [plan.run_inputs] at nextPolicy
      obtain ⟨plans, rest, length, nextSplit, served⟩ := ih (plan.after registered s)
        (step.repeatCell repeats) left afterSlot nextRoom nextPolicy
      exact ⟨plan :: plans, rest, by simp [length], by rw [split, nextSplit]; simp [List.append_assoc],
        ⟨service, served⟩⟩

theorem from_clocks (registered : Bool) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (limit : g.limit = .unbounded) (receive : cell.receive = true)
    (cut : Cut registered rows cursor previous s)
    (row : rows[cursor.pc]? = some (.cell (.stream cell (some g))))
    (checked : successors rows budget cursor = some (.next following)) (budgetFits : budget < 65536)
    (slots : Nat) (armed : cursor.slots = some slots) (clocks : List (Values Core.Input))
    (room : 1 + slots * slotBudget cell peerBound creditBound ≤ clocks.length)
    (policy : SupplyFrom registered s clocks cell g peerBound creditBound) :
    ∃ (used rest : List (Values Core.Input)) (sample : Option Bool), clocks = used ++ rest ∧
      ServiceSpan registered rows following sample s used := by
  cases clocks with
  | nil => simp at room
  | cons fetch clocks =>
    have ordinary := noReset (policy.drain fetch (by simp))
    obtain ⟨canonical, _, _, _, _, _, positive, _, _⟩ := successor_stream row armed checked
    have count := cut.slots slots armed
    have nonzero : s (.base .remaining) ≠ 0#16 := by
      intro zero
      simp [zero] at count
      omega
    have loaded := load_row registered cell g s fetch cut.boundary ordinary row canonical nonzero
    let live : Values (Register a) := (circuit a registered).step fetch s
    have loadedCount : (live (.base .remaining)).toNat = slots := by
      change ((circuit a registered).step fetch s (.base .remaining)).toNat = slots
      rw [loaded.remaining, count]
    have enough : slots * slotBudget cell peerBound creditBound ≤ clocks.length := by
      simp only [List.length_cons] at room
      omega
    have localPolicy : SupplyFrom registered live clocks cell g peerBound creditBound :=
      policy.suffix (before := [@fetch]) rfl
    obtain ⟨plans, rest, length, split, served⟩ := slots_from_clocks registered live cell g limit receive loaded.ready
      (List.getElem?_eq_some_iff.mp row).1 slots loadedCount clocks enough localPolicy
    have service := service_stream registered cell g .unbounded limit receive s fetch plans cut row checked
      budgetFits (length.symm ▸ armed) ordinary served
    exact ⟨@fetch :: plans.flatMap SlotPlan.inputs, rest, _, by simp [split], service⟩

end Pinwheel.Hardware.StreamingReady.SegmentEventStream
