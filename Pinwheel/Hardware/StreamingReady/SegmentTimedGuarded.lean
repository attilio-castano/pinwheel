import Pinwheel.Hardware.StreamingReady.SegmentGuardedTransaction
import Pinwheel.Hardware.StreamingReady.SegmentHostService
import Pinwheel.Hardware.StreamingReady.SegmentRawAperture
import Pinwheel.Hardware.StreamingReady.SegmentAdmission

/-! Recover guarded slot boundaries from one supplied clock list. The host
    bounds credit delay, and the wire samples decide the bounded aperture. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTimedGuarded

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTiming SegmentGuardedTransaction
open SegmentUnguardedReceive (AtReservation ParkHistory)
open SegmentHostService (BoundedCredit reserve_within)
open SegmentRawAperture (LoadedGuard select_poll poll_from_raw)
open ProtocolOwnership (DrainInput)
open Pinwheel.Program.StreamingReady (Cell Guard WaitLimit encode)
open Pinwheel.Program.StreamingReadySegments (Row Successors successors)
open SegmentTransaction (Cut)
open SegmentAdmission (TimedService)

def slotBudget (cell : Cell) (n : Fin 255) (bound : Nat) : Nat :=
  bound + cell.lowDuration.val + n.val + cell.highDuration.val + 4

theorem split_dwell (clocks : List (Values Core.Input)) (ticks : Nat) (room : ticks < clocks.length) :
    ∃ (holds : List (Values Core.Input)) (last : Values Core.Input) (rest : List (Values Core.Input)),
      clocks = holds ++ @last :: rest ∧ holds.length = ticks := by
  have nonempty : clocks.drop ticks ≠ [] := by
    intro empty
    have dropped := List.length_drop (l := clocks) (i := ticks)
    simp only [empty, List.length_nil] at dropped
    omega
  cases split : clocks.drop ticks with
  | nil => exact (nonempty split).elim
  | cons last rest =>
    refine ⟨clocks.take ticks, last, rest, ?_, ?_⟩
    · rw [← split, List.take_append_drop]
    · rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt room)]

private theorem check_prefix (clocks consumed rest : List (Values Core.Input)) (ticks : Nat)
    (split : clocks = consumed ++ rest) (room : consumed.length ≤ ticks)
    (clean : ∀ i ∈ clocks.take ticks, DrainInput i) : ∀ i ∈ consumed, DrainInput i := by
  have kept : (clocks.take ticks).take consumed.length = consumed := by
    rw [List.take_take, Nat.min_eq_left room, split, List.take_left]
  intro i mem
  apply clean i
  exact List.mem_of_mem_take (kept ▸ mem)

/-- The host may push while restoring credit. After the first reservation,
    command-zero clocks without TX push cover LOW and the poll budget.
    RX pops remain available during those clocks. -/
structure Supply (registered : Bool) (s : Values (Register a)) (clocks : List (Values Core.Input))
    (cell : Cell) (n : Fin 255) (bound : Nat) : Prop where
  room : slotBudget cell n bound ≤ clocks.length
  ordinary : ∀ i ∈ clocks, NoReset i
  credit : BoundedCredit registered s clocks bound
  quiet : ∀ (parks : List (Values Core.Input)) (admit : Values Core.Input) (rest : List (Values Core.Input)),
    clocks = parks ++ @admit :: rest → ParkHistory registered s parks →
    Core.credit.eval admit (project (run registered s parks)) = 1#1 →
    ∀ i ∈ rest.take (cell.lowDuration.val + n.val + 2), DrainInput i

inductive Supplied (registered : Bool) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (n : Fin 255) (bound : Nat) (clocks : List (Values Core.Input)) : Prop where
  | qualified {plan : SlotPlan} {rest : List (Values Core.Input)}
      (split : clocks = plan.inputs ++ rest) (used : plan.inputs.length ≤ slotBudget cell n bound)
      (service : plan.Served registered cell g (.misses n) s)
  | expired {plan : AperturePlan} {rest : List (Values Core.Input)}
      (split : clocks = plan.prefix ++ @plan.poll :: rest)
      (service : plan.Delivered registered cell (.misses n) s) (elapsed : plan.misses.length = n.val)
      (miss : g.matches (plan.beforePoll registered s (.base .stage2)) = false)

/-- Choose reservation, LOW dwell, earliest eligible poll, and any required
    HIGH dwell. The caller supplies the clocks and their service bounds. -/
theorem slot_from_clocks (registered : Bool) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (n : Fin 255) (limit : g.limit = .misses n) (clocks : List (Values Core.Input))
    (entry : AtReservation rows pc cell (some g) previous s) (bounds : Supply registered s clocks cell n bound) :
    Supplied registered s cell g n bound clocks := by
  obtain ⟨parks, admit, rest, split, within, history, parked, _, admitInput, credit, reserve⟩ :=
    reserve_within registered s clocks bound entry bounds.ordinary bounds.credit
  have enough : cell.lowDuration.val + n.val + cell.highDuration.val + 3 ≤ rest.length := by
    have room := bounds.room
    rw [split] at room
    simp only [slotBudget, List.length_append, List.length_cons] at room
    omega
  obtain ⟨low, arm, afterArm, tailSplit, lowLength⟩ :=
    split_dwell rest cell.lowDuration.val (by omega)
  have quiet := bounds.quiet parks admit rest split history credit
  have quietLow : ∀ i ∈ low ++ [@arm], DrainInput i := by
    refine check_prefix rest (low ++ [@arm]) afterArm _ ?_ ?_ quiet
    · simpa only [List.append_assoc, List.singleton_append] using tailSplit
    · simp [lowLength]
      omega
  have lowInput : ∀ i ∈ low, DrainInput i := fun i member => quietLow i (List.mem_append_left _ member)
  have armInput : DrainInput arm := quietLow arm (by simp)
  let reserved : Values (Register a) := (circuit a registered).step admit (run registered s parks)
  let lowEnd : Values (Register a) := run registered reserved low
  let entered : Values (Register a) := (circuit a registered).step arm lowEnd
  have timer : (reserved (.base .countdown)).toNat = cell.lowDuration.val := by
    have programmed := congrArg BitVec.toNat reserve.countdown
    change (reserved (.base .countdown)).toNat = (BitVec.ofNat 8 cell.lowDuration.val).toNat at programmed
    simpa [Nat.mod_eq_of_lt cell.lowDuration.isLt] using programmed
  have lowSpan : SegmentStreamStep.LowSpan reserved lowEnd low.length :=
    SegmentStreamStep.low_span registered reserved low reserve.phase (by simp only [timer, lowLength, Nat.le_refl]) lowInput
  have lowElapsed : lowEnd (.base .countdown) = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    rw [lowSpan.countdown, timer, lowLength, Nat.sub_self, BitVec.toNat_zero]
  have lowWord : lowEnd (.base .currentWord) = encode (.stream cell (some g)) :=
    lowSpan.pose.current.trans (reserve.current.trans parked.ready.current)
  have waiting := enter_guarded_aperture registered arm lowEnd cell g armInput lowSpan.phase lowElapsed lowWord
  have loaded : LoadedGuard g entered := LoadedGuard.stream cell g (waiting.current.trans lowWord)
  have count : (entered (.base .countdown)).toNat = n.val := by
    rw [show entered (.base .countdown) = g.limit.initialCountdown from waiting.countdown, limit]
    simp [WaitLimit.initialCountdown, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n.val < 256 by omega)]
  have bounded : guardBudget entered ≠ 0#8 := by
    rw [loaded.budget, limit]
    exact SourceRefinement.budget_nonzero n
  have inputLength : n.val + cell.highDuration.val + 2 ≤ afterArm.length := by
    rw [tailSplit] at enough
    simp only [List.length_append, List.length_cons, lowLength] at enough
    omega
  let older := entered (.base .stage2)
  let newer := entered (.base .stage1)
  obtain ⟨misses, poll, afterPoll, pollSplit, withinPoll, missed, outcome⟩ :=
    select_poll g older newer afterArm n.val (by omega)
  have sampledInputs : ∀ i ∈ low ++ @arm :: (misses ++ [@poll]), DrainInput i := by
    refine check_prefix rest (low ++ @arm :: (misses ++ [@poll])) afterPoll _ ?_ ?_ quiet
    · rw [tailSplit, pollSplit]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    · simp only [List.length_append, List.length_cons, List.length_nil, lowLength]
      omega
  have missedInputs : ∀ i ∈ misses, DrainInput i := by
    intro i member
    apply sampledInputs i
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ member))
  have pollInput : DrainInput poll := sampledInputs poll (by simp)
  have admitted := poll_from_raw registered entered g older newer misses poll rfl rfl missedInputs waiting.phase
    loaded bounded (count ▸ withinPoll) missed
  let aperture : AperturePlan := ⟨admit, low, arm, misses, poll, parks⟩
  have service : aperture.Delivered registered cell (.misses n) s :=
    ⟨history, admitInput, credit, lowLength, lowInput, armInput, admitted.history, withinPoll, pollInput⟩
  have splitAtPoll : clocks = aperture.prefix ++ @poll :: afterPoll := by
    rw [split, tailSplit, pollSplit]
    simp only [aperture, AperturePlan.prefix, List.append_assoc, List.cons_append]
  have sample : aperture.beforePoll registered s (.base .stage2) =
      SegmentRawAperture.sampleAfter older newer misses := admitted.sample
  cases verdict : g.matches (aperture.beforePoll registered s (.base .stage2)) with
  | false =>
    rw [← sample, verdict] at outcome
    exact .expired splitAtPoll service (outcome.resolve_left (by decide)) verdict
  | true =>
    have highRoom : cell.highDuration.val < afterPoll.length := by
      rw [pollSplit] at inputLength
      simp only [List.length_append, List.length_cons] at inputLength
      omega
    obtain ⟨high, leave, tail, highSplit, highLength⟩ :=
      split_dwell afterPoll cell.highDuration.val highRoom
    let plan : SlotPlan := ⟨aperture, high, leave⟩
    have whole : clocks = plan.inputs ++ tail := by
      rw [splitAtPoll, highSplit]
      simp only [plan, SlotPlan.inputs, List.append_assoc, List.cons_append, List.nil_append]
      rfl
    have highInputs : ∀ i ∈ high, NoReset i := by
      intro i member
      apply bounds.ordinary i
      rw [splitAtPoll, highSplit]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ member))
    have leaveInput : NoReset leave := bounds.ordinary leave (by rw [splitAtPoll, highSplit]; simp)
    refine .qualified whole ?_ ⟨service, verdict, highLength, highInputs, leaveInput⟩
    simp only [plan, aperture, SlotPlan.inputs, AperturePlan.prefix, List.length_append,
      List.length_cons, List.length_nil, lowLength, highLength, slotBudget]
    omega

/-- A host policy is inherited at stream boundaries along the same input
    list. The arithmetic budget supplies the required room at each cut. -/
def SupplyFrom (registered : Bool) (s : Values (Register a)) (clocks : List (Values Core.Input))
    (cell : Cell) (n : Fin 255) (bound : Nat) : Prop :=
  ∀ (before rest : List (Values Core.Input)), clocks = before ++ rest →
    (run registered s before) (.base .phase) = 2#3 →
    slotBudget cell n bound ≤ rest.length → Supply registered (run registered s before) rest cell n bound

private theorem SupplyFrom.suffix {s : Values (Register a)}
    (policy : SupplyFrom registered s clocks cell n bound) (split : clocks = before ++ rest) :
    SupplyFrom registered (run registered s before) rest cell n bound := by
  intro elapsed remaining next phase room
  have full : clocks = (before ++ elapsed) ++ remaining := by rw [split, next, List.append_assoc]
  rw [← run_append] at phase ⊢
  exact policy (before ++ elapsed) remaining full phase room

inductive Slots (registered : Bool) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (n : Fin 255) (count : Nat) (clocks : List (Values Core.Input)) : Prop where
  | complete {plans : List SlotPlan} {rest : List (Values Core.Input)}
      (length : plans.length = count) (split : clocks = plans.flatMap SlotPlan.inputs ++ rest)
      (served : Served registered cell g (.misses n) s plans)
  | expired {plans : List SlotPlan} {aperture : AperturePlan} {rest : List (Values Core.Input)}
      (inside : plans.length < count)
      (split : clocks = plans.flatMap SlotPlan.inputs ++ (aperture.prefix ++ @aperture.poll :: rest))
      (served : Served registered cell g (.misses n) s plans)
      (last : aperture.Delivered registered cell (.misses n) (runSlots registered s plans))
      (elapsed : aperture.misses.length = n.val)
      (miss : g.matches (aperture.beforePoll registered (runSlots registered s plans) (.base .stage2)) = false)

private theorem slots_from_clocks (registered : Bool) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (n : Fin 255) (limit : g.limit = .misses n) (receive : cell.receive = true)
    (entry : AtReservation rows pc cell (some g) previous s) (inBounds : pc < rows.length)
    (count : Nat) (slots : (s (.base .remaining)).toNat = count)
    (clocks : List (Values Core.Input)) (bound : Nat)
    (room : count * slotBudget cell n bound ≤ clocks.length)
    (policy : SupplyFrom registered s clocks cell n bound) : Slots registered s cell g n count clocks := by
  induction count generalizing s previous clocks with
  | zero => exact .complete (plans := []) (rest := clocks) rfl rfl trivial
  | succ count ih =>
    have roomSlot : slotBudget cell n bound ≤ clocks.length := by rw [Nat.succ_mul] at room; omega
    have supplying : Supply registered s clocks cell n bound :=
      policy [] clocks rfl entry.phase roomSlot
    cases slot_from_clocks registered s cell g n limit clocks entry supplying with
    | @expired aperture rest split service elapsed miss =>
      exact .expired (plans := []) (aperture := aperture) (rest := rest)
        (Nat.zero_lt_succ _) split trivial service elapsed miss
    | @qualified plan afterSlot split used service =>
      cases count with
      | zero =>
        exact .complete (plans := [plan]) (rest := afterSlot) rfl (by simpa using split) ⟨service, trivial⟩
      | succ count =>
        have positive : 0 < (s (.base .remaining)).toNat := by rw [slots]; omega
        have repeats : 1 < (s (.base .remaining)).toNat := by rw [slots]; omega
        obtain ⟨step, _⟩ := run_slot registered cell g (.misses n) limit receive plan s entry inBounds positive service
        have left : ((plan.after registered s) (.base .remaining)).toNat = count + 1 := by
          rw [step.remaining, slots]
          omega
        have nextRoom : (count + 1) * slotBudget cell n bound ≤ afterSlot.length := by
          rw [Nat.succ_mul, split, List.length_append] at room
          omega
        have nextPolicy := policy.suffix split
        rw [plan.run_inputs] at nextPolicy
        cases ih (plan.after registered s) (step.repeatCell repeats) left afterSlot nextRoom nextPolicy with
        | @complete plans rest length nextSplit served =>
          refine .complete (plans := plan :: plans) (rest := rest) (by simp [length]) ?_ ⟨service, served⟩
          rw [split, nextSplit]
          simp only [List.flatMap_cons, List.append_assoc]
        | @expired plans aperture rest inside nextSplit served last elapsed miss =>
          refine .expired (plans := plan :: plans) (aperture := aperture) (rest := rest) ?_ ?_
            ⟨service, served⟩ ?_ elapsed ?_
          · simp only [List.length_cons]
            omega
          · rw [split, nextSplit]
            simp only [List.flatMap_cons, List.append_assoc]
          · simpa only [runSlots_cons] using last
          · simpa only [runSlots_cons] using miss

/-- Construct the row service witness from bounded host credit and raw
    clocks. The first expired slot, if any, is selected by wire samples. -/
theorem from_clocks (registered : Bool) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (n : Fin 255) (limit : g.limit = .misses n) (receive : cell.receive = true)
    (cut : Cut registered rows cursor previous s) (row : rows[cursor.pc]? = some (.cell (.stream cell (some g))))
    (checked : successors rows budget cursor = some (.next following)) (budgetFits : budget < 65536)
    (slots : Nat) (armed : cursor.slots = some slots)
    (clocks : List (Values Core.Input)) (bound : Nat) (room : 1 + slots * slotBudget cell n bound ≤ clocks.length)
    (ordinary : ∀ i ∈ clocks, NoReset i) (policy : SupplyFrom registered s clocks cell n bound) :
    TimedService registered rows budget cursor following s clocks := by
  cases clocks with
  | nil => simp at room
  | cons fetch rest =>
    have fetchInput : NoReset fetch := ordinary fetch (by simp)
    obtain ⟨canonical, _, _, _, _, _, positive, _, _⟩ := successor_stream row armed checked
    have liveSlots := cut.slots slots armed
    have nonzero : s (.base .remaining) ≠ 0#16 := by
      intro zero
      simp [zero] at liveSlots
      omega
    let loaded : Values (Register a) := (circuit a registered).step fetch s
    have load := load_row registered cell g s fetch cut.boundary fetchInput row canonical nonzero
    have enough : slots * slotBudget cell n bound ≤ rest.length := by simp only [List.length_cons] at room; omega
    have restPolicy : SupplyFrom registered loaded rest cell n bound := policy.suffix (before := [@fetch]) rfl
    cases slots_from_clocks registered loaded cell g n limit receive load.ready
        (List.getElem?_eq_some_iff.mp row).1 slots ((congrArg BitVec.toNat load.remaining).trans liveSlots)
        rest bound enough restPolicy with
    | @complete plans tail length split served =>
      have span := service_stream registered cell g (.misses n) limit receive s fetch plans cut row checked budgetFits
        (by rw [length]; exact armed) fetchInput served
      exact .advance (by simpa only [List.cons_append] using congrArg (List.cons (α := Values Core.Input) fetch) split) span
    | @expired plans aperture tail inside split served last elapsed miss =>
      have wall := timeout_stream_row registered cell g n limit receive s fetch plans aperture
        cut.boundary fetchInput row canonical (liveSlots ▸ inside) served last elapsed miss
      have span := timeout_span registered cell g n limit receive s cut row checked budgetFits armed inside wall
      refine .timeout (rest := tail) ?_ span
      simpa only [deadlinePrefix, List.cons_append, List.append_assoc] using
        congrArg (List.cons (α := Values Core.Input) fetch) split

end Pinwheel.Hardware.StreamingReady.SegmentTimedGuarded
