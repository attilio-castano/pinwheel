import Pinwheel.Hardware.StreamingReady.SegmentCapture
import Pinwheel.Hardware.StreamingReady.SegmentTransaction

/-! Row execution for a counted unguarded stream, with pre-edge credit at
reservation and a sample at each expired LOW aperture. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentUnguardedReceive

open Pinwheel.Hardware SegmentCore SegmentPathControl
open Pinwheel.Program.StreamingReady
open Pinwheel.Program.StreamingReadySegments (Row)
open ProtocolOwnership (DrainInput)
open SegmentTransaction (ActiveClocks)

/-- A slot may park for finitely many clocks before credit is available.
The dwell lists exclude the edges that enter and leave each phase. -/
structure SlotPlan where
  admit : Values Core.Input
  low : List (Values Core.Input)
  aperture : Values Core.Input
  high : List (Values Core.Input)
  leave : Values Core.Input
  parks : List (Values Core.Input) := []

def SlotPlan.inputs (slot : SlotPlan) : List (Values Core.Input) :=
  slot.parks ++ (@slot.admit) :: (slot.low ++ (@slot.aperture) :: (slot.high ++ [@slot.leave]))

def SlotPlan.ready (slot : SlotPlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) := SegmentTiming.run registered s slot.parks

def SlotPlan.lowEnd (slot : SlotPlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) :=
  SegmentTiming.run registered ((circuit a registered).step slot.admit (slot.ready registered s)) slot.low

def SlotPlan.highEnd (slot : SlotPlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) :=
  SegmentTiming.run registered ((circuit a registered).step slot.aperture (slot.lowEnd registered s)) slot.high

def SlotPlan.after (slot : SlotPlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) :=
  (circuit a registered).step slot.leave (slot.highEnd registered s)

def SlotPlan.sample (slot : SlotPlan) (registered : Bool) (cell : Cell) (s : Values (Register a)) : Bool :=
  ((slot.lowEnd registered s) (.base .stage2))[cell.rxInput.val]

theorem SlotPlan.run_inputs (slot : SlotPlan) (registered : Bool) (s : Values (Register a)) :
    @SegmentTiming.run a registered s slot.inputs = @SlotPlan.after a slot registered s := by
  unfold SlotPlan.inputs
  rw [SegmentTiming.run_append]
  change @SegmentTiming.run a registered ((circuit a registered).step slot.admit (slot.ready registered s))
      (slot.low ++ (@slot.aperture) :: (slot.high ++ [@slot.leave])) = _
  rw [SegmentTiming.run_append]
  change @SegmentTiming.run a registered ((circuit a registered).step slot.aperture (slot.lowEnd registered s))
      (slot.high ++ [@slot.leave]) = _
  rw [SegmentTiming.run_append]
  rfl

def ParkHistory (registered : Bool) (s : Values (Register a)) : List (Values Core.Input) → Prop
  | [] => True
  | i :: rest => NoReset i ∧ Core.credit.eval i (project s) = 0#1 ∧
      ParkHistory registered ((circuit a registered).step i s) rest

/-- Each credit check sees the real state before the reservation edge. -/
structure SlotPlan.Served (slot : SlotPlan) (registered : Bool) (cell : Cell)
    (s : Values (Register a)) : Prop where
  parks : ParkHistory registered s slot.parks
  admit : NoReset slot.admit
  credit : Core.credit.eval slot.admit (project (slot.ready registered s)) = 1#1
  lowTicks : slot.low.length = cell.lowDuration.val
  low : ∀ i ∈ slot.low, DrainInput i
  aperture : NoReset slot.aperture
  highTicks : slot.high.length = cell.highDuration.val
  high : ∀ i ∈ slot.high, NoReset i
  leave : NoReset slot.leave

def Served (registered : Bool) (cell : Cell) (s : Values (Register a)) : List SlotPlan → Prop
  | [] => True
  | slot :: rest => slot.Served registered cell s ∧ Served registered cell (slot.after registered s) rest

/-- The physical elapsed time is the programmed dwell time plus the actual
    no-credit waits. Each slot spends one admission, sample and exit edge. -/
theorem served_length (registered : Bool) (cell : Cell) (s : Values (Register a))
    (slots : List SlotPlan) (service : Served registered cell s slots) :
    (slots.flatMap SlotPlan.inputs).length = slots.length * (3 + cell.lowDuration.val + cell.highDuration.val) +
      (slots.map (fun slot => slot.parks.length)).sum := by
  induction slots generalizing s with
  | nil => simp
  | cons slot rest ih =>
    change _ ∧ _ at service
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.map_cons, List.sum_cons]
    rw [ih _ service.2, Nat.add_mul]
    simp only [SlotPlan.inputs, List.length_append, List.length_cons, List.length_nil, service.1.lowTicks,
      service.1.highTicks, Nat.one_mul]
    omega

def runSlots (registered : Bool) (s : Values (Register a)) (slots : List SlotPlan) : Values (Register a) :=
  SegmentTiming.run registered s (slots.flatMap SlotPlan.inputs)

theorem runSlots_cons (registered : Bool) (s : Values (Register a)) (slot : SlotPlan)
    (rest : List SlotPlan) :
    @runSlots a registered s (slot :: rest) = @runSlots a registered (slot.after registered s) rest := by
  change @SegmentTiming.run a registered s (slot.inputs ++ rest.flatMap SlotPlan.inputs) =
    @SegmentTiming.run a registered (slot.after registered s) (rest.flatMap SlotPlan.inputs)
  rw [SegmentTiming.run_append, slot.run_inputs]

def captured (registered : Bool) (cell : Cell) (s : Values (Register a)) (previous : Option Bool) :
    List SlotPlan → Option Bool
  | [] => previous
  | slot :: rest => captured registered cell (slot.after registered s)
      (if cell.receive then some (slot.sample registered cell s) else previous) rest

/-- A receive-disabled stream leaves the capture latch as it was at entry. -/
theorem captured_passive (registered : Bool) (cell : Cell) (s : Values (Register a))
    (previous : Option Bool) (slots : List SlotPlan) (passive : cell.receive = false) :
    captured registered cell s previous slots = previous := by
  induction slots generalizing s with
  | nil => rfl
  | cons slot rest ih => simp only [captured, passive, Bool.false_eq_true, if_false, ih]

/-- A nonempty receiving stream produces a qualified capture regardless of the
    incoming latch. -/
theorem captured_qualifies (registered : Bool) (cell : Cell) (s : Values (Register a))
    (previous : Option Bool) (slots : List SlotPlan) (receive : cell.receive = true)
    (nonempty : slots ≠ []) : (captured registered cell s previous slots).isSome = true := by
  induction slots generalizing s previous with
  | nil => exact (nonempty rfl).elim
  | cons slot rest ih =>
    simp only [captured, receive, if_true]
    cases rest with
    | nil => rfl
    | cons next rest => exact ih _ _ (by simp)

private theorem noReset (h : DrainInput i) : NoReset i := ⟨h.1, by simp [h.2.1]⟩

structure Held (s after : Values (Register a)) : Prop where
  last : after .lastCapture = s .lastCapture
  valid : after .captureValid = s .captureValid
  produced : after (.base .rxProduced) = s (.base .rxProduced)

theorem Held.capture (frame : Held s after) (old : HasCapture s previous) :
    HasCapture after previous := by
  cases previous <;> simpa only [HasCapture, frame.last, frame.valid] using old

theorem Held.trans (left : Held s middle) (right : Held middle after) : Held s after :=
  ⟨right.last.trans left.last, right.valid.trans left.valid, right.produced.trans left.produced⟩

set_option linter.unusedSimpArgs false in
theorem hold (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i)
    (outsideAperture : (s (.base .phase) = 1#3 ∧ ((word registered).eval i s).extractLsb' 0 3 = 1#3) ∨
      s (.base .phase) = 2#3 ∨ (s (.base .phase) = 3#3 ∧ s (.base .countdown) ≠ 0#8)) :
    Held s ((circuit a registered).step i s) := by
  obtain ⟨init, command⟩ := ordinary
  rcases outsideAperture with ⟨phase, stream⟩ | phase | ⟨phase, positive⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    change (bindWord (word registered) (next _)).eval i s = _ <;>
    rw [bindWord_eval] <;>
    simp [next, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput, decodedRegister,
      withFetch, lift, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting,
      Core.cmd, Core.both, Core.either, Core.free, Core.starting, Core.releasing, Core.hostOwner,
      Core.owned, Core.retained, Core.isPhase, Core.fetching, Core.enteringCell, Core.reserving,
      Core.takingTX, Core.lowEnd, Core.advancing, Core.highEnd, Core.guardedLowEnd, Core.capture,
      Core.standaloneSuccess, Core.waitSuccess, Core.waitFault, Core.waitDecrement, Core.capturingRX,
      Core.receive, Core.highGuard, Core.stream, Core.field, Core.inputBit, Core.clearedRuntime,
      Core.inc, SegmentCore.control, SegmentCore.discard, branch, setCount, fetching, both, either, field, kind, count, *]
  all_goals done

set_option linter.unusedSimpArgs false in
theorem fetch_keeps_tx (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (fetch : s (.base .phase) = 1#3) :
    ((circuit a registered).step i s) (.base .txConsumed) = s (.base .txConsumed) := by
  change (bindWord (word registered) (next (.base .txConsumed))).eval i s = _
  rw [bindWord_eval]
  simp [next, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput, decodedRegister,
    withFetch, lift, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting,
    Core.cmd, Core.both, Core.either, Core.free, Core.starting, Core.releasing, Core.hostOwner,
    Core.owned, Core.retained, Core.isPhase, Core.reserving, Core.takingTX, ordinary.1, ordinary.2, fetch]

theorem held_low (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (phase : s (.base .phase) = 3#3) (within : inputs.length ≤ (s (.base .countdown)).toNat)
    (ordinary : ∀ i ∈ inputs, DrainInput i) :
    Held s (SegmentTiming.run registered s inputs) := by
  induction inputs generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons i rest ih =>
    have one : [@i].length ≤ (s (.base .countdown)).toNat := by
      simp only [List.length_cons, List.length_nil]
      simp only [List.length_cons] at within
      omega
    have drain := ordinary i (by simp)
    let after : Values (Register a) := (circuit a registered).step i s
    have step : SegmentStreamStep.LowSpan s after 1 :=
      SegmentStreamStep.low_span registered s [@i] phase one (by simpa using drain)
    have preserved := hold registered i s (noReset drain) (.inr (.inr ⟨phase, by
      intro zero
      simp [zero] at one⟩))
    have nextWithin : rest.length ≤ (after (.base .countdown)).toNat := by
      rw [step.countdown]
      simp only [List.length_cons] at within
      omega
    exact preserved.trans (ih after step.phase nextWithin
      (fun j hj => ordinary j (List.mem_cons_of_mem (α := Values Core.Input) i hj)))

/-- The live stream word has been loaded and the next slot awaits credit. -/
structure AtReservation (rows : List Row) (pc : Nat) (cell : Cell) (guard : Option Guard) (previous : Option Bool)
    (s : Values (Register a)) : Prop where
  installed : Installed rows s
  phase : s (.base .phase) = 2#3
  position : (s (.base .pc)).toNat = pc
  current : s (.base .currentWord) = encode (.stream cell guard)
  latched : HasCapture s previous

structure Parked (rows : List Row) (pc : Nat) (cell : Cell) (guard : Option Guard) (previous : Option Bool)
    (s after : Values (Register a)) : Prop where
  ready : AtReservation rows pc cell guard previous after
  remaining : after (.base .remaining) = s (.base .remaining)
  levels : after (.base .levels) = s (.base .levels)
  enabled : after (.base .enabled) = s (.base .enabled)
  reserved : after (.base .txConsumed) = s (.base .txConsumed)
  produced : after (.base .rxProduced) = s (.base .rxProduced)

theorem run_parks (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    {guard : Option Guard}
    (start : AtReservation rows pc cell guard previous s) (history : ParkHistory registered s inputs) :
    Parked rows pc cell guard previous s (SegmentTiming.run registered s inputs) ∧ ActiveClocks registered s inputs := by
  induction inputs generalizing s with
  | nil => exact ⟨⟨start, rfl, rfl, rfl, rfl, rfl⟩, .nil⟩
  | cons i rest ih =>
    have ordinary := history.1
    have edge := SegmentStreamStep.park_runtime registered i s ordinary start.phase history.2.1
    have image := image_frame registered i s ordinary (.inl (by simp [start.phase]))
    have held := hold registered i s ordinary (.inr (.inl start.phase))
    have ready := AtReservation.mk (image.installed start.installed) edge.phase
      ((congrArg BitVec.toNat edge.pc).trans start.position) (edge.pose.current.trans start.current)
      (held.capture start.latched)
    obtain ⟨tail, active⟩ := ih _ ready history.2.2
    exact ⟨⟨tail.ready, tail.remaining.trans edge.pose.remaining, tail.levels.trans edge.pose.levels,
      tail.enabled.trans edge.pose.enabled, tail.reserved.trans edge.reserved,
      tail.produced.trans edge.produced⟩,
      .cons ordinary (by simp [start.phase]) (by simp [start.phase]) (by simp [start.phase]) active⟩

structure SlotEnd (registered : Bool) (rows : List Row) (pc : Nat) (cell : Cell)
    (previous : Option Bool) (s after : Values (Register a)) : Prop where
  remaining : (after (.base .remaining)).toNat = (s (.base .remaining)).toNat - 1
  produced : after (.base .rxProduced) = s (.base .rxProduced) + (if cell.receive then 1#16 else 0)
  consumed : after (.base .txConsumed) = s (.base .txConsumed) + (if cell.transmit then 1#16 else 0)
  repeatCell : 1 < (s (.base .remaining)).toNat → AtReservation rows pc cell none previous after
  finished : (s (.base .remaining)).toNat = 1 → AtBoundary registered rows (pc + 1) previous after

/-- A served slot advances to its next counted reservation or completes its row. -/
theorem run_slot (registered : Bool) (cell : Cell) (slot : SlotPlan) (s : Values (Register a))
    (start : AtReservation rows pc cell none previous s) (inBounds : pc < rows.length)
    (positive : 0 < (s (.base .remaining)).toNat) (service : slot.Served registered cell s) :
    SlotEnd registered rows pc cell (if cell.receive then some (slot.sample registered cell s) else previous)
      s (slot.after registered s) ∧ ActiveClocks registered s slot.inputs := by
  let ready : Values (Register a) := slot.ready registered s
  obtain ⟨parks, parkActive⟩ := run_parks registered s slot.parks start service.parks
  have parked : AtReservation rows pc cell none previous ready := parks.ready
  let reserved : Values (Register a) := (circuit a registered).step slot.admit ready
  let lowEnd : Values (Register a) := slot.lowEnd registered s
  let entered : Values (Register a) := (circuit a registered).step slot.aperture lowEnd
  let highEnd : Values (Register a) := slot.highEnd registered s
  have reserve := SegmentStreamStep.reserve_runtime registered slot.admit ready cell none service.admit parked.phase
    parked.current service.credit
  have lowTimer : (reserved (.base .countdown)).toNat = slot.low.length := by
    have programmed := congrArg BitVec.toNat reserve.countdown
    change (reserved (.base .countdown)).toNat = (BitVec.ofNat 8 cell.lowDuration.val).toNat at programmed
    simpa [Nat.mod_eq_of_lt cell.lowDuration.isLt, service.lowTicks] using programmed
  have lowWithin : slot.low.length ≤ (reserved (.base .countdown)).toNat := Nat.le_of_eq lowTimer.symm
  have low : SegmentStreamStep.LowSpan reserved lowEnd slot.low.length :=
    SegmentStreamStep.low_span registered reserved slot.low reserve.phase lowWithin service.low
  have lowExpired : lowEnd (.base .countdown) = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    change (lowEnd (.base .countdown)).toNat = 0
    rw [low.countdown, lowTimer, Nat.sub_self]
  have held := (hold registered slot.admit ready service.admit (.inr (.inl parked.phase))).trans
    (held_low registered reserved slot.low reserve.phase lowWithin service.low)
  have sampled := SegmentCapture.capture registered slot.aperture lowEnd cell service.aperture
    low.phase lowExpired (low.pose.current.trans (reserve.current.trans parked.current)) (held.capture parked.latched)
  have highTimer : (entered (.base .countdown)).toNat = slot.high.length := by
    have programmed := congrArg BitVec.toNat sampled.countdown
    simpa [Nat.mod_eq_of_lt cell.highDuration.isLt, service.highTicks] using programmed
  have high : HighPrefix entered highEnd slot.high.length
      (if cell.receive then some (slot.sample registered cell s) else previous) :=
    high_prefix registered entered slot.high service.high sampled.high (Nat.le_of_eq highTimer.symm) sampled.latched
  have highExpired : highEnd (.base .countdown) = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    change (highEnd (.base .countdown)).toNat = 0
    rw [high.countdown, highTimer, Nat.sub_self]
  have current : highEnd (.base .currentWord) = encode (.stream cell none) :=
    high.current.trans (sampled.current.trans (low.pose.current.trans (reserve.current.trans parked.current)))
  have stream : IsStream highEnd := by
    change (highEnd (.base .currentWord)).extractLsb' 0 3 = 1#3
    rw [current]
    exact (encode_fields (.stream cell none)).operation
  have position : (highEnd (.base .pc)).toNat = pc :=
    (congrArg BitVec.toNat (high.pc.trans (sampled.pc.trans (low.pc.trans reserve.pc)))).trans parked.position
  have remaining : (highEnd (.base .remaining)).toNat = (s (.base .remaining)).toNat :=
    congrArg BitVec.toNat (high.remaining.trans (sampled.remaining.trans
      (low.pose.remaining.trans (reserve.remaining.trans parks.remaining))))
  have installed := high.image.installed
    ((image_frame registered slot.aperture lowEnd service.aperture (.inl (by simp [low.phase]))).installed
      (low.image.installed ((image_frame registered slot.admit ready service.admit
        (.inl (by simp [parked.phase]))).installed parked.installed)))
  have exit : HighStep highEnd (slot.after registered s) (decide (highEnd (.base .countdown) = 0#8))
      (decide (IsStream highEnd)) (decide (IsStream highEnd ∧ 1 < (highEnd (.base .remaining)).toNat)) :=
    high_step registered slot.leave highEnd service.leave high.phase
  have expiredBit := decide_eq_true highExpired
  have streamBit := decide_eq_true stream
  have canDecrease : (1 : BitVec 16) ≤ highEnd (.base .remaining) := by
    change 1 ≤ (highEnd (.base .remaining)).toNat
    rwa [remaining]
  have left : (slot.after registered s) (.base .remaining) = highEnd (.base .remaining) - 1 := by
    simpa only [expiredBit, streamBit, Bool.true_and, if_true] using exit.remaining
  refine ⟨⟨?_, exit.produced.trans (high.produced.trans (sampled.produced.trans
    (congrArg (· + (if cell.receive then 1#16 else 0)) (held.produced.trans parks.produced)))),
    exit.reserved.trans (high.reserved.trans (sampled.reserved.trans
      (low.reserved.trans (reserve.txConsumed.trans
        (congrArg (· + (if cell.transmit then 1#16 else 0#16)) parks.reserved))))), ?_, ?_⟩, ?_⟩
  · rw [left, BitVec.toNat_sub_of_le canDecrease, remaining]
    rfl
  · intro repeats
    have again : IsStream highEnd ∧ 1 < (highEnd (.base .remaining)).toNat := ⟨stream, by rwa [remaining]⟩
    have againBit := decide_eq_true again
    have phase : (slot.after registered s) (.base .phase) = 2#3 := by
      simpa only [expiredBit, againBit, if_true] using exit.phase
    have nextPC : (slot.after registered s) (.base .pc) = highEnd (.base .pc) := by
      simpa only [expiredBit, againBit, Bool.not_true, Bool.and_false, Bool.false_eq_true,
        if_false] using exit.pc
    exact ⟨(image_frame registered slot.leave highEnd service.leave (.inl (by simp [high.phase]))).installed installed,
      phase, (congrArg BitVec.toNat nextPC).trans position, exit.current.trans current,
      high_capture_frame registered slot.leave highEnd service.leave high.phase high.latched⟩
  · intro one
    exact high_to_boundary_step registered slot.leave highEnd service.leave high.phase highExpired
      (fun h => by rw [remaining, one] at h; exact (Nat.lt_irrefl 1) h.2)
      installed position inBounds high.latched
  · have lowActive : ActiveClocks registered reserved slot.low := by
      apply ActiveClocks.of_prefixes registered reserved slot.low 3 (by decide) (by decide) (by decide)
        (fun i member => noReset (service.low i member))
      intro before after i split
      apply (SegmentStreamStep.low_span registered reserved before reserve.phase ?_ ?_).phase
      · rw [split, List.length_append] at lowWithin
        omega
      · intro input member
        apply service.low input
        rw [split]
        exact List.mem_append_left _ member
    have highWithin : slot.high.length ≤ (entered (.base .countdown)).toNat := Nat.le_of_eq highTimer.symm
    have highActive : ActiveClocks registered entered slot.high := by
      apply ActiveClocks.of_prefixes registered entered slot.high 4 (by decide) (by decide) (by decide) service.high
      intro before after i split
      apply (high_prefix registered entered before ?_ sampled.high ?_ sampled.latched).phase
      · intro input member
        apply service.high input
        rw [split]
        exact List.mem_append_left _ member
      · rw [split, List.length_append] at highWithin
        omega
    have leave : ActiveClocks registered highEnd [@slot.leave] :=
      .cons service.leave (by simp [high.phase]) (by simp [high.phase]) (by simp [high.phase]) .nil
    have aperture : ActiveClocks registered lowEnd ((@slot.aperture) :: (slot.high ++ [@slot.leave])) :=
      .cons service.aperture (by simp [low.phase]) (by simp [low.phase]) (by simp [low.phase])
        (highActive.append leave)
    exact parkActive.append (.cons service.admit (by simp [parks.ready.phase]) (by simp [parks.ready.phase])
      (by simp [parks.ready.phase]) (lowActive.append aperture))

/-- A completed stream advances once, spends its count, and qualifies one
    sample per receiving slot. The RX counter is the RTL's 16-bit counter. -/
structure Completed (registered : Bool) (rows : List Row) (pc : Nat) (cell : Cell)
    (last : Option Bool) (slots : Nat) (s after : Values (Register a)) : Prop where
  boundary : AtBoundary registered rows (pc + 1) last after
  remaining : after (.base .remaining) = 0#16
  produced : after (.base .rxProduced) = s (.base .rxProduced) +
    (if cell.receive then BitVec.ofNat 16 slots else 0#16)
  consumed : after (.base .txConsumed) = s (.base .txConsumed) +
    (if cell.transmit then BitVec.ofNat 16 slots else 0#16)

private theorem add_one_slot (counter : BitVec 16) (slots : Nat) (enabled : Bool) :
    (counter + (if enabled then 1#16 else 0)) + (if enabled then BitVec.ofNat 16 slots else 0) =
      counter + (if enabled then BitVec.ofNat 16 (slots + 1) else 0) := by
  cases enabled
  · simp
  · simp only [if_true, BitVec.ofNat_add, BitVec.add_assoc]
    rw [BitVec.add_comm 1#16 (BitVec.ofNat 16 slots)]

private theorem run_slots (registered : Bool) (cell : Cell) (s : Values (Register a))
    (slots : List SlotPlan) (start : AtReservation rows pc cell none previous s) (inBounds : pc < rows.length)
    (positive : 0 < slots.length) (count : (s (.base .remaining)).toNat = slots.length)
    (service : Served registered cell s slots) :
    Completed registered rows pc cell (captured registered cell s previous slots) slots.length s
      (runSlots registered s slots) ∧ ActiveClocks registered s (slots.flatMap SlotPlan.inputs) := by
  induction slots generalizing s previous with
  | nil => simp at positive
  | cons slot rest ih =>
    rw [runSlots_cons]
    change _ ∧ _ at service
    obtain ⟨step, active⟩ := run_slot registered cell slot s start inBounds (by rwa [count]) service.1
    have appendActive (tail : ActiveClocks registered (slot.after registered s) (rest.flatMap SlotPlan.inputs)) :
        ActiveClocks registered s ((slot :: rest).flatMap SlotPlan.inputs) := by
      have next : ActiveClocks registered (SegmentTiming.run registered s slot.inputs) (rest.flatMap SlotPlan.inputs) :=
        (slot.run_inputs registered s).symm ▸ tail
      exact active.append next
    cases rest with
    | nil =>
      have one : (s (.base .remaining)).toNat = 1 := by simpa using count
      refine ⟨⟨step.finished one, BitVec.eq_of_toNat_eq ?_, step.produced, step.consumed⟩, appendActive .nil⟩
      · change ((slot.after registered s) (.base .remaining)).toNat = 0
        rw [step.remaining, one, Nat.sub_self]
    | cons next rest =>
      have repeats : 1 < (s (.base .remaining)).toNat := by simp [count]
      have restCount : ((slot.after registered s) (.base .remaining)).toNat = (next :: rest).length := by
        rw [step.remaining, count, List.length_cons, Nat.add_sub_cancel]
      obtain ⟨tail, activeTail⟩ := ih (slot.after registered s) (step.repeatCell repeats) (by simp) restCount service.2
      refine ⟨⟨tail.boundary, tail.remaining, ?_, ?_⟩, appendActive activeTail⟩
      · rw [tail.produced, step.produced]
        exact add_one_slot _ _ _
      · rw [tail.consumed, step.consumed]
        exact add_one_slot _ _ _

/-- A fetched unguarded stream enters its first reservation boundary. -/
theorem load_row (registered : Bool) (cell : Cell) (s : Values (Register a)) (fetch : Values Core.Input)
    (start : AtBoundary registered rows pc previous s) (ordinary : NoReset fetch)
    (row : rows[pc]? = some (.cell (.stream cell none)))
    (nonzero : s (.base .remaining) ≠ 0#16) :
    let live : Values (Register a) := (circuit a registered).step fetch s
    AtReservation rows pc cell none previous live ∧ live (.base .remaining) = s (.base .remaining) ∧
      live (.base .rxProduced) = s (.base .rxProduced) ∧ live (.base .txConsumed) = s (.base .txConsumed) := by
  let live : Values (Register a) := (circuit a registered).step fetch s
  have inBounds := (List.getElem?_eq_some_iff.mp row).1
  have selected := selected_row start fetch row
  have atFetch : SegmentControl.AtFetch fetch s :=
    ⟨ordinary.1, ordinary.2, start.phase, by rw [start.position, start.installed.count]; exact inBounds⟩
  have loaded := SegmentStreamStep.load_stream registered fetch s cell none atFetch trivial nonzero selected
  have stream : ((word registered).eval fetch s).extractLsb' 0 3 = 1#3 := by
    rw [selected]
    exact (encode_fields (.stream cell none)).operation
  have held := hold registered fetch s ordinary (.inl ⟨start.phase, stream⟩)
  have installed := (image_frame registered fetch s ordinary (.inl (by simp [start.phase]))).installed start.installed
  have ready : AtReservation rows pc cell none previous live := ⟨installed, loaded.phase,
    (congrArg BitVec.toNat loaded.pc).trans start.position, loaded.current, held.capture start.latched⟩
  exact ⟨ready, loaded.remaining, held.produced, fetch_keeps_tx registered fetch s ordinary start.phase⟩

/-- Execute the installed unguarded stream from its FETCH boundary through
    all counted slots. The inputs are `fetch :: slots.flatMap SlotPlan.inputs`. -/
theorem run_stream_row (registered : Bool) (cell : Cell) (s : Values (Register a)) (fetch : Values Core.Input)
    (slots : List SlotPlan) (start : AtBoundary registered rows pc previous s) (ordinary : NoReset fetch)
    (row : rows[pc]? = some (.cell (.stream cell none)))
    (positive : 0 < slots.length) (count : (s (.base .remaining)).toNat = slots.length)
    (service : Served registered cell ((circuit a registered).step fetch s) slots) :
    Completed registered rows pc cell
      (captured registered cell ((circuit a registered).step fetch s) previous slots) slots.length s
      (SegmentTiming.run registered s ((@fetch) :: slots.flatMap SlotPlan.inputs)) ∧
      ActiveClocks registered s ((@fetch) :: slots.flatMap SlotPlan.inputs) := by
  let live : Values (Register a) := (circuit a registered).step fetch s
  have nonzero : s (.base .remaining) ≠ 0#16 := by
    intro zero
    simp [zero] at count
    omega
  obtain ⟨ready, loadedCount, rx, tx⟩ := load_row registered cell s fetch start ordinary row nonzero
  obtain ⟨run, active⟩ := run_slots registered cell live slots ready (List.getElem?_eq_some_iff.mp row).1 positive
    ((congrArg BitVec.toNat loadedCount).trans count) service
  exact ⟨⟨run.boundary, run.remaining, run.produced.trans (congrArg (· + _) rx),
    run.consumed.trans (congrArg (· + _) tx)⟩,
    .cons ordinary (by simp [start.phase]) (by simp [start.phase]) (by simp [start.phase]) active⟩

end Pinwheel.Hardware.StreamingReady.SegmentUnguardedReceive
