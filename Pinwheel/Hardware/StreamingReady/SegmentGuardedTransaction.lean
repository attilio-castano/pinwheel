import Pinwheel.Hardware.StreamingReady.SegmentUnguardedReceive
import Pinwheel.Hardware.StreamingReady.SegmentTransactionTimeout
import Pinwheel.Hardware.StreamingReady.SegmentEventWait

/-! Execution of guarded stream slots through qualification or bounded expiry. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentGuardedTransaction

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTiming
open Pinwheel.Program.StreamingReady
open Pinwheel.Program.StreamingReadySegments (Row Cursor Successors successors)
open Pinwheel.Program.StreamingReadySegments.Execution (pollWindow)
open ProtocolOwnership (AtDeadline DrainInput)
open SegmentTransaction (ActiveClocks Cut ServiceSpan)
open SegmentTransactionTimeout (TimeoutSpan)
open SegmentUnguardedReceive (AtReservation ParkHistory)

/-- Concrete inputs through a slot's last eligible poll. The ordinary prefix
    ends immediately before the input that qualifies or expires the slot. -/
structure AperturePlan where
  admit : Values Core.Input
  low : List (Values Core.Input)
  arm : Values Core.Input
  misses : List (Values Core.Input)
  poll : Values Core.Input
  parks : List (Values Core.Input) := []

def AperturePlan.prefix (plan : AperturePlan) : List (Values Core.Input) :=
  plan.parks ++ @plan.admit :: (plan.low ++ @plan.arm :: plan.misses)

def AperturePlan.ready (plan : AperturePlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) := run registered s plan.parks

def AperturePlan.lowEnd (plan : AperturePlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) := run registered ((circuit a registered).step plan.admit (plan.ready registered s)) plan.low

def AperturePlan.entered (plan : AperturePlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) := (circuit a registered).step plan.arm (plan.lowEnd registered s)

def AperturePlan.beforePoll (plan : AperturePlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) := run registered (plan.entered registered s) plan.misses

def AperturePlan.afterPoll (plan : AperturePlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) := (circuit a registered).step plan.poll (plan.beforePoll registered s)

def AperturePlan.samples (plan : AperturePlan) (registered : Bool) (s : Values (Register a)) : List (BitVec 2) :=
  SegmentPollRefinement.stage2Samples registered (plan.entered registered s) plan.misses ++
    [plan.beforePoll registered s (.base .stage2)]

theorem AperturePlan.run_prefix (plan : AperturePlan) (registered : Bool) (s : Values (Register a)) :
    @run a registered s plan.prefix = @AperturePlan.beforePoll a plan registered s := by
  unfold AperturePlan.prefix
  rw [run_append]
  change @run a registered ((circuit a registered).step plan.admit (plan.ready registered s))
    (plan.low ++ @plan.arm :: plan.misses) = _
  rw [run_append]
  rfl

structure AperturePlan.Delivered (plan : AperturePlan) (registered : Bool) (cell : Cell) (limit : WaitLimit)
    (s : Values (Register a)) : Prop where
  parks : ParkHistory registered s plan.parks
  admit : NoReset plan.admit
  credit : Core.credit.eval plan.admit (project (plan.ready registered s)) = 1#1
  lowTicks : plan.low.length = cell.lowDuration.val
  low : ∀ i ∈ plan.low, DrainInput i
  arm : DrainInput plan.arm
  history : MissHistory registered (plan.entered registered s) plan.misses
  within : match limit with
    | .unbounded => True
    | .misses n => plan.misses.length ≤ n.val
  poll : DrainInput plan.poll

structure SlotPlan extends AperturePlan where
  high : List (Values Core.Input)
  leave : Values Core.Input

def SlotPlan.inputs (plan : SlotPlan) : List (Values Core.Input) :=
  plan.prefix ++ @plan.poll :: (plan.high ++ [@plan.leave])

def SlotPlan.highEnd (plan : SlotPlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) := run registered (plan.afterPoll registered s) plan.high

def SlotPlan.after (plan : SlotPlan) (registered : Bool) (s : Values (Register a)) :
    Values (Register a) := (circuit a registered).step plan.leave (plan.highEnd registered s)

def SlotPlan.sample (plan : SlotPlan) (registered : Bool) (cell : Cell) (s : Values (Register a)) : Bool :=
  (plan.beforePoll registered s (.base .stage2))[cell.rxInput.val]

theorem SlotPlan.run_inputs (plan : SlotPlan) (registered : Bool) (s : Values (Register a)) :
    @run a registered s plan.inputs = @SlotPlan.after a plan registered s := by
  unfold SlotPlan.inputs
  rw [run_append, AperturePlan.run_prefix]
  change @run a registered (plan.afterPoll registered s) (plan.high ++ [@plan.leave]) = _
  rw [run_append]
  rfl

structure SlotPlan.Served (plan : SlotPlan) (registered : Bool) (cell : Cell) (g : Guard) (limit : WaitLimit)
    (s : Values (Register a)) : Prop where
  aperture : plan.toAperturePlan.Delivered registered cell limit s
  qualified : g.matches (plan.beforePoll registered s (.base .stage2)) = true
  highTicks : plan.high.length = cell.highDuration.val
  high : ∀ i ∈ plan.high, NoReset i
  leave : NoReset plan.leave

def Served (registered : Bool) (cell : Cell) (g : Guard) (limit : WaitLimit) (s : Values (Register a)) :
    List SlotPlan → Prop
  | [] => True
  | plan :: rest => plan.Served registered cell g limit s ∧ Served registered cell g limit (plan.after registered s) rest

private theorem noReset (h : DrainInput i) : NoReset i := ⟨h.1, by simp [h.2.1]⟩

private structure WaitFrame (s after : Values (Register a)) : Prop where
  pc : after (.base .pc) = s (.base .pc)
  reserved : after (.base .txConsumed) = s (.base .txConsumed)

private theorem base_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) : (circuit a registered).step i s (.base r) =
      (nextBase r).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

set_option linter.unusedSimpArgs false in
private theorem wait_frame (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : DrainInput i) (active : s (.base .phase) = 3#3 ∨ s (.base .phase) = 7#3)
    (stream : IsStream s) : WaitFrame s ((circuit a registered).step i s) := by
  have operation : (s (.base .currentWord)).extractLsb' 0 3 = 1#3 := stream
  rcases active with phase | phase <;>
    refine ⟨?_, ?_⟩ <;>
    simp [base_step, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
      withFetch, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting,
      Core.cmd, Core.both, Core.either, Core.free, Core.starting, Core.releasing, Core.hostOwner,
      Core.owned, Core.retained, Core.isPhase, Core.fetching, Core.advancing, Core.highEnd,
      Core.standaloneSuccess, Core.waitSuccess, Core.stream, Core.field, lift, decodedRegister,
      Core.takingTX, Core.reserving, Core.clearedRuntime,
      SegmentCore.discard, branch, setCount, fetching, both, either, ordinary.1, ordinary.2.1, phase, operation]

private theorem WaitFrame.trans {s mid after : Values (Register a)} (left : WaitFrame s mid)
    (right : WaitFrame mid after) : WaitFrame s after :=
  ⟨right.pc.trans left.pc, right.reserved.trans left.reserved⟩

private theorem misses_frame (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (waiting : s (.base .phase) = 7#3) (stream : IsStream s) (bounded : guardBudget s ≠ 0#8)
    (history : MissHistory registered s inputs) (within : inputs.length ≤ (s (.base .countdown)).toNat) :
    WaitFrame s (run registered s inputs) ∧ ActiveClocks registered s inputs := by
  induction inputs generalizing s with
  | nil => exact ⟨⟨rfl, rfl⟩, .nil⟩
  | cons i rest ih =>
    obtain ⟨ordinary, miss, later⟩ := history
    have one : [@i].length ≤ (s (.base .countdown)).toNat := by
      simp only [List.length_cons, List.length_nil] at within ⊢
      omega
    let after : Values (Register a) := (circuit a registered).step i s
    have step : MissCut s after 1 := miss_prefix registered s [@i] waiting bounded ⟨ordinary, miss, trivial⟩ one
    have nextBounded : guardBudget after ≠ 0#8 := by
      simpa only [guardBudget, step.pose.current] using bounded
    have nextWithin : rest.length ≤ (after (.base .countdown)).toNat := by
      rw [step.countdown]
      simp only [List.length_cons] at within
      omega
    have nextStream : IsStream after := by simpa only [IsStream, step.pose.current] using stream
    obtain ⟨tail, active⟩ := ih after step.phase nextStream nextBounded later nextWithin
    exact ⟨(wait_frame registered i s ordinary (.inr waiting) stream).trans tail,
      .cons (noReset ordinary) (by simp [waiting]) (by simp [waiting]) (by simp [waiting]) active⟩

set_option linter.unusedSimpArgs false in
private theorem arm_preserves_rx (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : DrainInput i) (low : s (.base .phase) = 3#3) (stream : IsStream s)
    (guarded : (s (.base .currentWord)).extractLsb' 62 1 = 1#1) :
    ((circuit a registered).step i s) (.base .rxProduced) = s (.base .rxProduced) := by
  have operation : (s (.base .currentWord)).extractLsb' 0 3 = 1#3 := stream
  simp [base_step, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
    withFetch, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting,
    Core.cmd, Core.both, Core.either, Core.free, Core.starting, Core.releasing, Core.hostOwner,
    Core.owned, Core.retained, Core.isPhase, Core.clearedRuntime, Core.capturingRX, Core.capture,
    Core.lowEnd, Core.highGuard, Core.waitSuccess, Core.field, lift, decodedRegister,
    Core.stream, ordinary.1, ordinary.2.1, low, guarded, operation]

private structure Prepared (registered : Bool) (plan : AperturePlan) (cell : Cell) (g : Guard)
    (limit : WaitLimit) (s : Values (Register a)) : Prop where
  low : plan.lowEnd registered s (.base .phase) = 3#3
  elapsed : plan.lowEnd registered s (.base .countdown) = 0#8
  lowWord : plan.lowEnd registered s (.base .currentWord) = encode (.stream cell (some g))
  waiting : plan.beforePoll registered s (.base .phase) = 7#3
  countdown : (plan.beforePoll registered s (.base .countdown)).toNat =
    limit.initialCountdown.toNat - plan.misses.length
  current : plan.beforePoll registered s (.base .currentWord) = encode (.stream cell (some g))
  pc : plan.beforePoll registered s (.base .pc) = s (.base .pc)
  remaining : plan.beforePoll registered s (.base .remaining) = s (.base .remaining)
  reserved : plan.beforePoll registered s (.base .txConsumed) =
    s (.base .txConsumed) + (if cell.transmit then 1#16 else 0#16)
  produced : plan.beforePoll registered s (.base .rxProduced) = s (.base .rxProduced)
  active : ActiveClocks registered s plan.prefix

private theorem prepare (registered : Bool) (plan : AperturePlan) (cell : Cell) (g : Guard)
    (schedule : WaitLimit) (limit : g.limit = schedule) (s : Values (Register a))
    (start : AtReservation rows pc cell (some g) previous s) (service : plan.Delivered registered cell schedule s) :
    Prepared registered plan cell g schedule s := by
  let ready : Values (Register a) := plan.ready registered s
  let reserved : Values (Register a) := (circuit a registered).step plan.admit ready
  let lowEnd : Values (Register a) := plan.lowEnd registered s
  let entered : Values (Register a) := plan.entered registered s
  obtain ⟨parks, parkActive⟩ := SegmentUnguardedReceive.run_parks registered s plan.parks start service.parks
  have park : AtReservation rows pc cell (some g) previous ready := parks.ready
  have reserve := SegmentStreamStep.reserve_runtime registered plan.admit ready cell (some g) service.admit
    park.phase park.current service.credit
  have lowTimer : (reserved (.base .countdown)).toNat = plan.low.length := by
    have programmed := congrArg BitVec.toNat reserve.countdown
    change (reserved (.base .countdown)).toNat = (BitVec.ofNat 8 cell.lowDuration.val).toNat at programmed
    simpa [Nat.mod_eq_of_lt cell.lowDuration.isLt, service.lowTicks] using programmed
  have lowWithin : plan.low.length ≤ (reserved (.base .countdown)).toNat := Nat.le_of_eq lowTimer.symm
  have low : SegmentStreamStep.LowSpan reserved lowEnd plan.low.length :=
    SegmentStreamStep.low_span registered reserved plan.low reserve.phase lowWithin service.low
  have expired : lowEnd (.base .countdown) = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    change (lowEnd (.base .countdown)).toNat = 0
    rw [low.countdown, lowTimer, Nat.sub_self]
  have lowWord : lowEnd (.base .currentWord) = encode (.stream cell (some g)) :=
    low.pose.current.trans (reserve.current.trans park.current)
  have arm := enter_guarded_aperture registered plan.arm lowEnd cell g service.arm low.phase expired lowWord
  have entryWord : entered (.base .currentWord) = encode (.stream cell (some g)) := arm.current.trans lowWord
  have fields := encode_fields (.stream cell (some g))
  have isStream (state : Values (Register a))
      (loaded : state (.base .currentWord) = encode (.stream cell (some g))) : IsStream state := by
    change (state (.base .currentWord)).extractLsb' 0 3 = 1#3
    rw [loaded]
    exact fields.operation
  let poll : Values (Register a) := plan.beforePoll registered s
  have encodedBudget : guardBudget entered = schedule.budget := by
    rw [guardBudget, entryWord, fields.guardBudget]
    exact congrArg WaitLimit.budget limit
  have waitCount : entered (.base .countdown) = schedule.initialCountdown :=
    arm.countdown.trans (congrArg WaitLimit.initialCountdown limit)
  have waited : poll (.base .phase) = 7#3 ∧
      (poll (.base .countdown)).toNat = schedule.initialCountdown.toNat - plan.misses.length ∧
      WaitPose entered poll ∧ poll (.base .rxProduced) = entered (.base .rxProduced) ∧
      WaitFrame entered poll ∧ ActiveClocks registered entered plan.misses := by
    cases schedule with
    | unbounded =>
      obtain ⟨held, active⟩ := SegmentEventWait.hold_misses registered entered plan.misses arm.phase
        encodedBudget service.history
      have timer := congrArg BitVec.toNat (held.countdown.trans waitCount)
      exact ⟨held.phase, by
        change (run registered entered plan.misses (.base .countdown)).toNat = _
        simpa [WaitLimit.initialCountdown] using timer, held.pose, held.captured,
        ⟨held.pc, held.reserved⟩, active⟩
    | misses n =>
      have bounded : guardBudget entered ≠ 0#8 := encodedBudget ▸ SourceRefinement.budget_nonzero n
      have elapsed : plan.misses.length ≤ (entered (.base .countdown)).toNat := by
        rw [waitCount]
        simpa [WaitLimit.initialCountdown, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n.val < 256 by omega)]
          using service.within
      have held := miss_prefix registered entered plan.misses arm.phase bounded service.history elapsed
      obtain ⟨frame, active⟩ := misses_frame registered entered plan.misses arm.phase
        (isStream entered entryWord) bounded service.history elapsed
      exact ⟨held.phase, held.countdown.trans (congrArg (· - _) (congrArg BitVec.toNat waitCount)),
        held.pose, held.captured, frame, active⟩
  obtain ⟨waitPhase, waitTimer, waitPose, waitCapture, wait, activeWait⟩ := waited
  have armFrame := wait_frame registered plan.arm lowEnd service.arm (.inl low.phase)
    (isStream lowEnd lowWord)
  have lowActive : ActiveClocks registered reserved plan.low := by
    apply ActiveClocks.of_prefixes registered reserved plan.low 3 (by decide) (by decide) (by decide)
      (fun i member => noReset (service.low i member))
    intro before after i split
    apply (SegmentStreamStep.low_span registered reserved before reserve.phase ?_ ?_).phase
    · rw [split, List.length_append] at lowWithin
      omega
    · intro input member
      apply service.low input
      rw [split]
      exact List.mem_append_left _ member
  have activeArm : ActiveClocks registered lowEnd (@plan.arm :: plan.misses) :=
    .cons (noReset service.arm) (by simp [low.phase]) (by simp [low.phase]) (by simp [low.phase]) activeWait
  have activeAdmit : ActiveClocks registered ready (@plan.admit :: (plan.low ++ @plan.arm :: plan.misses)) :=
    .cons service.admit (by simp [park.phase]) (by simp [park.phase]) (by simp [park.phase])
      (lowActive.append activeArm)
  have active : ActiveClocks registered s plan.prefix := parkActive.append activeAdmit
  have held := (SegmentUnguardedReceive.hold registered plan.admit ready service.admit
    (.inr (.inl park.phase))).trans
    (SegmentUnguardedReceive.held_low registered reserved plan.low reserve.phase lowWithin service.low)
  refine ⟨low.phase, expired, lowWord, waitPhase, waitTimer,
    waitPose.current.trans entryWord, ?_, ?_, ?_, ?_, active⟩
  · exact wait.pc.trans (armFrame.pc.trans (low.pc.trans (reserve.pc.trans
      ((BitVec.eq_of_toNat_eq ((park.position).trans start.position.symm))))))
  · exact waitPose.remaining.trans (arm.remaining.trans
      (low.pose.remaining.trans (reserve.remaining.trans parks.remaining)))
  · exact wait.reserved.trans (armFrame.reserved.trans (low.reserved.trans (reserve.txConsumed.trans
      (congrArg (· + _) parks.reserved))))
  · exact waitCapture.trans ((arm_preserves_rx registered plan.arm lowEnd service.arm low.phase (isStream lowEnd lowWord)
      (lowWord ▸ fields.highGuard)).trans (held.produced.trans parks.produced))

/-- The guarded slot's verdict uses the same inclusive window as executable
    segment source, including qualification on the last eligible clock. -/
theorem aperture_poll (registered : Bool) (plan : AperturePlan) (cell : Cell) (g : Guard)
    (n : Fin 255) (limit : g.limit = .misses n) (receive : cell.receive = true) (s : Values (Register a))
    (start : AtReservation rows pc cell (some g) previous s) (service : plan.Delivered registered cell (.misses n) s) :
    let sample := plan.beforePoll registered s (.base .stage2)
    pollWindow g (plan.samples registered s) = if g.matches sample then some (some sample)
      else if plan.misses.length == n.val then some none else none := by
  have prepared := prepare registered plan cell g (.misses n) limit s start service
  exact (SegmentPollRefinement.guarded_stream_poll registered (plan.lowEnd registered s) cell g n
    limit receive plan.arm plan.poll plan.misses service.arm service.poll prepared.low prepared.elapsed
    prepared.lowWord service.history service.within).1

private theorem bounded_word {s : Values (Register a)} (loaded : s (.base .currentWord) = encode (.stream cell (some g)))
    (limit : g.limit = .misses n) : guardBudget s ≠ 0#8 := by
  rw [guardBudget, loaded, (encode_fields (.stream cell (some g))).guardBudget]
  change g.limit.budget ≠ 0#8
  rw [limit]
  exact SourceRefinement.budget_nonzero n

/-- A failed guarded slot reaches the last unqualified poll after reserving
    its TX bit. RX length still describes the successful prefix. -/
structure Deadline (registered : Bool) (plan : AperturePlan) (cell : Cell) (g : Guard)
    (s : Values (Register a)) : Prop where
  active : ActiveClocks registered s plan.prefix
  deadline : AtDeadline plan.poll (plan.beforePoll registered s)
  current : plan.beforePoll registered s (.base .currentWord) = encode (.stream cell (some g))
  pc : plan.beforePoll registered s (.base .pc) = s (.base .pc)
  remaining : plan.beforePoll registered s (.base .remaining) = s (.base .remaining)
  reserved : plan.beforePoll registered s (.base .txConsumed) =
    s (.base .txConsumed) + (if cell.transmit then 1#16 else 0#16)
  produced : plan.beforePoll registered s (.base .rxProduced) = s (.base .rxProduced)

theorem deadline_slot (registered : Bool) (plan : AperturePlan) (cell : Cell) (g : Guard)
    (n : Fin 255) (limit : g.limit = .misses n) (s : Values (Register a))
    (start : AtReservation rows pc cell (some g) previous s)
    (service : plan.Delivered registered cell (.misses n) s) (last : plan.misses.length = n.val)
    (miss : g.matches (plan.beforePoll registered s (.base .stage2)) = false) :
    Deadline registered plan cell g s := by
  have reached := prepare registered plan cell g (.misses n) limit s start service
  have ready : ready plan.poll (plan.beforePoll registered s) = 0#1 := by
    rw [ready_from_row _ _ cell g reached.current, miss]
    rfl
  have elapsed : plan.beforePoll registered s (.base .countdown) = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    rw [reached.countdown, last, BitVec.toNat_zero]
    simp [WaitLimit.initialCountdown, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n.val < 256 by omega)]
  exact ⟨reached.active, ⟨service.poll, reached.waiting, ready, bounded_word reached.current limit, elapsed⟩,
    reached.current, reached.pc, reached.remaining, reached.reserved, reached.produced⟩

structure SlotEnd (registered : Bool) (rows : List Row) (pc : Nat) (cell : Cell) (g : Guard)
    (sample : Bool) (s after : Values (Register a)) : Prop where
  remaining : (after (.base .remaining)).toNat = (s (.base .remaining)).toNat - 1
  produced : after (.base .rxProduced) = s (.base .rxProduced) + 1
  reserved : after (.base .txConsumed) = s (.base .txConsumed) + (if cell.transmit then 1#16 else 0#16)
  repeatCell : 1 < (s (.base .remaining)).toNat → AtReservation rows pc cell (some g) (some sample) after
  finished : (s (.base .remaining)).toNat = 1 → AtBoundary registered rows (pc + 1) (some sample) after

theorem run_slot (registered : Bool) (cell : Cell) (g : Guard) (schedule : WaitLimit)
    (limit : g.limit = schedule) (receive : cell.receive = true)
    (plan : SlotPlan) (s : Values (Register a)) (start : AtReservation rows pc cell (some g) previous s)
    (inBounds : pc < rows.length) (positive : 0 < (s (.base .remaining)).toNat)
    (service : plan.Served registered cell g schedule s) :
    SlotEnd registered rows pc cell g (plan.sample registered cell s) s (plan.after registered s) ∧
      ActiveClocks registered s plan.inputs := by
  let atPoll : Values (Register a) := plan.beforePoll registered s
  let raised : Values (Register a) := plan.afterPoll registered s
  let highEnd : Values (Register a) := plan.highEnd registered s
  have prepared := prepare registered plan.toAperturePlan cell g schedule limit s start service.aperture
  have waiting : atPoll (.base .phase) = 7#3 := prepared.waiting
  have stream : IsStream atPoll := by
    change (atPoll (.base .currentWord)).extractLsb' 0 3 = 1#3
    rw [show atPoll (.base .currentWord) = _ from prepared.current]
    exact (encode_fields (.stream cell (some g))).operation
  have receiveBit : (atPoll (.base .currentWord)).extractLsb' 35 1 = 1#1 := by
    rw [show atPoll (.base .currentWord) = _ from prepared.current, (encode_fields (.stream cell (some g))).receive]
    change BitVec.ofBool cell.receive = 1#1
    rw [receive]
    rfl
  have ready : ready plan.poll atPoll = 1#1 := by
    rw [ready_from_row _ _ cell g prepared.current, service.qualified]
    rfl
  have received : ReceiveCut atPoll atPoll raised :=
    receive_edge registered plan.poll atPoll service.aperture.poll prepared.waiting ready stream receiveBit
  have kept := wait_frame registered plan.poll atPoll service.aperture.poll (.inr prepared.waiting) stream
  have highTimer : (raised (.base .countdown)).toNat = plan.high.length := by
    have timer : raised (.base .countdown) = BitVec.ofNat 8 cell.highDuration.val :=
      SegmentPollRefinement.high_countdown registered plan.poll atPoll cell g service.aperture.poll
        prepared.waiting service.qualified prepared.current
    rw [timer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cell.highDuration.isLt, service.highTicks]
  have latched : HasCapture raised (some (plan.sample registered cell s)) :=
    ⟨received.valid, received.sample.trans (SegmentPollRefinement.rxBit_from_row atPoll cell g prepared.current)⟩
  have highWithin : plan.high.length ≤ (raised (.base .countdown)).toNat := Nat.le_of_eq highTimer.symm
  have high : HighPrefix raised highEnd plan.high.length (some (plan.sample registered cell s)) :=
    high_prefix registered raised plan.high service.high received.phase highWithin latched
  have highExpired : highEnd (.base .countdown) = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    change (highEnd (.base .countdown)).toNat = 0
    rw [high.countdown, highTimer, Nat.sub_self]
  have current : highEnd (.base .currentWord) = encode (.stream cell (some g)) :=
    high.current.trans (received.pose.current.trans prepared.current)
  have streamHigh : IsStream highEnd := by
    change (highEnd (.base .currentWord)).extractLsb' 0 3 = 1#3
    rw [current]
    exact (encode_fields (.stream cell (some g))).operation
  have position : (highEnd (.base .pc)).toNat = pc :=
    (congrArg BitVec.toNat (high.pc.trans (kept.pc.trans prepared.pc))).trans start.position
  have remaining : (highEnd (.base .remaining)).toNat = (s (.base .remaining)).toNat :=
    congrArg BitVec.toNat (high.remaining.trans (received.pose.remaining.trans prepared.remaining))
  have delayActive : ActiveClocks registered raised plan.high := by
    apply ActiveClocks.of_prefixes registered raised plan.high 4 (by decide) (by decide) (by decide) service.high
    intro before after i split
    apply (high_prefix registered raised before ?_ received.phase ?_ latched).phase
    · intro input member
      apply service.high input
      rw [split]
      exact List.mem_append_left _ member
    · rw [split, List.length_append] at highWithin
      omega
  have leaveActive : ActiveClocks registered highEnd [@plan.leave] :=
    .cons service.leave (by simp [high.phase]) (by simp [high.phase]) (by simp [high.phase]) .nil
  have pollActive : ActiveClocks registered atPoll (@plan.poll :: (plan.high ++ [@plan.leave])) :=
    .cons (noReset service.aperture.poll) (by simp [waiting])
      (by simp [waiting]) (by simp [waiting]) (delayActive.append leaveActive)
  have active : ActiveClocks registered s plan.inputs := by
    unfold SlotPlan.inputs
    refine prepared.active.append ?_
    rw [AperturePlan.run_prefix]
    exact pollActive
  have installed : Installed rows highEnd := by
    apply delayActive.image
    apply (image_frame registered plan.poll atPoll (noReset service.aperture.poll)
      (.inl (by simp [waiting]))).installed
    change Installed rows (plan.beforePoll registered s)
    rw [← AperturePlan.run_prefix]
    exact prepared.active.image start.installed
  have exit : HighStep highEnd (plan.after registered s) (decide (highEnd (.base .countdown) = 0#8))
      (decide (IsStream highEnd)) (decide (IsStream highEnd ∧ 1 < (highEnd (.base .remaining)).toNat)) :=
    high_step registered plan.leave highEnd service.leave high.phase
  have expiredBit := decide_eq_true highExpired
  have streamBit := decide_eq_true streamHigh
  have canDecrease : (1 : BitVec 16) ≤ highEnd (.base .remaining) := by
    change 1 ≤ (highEnd (.base .remaining)).toNat
    rwa [remaining]
  have left : (plan.after registered s) (.base .remaining) = highEnd (.base .remaining) - 1 := by
    simpa only [expiredBit, streamBit, Bool.true_and, if_true] using exit.remaining
  refine ⟨⟨?_, exit.produced.trans (high.produced.trans (received.produced.trans
    (congrArg (· + 1) prepared.produced))),
    exit.reserved.trans (high.reserved.trans (kept.reserved.trans prepared.reserved)), ?_, ?_⟩, active⟩
  · rw [left, BitVec.toNat_sub_of_le canDecrease, remaining]
    rfl
  · intro repeats
    have again : IsStream highEnd ∧ 1 < (highEnd (.base .remaining)).toNat := ⟨streamHigh, by rwa [remaining]⟩
    have againBit := decide_eq_true again
    have phase : (plan.after registered s) (.base .phase) = 2#3 := by
      simpa only [expiredBit, againBit, if_true] using exit.phase
    have nextPC : (plan.after registered s) (.base .pc) = highEnd (.base .pc) := by
      simpa only [expiredBit, againBit, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false] using exit.pc
    exact ⟨(image_frame registered plan.leave highEnd service.leave (.inl (by simp [high.phase]))).installed installed,
      phase, (congrArg BitVec.toNat nextPC).trans position, exit.current.trans current,
      high_capture_frame registered plan.leave highEnd service.leave high.phase high.latched⟩
  · intro one
    exact high_to_boundary_step registered plan.leave highEnd service.leave high.phase highExpired
      (fun h => by rw [remaining, one] at h; exact (Nat.lt_irrefl 1) h.2)
      installed position inBounds high.latched

def captured (registered : Bool) (cell : Cell) (s : Values (Register a)) (previous : Option Bool) :
    List SlotPlan → Option Bool
  | [] => previous
  | plan :: rest => captured registered cell (plan.after registered s) (some (plan.sample registered cell s)) rest

theorem captured_qualified (registered : Bool) (cell : Cell) (s : Values (Register a))
    (previous : Option Bool) (plans : List SlotPlan) (nonempty : plans ≠ []) :
    (captured registered cell s previous plans).isSome = true := by
  induction plans generalizing s previous with
  | nil => exact (nonempty rfl).elim
  | cons plan rest ih =>
    simp only [captured]
    cases rest with
    | nil => rfl
    | cons _ _ => exact ih _ _ (by simp)

def runSlots (registered : Bool) (s : Values (Register a)) (plans : List SlotPlan) : Values (Register a) :=
  run registered s (plans.flatMap SlotPlan.inputs)

theorem runSlots_cons (registered : Bool) (s : Values (Register a)) (plan : SlotPlan) (rest : List SlotPlan) :
    @runSlots a registered s (plan :: rest) = @runSlots a registered (plan.after registered s) rest := by
  unfold runSlots
  rw [List.flatMap_cons, run_append, plan.run_inputs]

private theorem bump (count : BitVec 16) (amount : Nat) (enabled : Bool) :
    (count + (if enabled then 1#16 else 0#16)) + (if enabled then BitVec.ofNat 16 amount else 0#16) =
      count + (if enabled then BitVec.ofNat 16 (amount + 1) else 0#16) := by
  cases enabled
  · simp
  · simp only [if_true, BitVec.ofNat_add, BitVec.add_assoc]
    rw [BitVec.add_comm 1#16 (BitVec.ofNat 16 amount)]

private structure Traversed (registered : Bool) (rows : List Row) (pc : Nat) (cell : Cell) (g : Guard)
    (last : Option Bool) (slots : Nat) (s after : Values (Register a)) : Prop where
  remaining : (after (.base .remaining)).toNat = (s (.base .remaining)).toNat - slots
  produced : after (.base .rxProduced) = s (.base .rxProduced) + BitVec.ofNat 16 slots
  reserved : after (.base .txConsumed) = s (.base .txConsumed) +
    (if cell.transmit then BitVec.ofNat 16 slots else 0#16)
  repeatCell : slots < (s (.base .remaining)).toNat → AtReservation rows pc cell (some g) last after
  finished : (s (.base .remaining)).toNat = slots → 0 < slots → AtBoundary registered rows (pc + 1) last after

private theorem run_slots (registered : Bool) (cell : Cell) (g : Guard) (schedule : WaitLimit)
    (limit : g.limit = schedule) (receive : cell.receive = true)
    (s : Values (Register a)) (plans : List SlotPlan) (start : AtReservation rows pc cell (some g) previous s)
    (inBounds : pc < rows.length) (within : plans.length ≤ (s (.base .remaining)).toNat)
    (service : Served registered cell g schedule s plans) :
    Traversed registered rows pc cell g (captured registered cell s previous plans) plans.length s
      (runSlots registered s plans) ∧ ActiveClocks registered s (plans.flatMap SlotPlan.inputs) := by
  induction plans generalizing s previous with
  | nil =>
    refine ⟨⟨?_, ?_, ?_, fun _ => start, by simp⟩, .nil⟩
    · rfl
    · change s (.base .rxProduced) = s (.base .rxProduced) + 0#16
      exact (BitVec.add_zero _).symm
    · change s (.base .txConsumed) = s (.base .txConsumed) + (if cell.transmit then 0#16 else 0#16)
      simp
  | cons plan rest ih =>
    rw [runSlots_cons]
    change _ ∧ _ at service
    have positive : 0 < (s (.base .remaining)).toNat := by
      simp only [List.length_cons] at within
      omega
    obtain ⟨step, active⟩ := run_slot registered cell g schedule limit receive plan s start inBounds positive service.1
    have activeWith (tail : ActiveClocks registered (plan.after registered s) (rest.flatMap SlotPlan.inputs)) :
        ActiveClocks registered s ((plan :: rest).flatMap SlotPlan.inputs) := by
      apply active.append
      rw [plan.run_inputs]
      exact tail
    cases rest with
    | nil =>
      refine ⟨⟨step.remaining, step.produced, step.reserved, step.repeatCell, fun one _ => step.finished one⟩,
        activeWith .nil⟩
    | cons next rest =>
      simp only [List.length_cons] at within
      have repeats : 1 < (s (.base .remaining)).toNat := by omega
      have restWithin : (next :: rest).length ≤ ((plan.after registered s) (.base .remaining)).toNat := by
        rw [step.remaining, List.length_cons]
        omega
      obtain ⟨tail, activeTail⟩ := ih (plan.after registered s) (step.repeatCell repeats) restWithin service.2
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, activeWith activeTail⟩
      · rw [tail.remaining, step.remaining, Nat.sub_sub]
        simp [Nat.add_comm]
      · rw [tail.produced, step.produced]
        exact bump (s (.base .rxProduced)) (next :: rest).length true
      · rw [tail.reserved, step.reserved]
        exact bump (s (.base .txConsumed)) (next :: rest).length cell.transmit
      · intro beforeEnd
        apply tail.repeatCell
        rw [step.remaining]
        simp only [List.length_cons] at beforeEnd ⊢
        omega
      · intro last _
        apply tail.finished
        · rw [step.remaining]
          simp only [List.length_cons] at last ⊢
          omega
        · simp

structure Loaded (rows : List Row) (pc : Nat) (cell : Cell) (g : Guard)
    (previous : Option Bool) (s after : Values (Register a)) : Prop where
  ready : AtReservation rows pc cell (some g) previous after
  remaining : after (.base .remaining) = s (.base .remaining)
  produced : after (.base .rxProduced) = s (.base .rxProduced)
  reserved : after (.base .txConsumed) = s (.base .txConsumed)

theorem load_row (registered : Bool) (cell : Cell) (g : Guard) (s : Values (Register a))
    (fetch : Values Core.Input) (start : AtBoundary registered rows pc previous s) (ordinary : NoReset fetch)
    (row : rows[pc]? = some (.cell (.stream cell (some g))))
    (canonical : (Instruction.stream cell (some g)).Canonical) (nonzero : s (.base .remaining) ≠ 0#16) :
    Loaded rows pc cell g previous s ((circuit a registered).step fetch s) := by
  let live : Values (Register a) := (circuit a registered).step fetch s
  have inBounds := (List.getElem?_eq_some_iff.mp row).1
  have selected := selected_row start fetch row
  have atFetch : SegmentControl.AtFetch fetch s :=
    ⟨ordinary.1, ordinary.2, start.phase, by rw [start.position, start.installed.count]; exact inBounds⟩
  have loaded := SegmentStreamStep.load_stream registered fetch s cell (some g) atFetch canonical nonzero selected
  have stream : ((word registered).eval fetch s).extractLsb' 0 3 = 1#3 := by
    rw [selected]
    exact (encode_fields (.stream cell (some g))).operation
  have held := SegmentUnguardedReceive.hold registered fetch s ordinary (.inl ⟨start.phase, stream⟩)
  have installed := (image_frame registered fetch s ordinary (.inl (by simp [start.phase]))).installed start.installed
  have ready : AtReservation rows pc cell (some g) previous live := ⟨installed, loaded.phase,
    (congrArg BitVec.toNat loaded.pc).trans start.position, loaded.current, held.capture start.latched⟩
  exact ⟨ready, loaded.remaining, held.produced,
    SegmentUnguardedReceive.fetch_keeps_tx registered fetch s ordinary start.phase⟩

/-- A complete guarded receive row advances PC only after the last slot and
    produces exactly one capture per timely poll. -/
theorem run_stream_row (registered : Bool) (cell : Cell) (g : Guard) (schedule : WaitLimit)
    (limit : g.limit = schedule) (receive : cell.receive = true)
    (s : Values (Register a)) (fetch : Values Core.Input) (plans : List SlotPlan)
    (start : AtBoundary registered rows pc previous s) (ordinary : NoReset fetch)
    (row : rows[pc]? = some (.cell (.stream cell (some g))))
    (canonical : (Instruction.stream cell (some g)).Canonical)
    (positive : 0 < plans.length) (count : (s (.base .remaining)).toNat = plans.length)
    (service : Served registered cell g schedule ((circuit a registered).step fetch s) plans) :
    SegmentUnguardedReceive.Completed registered rows pc cell
      (captured registered cell ((circuit a registered).step fetch s) previous plans) plans.length s
      (run registered s (@fetch :: plans.flatMap SlotPlan.inputs)) ∧
      ActiveClocks registered s (@fetch :: plans.flatMap SlotPlan.inputs) := by
  let live : Values (Register a) := (circuit a registered).step fetch s
  have nonzero : s (.base .remaining) ≠ 0#16 := by
    intro zero
    simp [zero] at count
    omega
  have loaded := load_row registered cell g s fetch start ordinary row canonical nonzero
  have exactCount : (live (.base .remaining)).toNat = plans.length :=
    (congrArg BitVec.toNat loaded.remaining).trans count
  obtain ⟨finished, active⟩ := run_slots registered cell g schedule limit receive live plans loaded.ready
    (List.getElem?_eq_some_iff.mp row).1 (Nat.le_of_eq exactCount.symm) service
  refine ⟨⟨finished.finished exactCount positive, BitVec.eq_of_toNat_eq ?_, ?_, ?_⟩,
    .cons ordinary (by simp [start.phase]) (by simp [start.phase]) (by simp [start.phase]) active⟩
  · change ((runSlots registered live plans) (.base .remaining)).toNat = 0
    rw [finished.remaining, exactCount, Nat.sub_self]
  · rw [receive]
    exact finished.produced.trans (congrArg (· + BitVec.ofNat 16 plans.length) loaded.produced)
  · exact finished.reserved.trans (congrArg (· + _) loaded.reserved)

theorem successor_stream {cursor following : Cursor}
    (row : rows[cursor.pc]? = some (.cell (.stream cell (some g)))) (armed : cursor.slots = some slots)
    (checked : successors rows budget cursor = some (.next following)) :
    (Instruction.stream cell (some g)).Canonical ∧ following.pc = cursor.pc + 1 ∧
      following.slots = none ∧ following.capture = cell.receive ∧
      following.tx = cursor.tx + (if cell.transmit then slots else 0) ∧
      following.rx = cursor.rx + (if cell.receive then slots else 0) ∧
      0 < slots ∧ following.tx ≤ budget ∧ following.rx < 65536 := by
  simp [successors, row, armed] at checked
  obtain ⟨canonical, ⟨⟨⟨positive, txFits⟩, rxFits⟩, rfl⟩⟩ := checked
  exact ⟨canonical, rfl, rfl, rfl, rfl, rfl, positive, txFits, rxFits⟩

private theorem count_without_wrap (before : BitVec 16) (enabled : Bool) (slots : Nat)
    (bound : before.toNat + (if enabled then slots else 0) < 65536) :
    (before + (if enabled then BitVec.ofNat 16 slots else 0#16)).toNat =
      before.toNat + (if enabled then slots else 0) := by
  cases enabled
  · simp
  · have slotsFit : slots < 65536 := by simp at bound; omega
    simp only [if_true, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt slotsFit]
    exact Nat.mod_eq_of_lt bound

/-- A timely guarded row realizes the checked successor with concrete FIFO
    counts and the actual last qualified sample. -/
theorem service_stream (registered : Bool) (cell : Cell) (g : Guard) (schedule : WaitLimit)
    (limit : g.limit = schedule) (receive : cell.receive = true) (s : Values (Register a))
    (fetch : Values Core.Input) (plans : List SlotPlan) (cut : Cut registered rows cursor previous s)
    (row : rows[cursor.pc]? = some (.cell (.stream cell (some g))))
    (checked : successors rows budget cursor = some (.next following)) (budgetFits : budget < 65536)
    (armed : cursor.slots = some plans.length) (ordinary : NoReset fetch)
    (served : Served registered cell g schedule ((circuit a registered).step fetch s) plans) :
    ServiceSpan registered rows following
      (captured registered cell ((circuit a registered).step fetch s) previous plans) s
      (@fetch :: plans.flatMap SlotPlan.inputs) := by
  obtain ⟨canonical, nextPC, nextSlots, _, nextTX, nextRX, positive, txFits, rxFits⟩ :=
    successor_stream row armed checked
  obtain ⟨completed, active⟩ := run_stream_row registered cell g schedule limit receive s fetch plans cut.boundary
    ordinary row canonical positive (cut.slots _ armed) served
  refine ⟨by simp, active, ⟨nextPC ▸ completed.boundary, ?_, by simp [nextSlots], ?_, ?_⟩⟩
  · intro _
    exact captured_qualified _ _ _ _ _ (by intro empty; simp [empty] at positive)
  · have bound : (s (.base .txConsumed)).toNat + (if cell.transmit then plans.length else 0) < 65536 := by
      rw [cut.tx, ← nextTX]
      exact Nat.lt_of_le_of_lt txFits budgetFits
    rw [completed.consumed, count_without_wrap _ _ _ bound, cut.tx, nextTX]
  · have bound : (s (.base .rxProduced)).toNat + (if cell.receive then plans.length else 0) < 65536 := by
      rw [cut.rx, ← nextRX]
      exact rxFits
    rw [completed.produced, count_without_wrap _ _ _ bound, cut.rx, nextRX]

def deadlinePrefix (fetch : Values Core.Input) (plans : List SlotPlan) (deadline : AperturePlan) :
    List (Values Core.Input) := @fetch :: (plans.flatMap SlotPlan.inputs ++ deadline.prefix)

/-- At a dynamic expiry the in-flight bit is counted as reserved, and the
    RX prefix ends at the previous successful poll. -/
structure ExpiredRow (registered : Bool) (cell : Cell) (g : Guard) (pc doneSlots : Nat)
    (s : Values (Register a)) (inputs : List (Values Core.Input)) (poll : Values Core.Input) : Prop where
  active : ActiveClocks registered s inputs
  deadline : AtDeadline poll (run registered s inputs)
  current : run registered s inputs (.base .currentWord) = encode (.stream cell (some g))
  position : (run registered s inputs (.base .pc)).toNat = pc
  remaining : (run registered s inputs (.base .remaining)).toNat = (s (.base .remaining)).toNat - doneSlots
  reserved : run registered s inputs (.base .txConsumed) = s (.base .txConsumed) +
    (if cell.transmit then BitVec.ofNat 16 (doneSlots + 1) else 0#16)
  produced : run registered s inputs (.base .rxProduced) =
    s (.base .rxProduced) + BitVec.ofNat 16 doneSlots

theorem timeout_stream_row (registered : Bool) (cell : Cell) (g : Guard) (n : Fin 255)
    (limit : g.limit = .misses n) (receive : cell.receive = true)
    (s : Values (Register a)) (fetch : Values Core.Input) (plans : List SlotPlan) (last : AperturePlan)
    (start : AtBoundary registered rows pc previous s) (ordinary : NoReset fetch)
    (row : rows[pc]? = some (.cell (.stream cell (some g))))
    (canonical : (Instruction.stream cell (some g)).Canonical)
    (within : plans.length < (s (.base .remaining)).toNat)
    (service : Served registered cell g (.misses n) ((circuit a registered).step fetch s) plans)
    (finalService : last.Delivered registered cell (.misses n) (runSlots registered ((circuit a registered).step fetch s) plans))
    (elapsed : last.misses.length = n.val)
    (miss : g.matches (last.beforePoll registered (runSlots registered ((circuit a registered).step fetch s) plans)
      (.base .stage2)) = false) :
    ExpiredRow registered cell g pc plans.length s (deadlinePrefix fetch plans last) last.poll := by
  let live : Values (Register a) := (circuit a registered).step fetch s
  let reached : Values (Register a) := runSlots registered live plans
  have nonzero : s (.base .remaining) ≠ 0#16 := by
    intro zero
    simp [zero] at within
  have loaded := load_row registered cell g s fetch start ordinary row canonical nonzero
  have left : plans.length < (live (.base .remaining)).toNat := by
    have remaining : live (.base .remaining) = s (.base .remaining) := loaded.remaining
    rwa [remaining]
  obtain ⟨prior, activePrior⟩ := run_slots registered cell g (.misses n) limit receive live plans loaded.ready
    (List.getElem?_eq_some_iff.mp row).1 (Nat.le_of_lt left) service
  have still := prior.repeatCell left
  have lastSlot := deadline_slot registered last cell g n limit reached still finalService elapsed miss
  have same : @run a registered s (deadlinePrefix fetch plans last) = @AperturePlan.beforePoll a last registered reached := by
    change @run a registered live (plans.flatMap SlotPlan.inputs ++ last.prefix) = _
    rw [run_append]
    exact last.run_prefix registered reached
  have active : ActiveClocks registered s (deadlinePrefix fetch plans last) :=
    .cons ordinary (by simp [start.phase]) (by simp [start.phase]) (by simp [start.phase])
      (activePrior.append lastSlot.active)
  refine ⟨active, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [same]
  · exact lastSlot.deadline
  · exact lastSlot.current
  · exact (congrArg BitVec.toNat lastSlot.pc).trans still.position
  · have leftCount : (reached (.base .remaining)).toNat = (live (.base .remaining)).toNat - plans.length :=
      prior.remaining
    have loadCount : live (.base .remaining) = s (.base .remaining) := loaded.remaining
    rw [lastSlot.remaining, leftCount, loadCount]
  · have tx : reached (.base .txConsumed) = s (.base .txConsumed) +
        (if cell.transmit then BitVec.ofNat 16 plans.length else 0#16) :=
      prior.reserved.trans (congrArg (· + _) loaded.reserved)
    rw [lastSlot.reserved, tx]
    cases cell.transmit <;> simp [BitVec.ofNat_add, BitVec.add_assoc]
  · exact lastSlot.produced.trans (prior.produced.trans (congrArg (· + _) loaded.produced))

/-- The expired row accounts for its completed slots and the in-flight TX
    reservation against the same checked path and bounded counter budget. -/
theorem timeout_span (registered : Bool) (cell : Cell) (g : Guard) (n : Fin 255)
    (_limit : g.limit = .misses n) (receive : cell.receive = true) (s : Values (Register a))
    (cut : Cut registered rows cursor previous s) (row : rows[cursor.pc]? = some (.cell (.stream cell (some g))))
    (checked : successors rows budget cursor = some (.next following)) (budgetFits : budget < 65536)
    (armed : cursor.slots = some slots) (inside : slot < slots)
    (expired : ExpiredRow registered cell g cursor.pc slot s inputs poll) :
    TimeoutSpan registered rows budget cursor slot
      (cursor.tx + if cell.transmit then slot + 1 else 0)
      (cursor.rx + if cell.receive then slot else 0) s inputs poll := by
  obtain ⟨_, _, _, _, nextTX, nextRX, _, txFits, rxFits⟩ := successor_stream row armed checked
  refine ⟨expired.active, ⟨.stream cell (some g), row, .stream armed inside, expired.current⟩,
    ⟨following, checked⟩, expired.position, ?_, ?_, expired.deadline⟩
  · have full : cursor.tx + (if cell.transmit then slots else 0) < 65536 := by
      rw [← nextTX]
      exact Nat.lt_of_le_of_lt txFits budgetFits
    have smaller : (s (.base .txConsumed)).toNat + (if cell.transmit then slot + 1 else 0) < 65536 := by
      rw [cut.tx]
      cases sending : cell.transmit <;>
        simp only [sending, Bool.false_eq_true, if_false, if_true] at full ⊢ <;> omega
    rw [expired.reserved, count_without_wrap _ _ _ smaller, cut.tx]
  · have full : cursor.rx + slots < 65536 := by simpa [nextRX, receive] using rxFits
    have smaller : (s (.base .rxProduced)).toNat + slot < 65536 := by rw [cut.rx]; omega
    have exactCount : (run registered s inputs (.base .rxProduced)).toNat = cursor.rx + slot := by
      rw [expired.produced, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show slot < 65536 by omega), Nat.mod_eq_of_lt smaller, cut.rx]
    simpa [receive] using exactCount

end Pinwheel.Hardware.StreamingReady.SegmentGuardedTransaction
