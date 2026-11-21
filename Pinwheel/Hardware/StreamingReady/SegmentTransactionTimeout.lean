import Pinwheel.Hardware.StreamingReady.SegmentTransaction

/-! A dynamic guard expiry interrupts a checked path. The final poll keeps the
captured prefix and the previously accepted TX under the admitted START owner. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTransactionTimeout

open Pinwheel.Hardware SegmentCore SegmentPathControl SegmentTransaction
open Pinwheel.Program.StreamingReady (Instruction)
open Pinwheel.Program.StreamingReadySegments
open SegmentTiming (run)

/-- Standalone waits consume no data. A failed STREAM slot has already reserved
    its TX bit, while only earlier slots have contributed RX bits. -/
inductive GuardedSlot (cursor : Cursor) : Instruction → Nat → Nat → Nat → Prop where
  | wait : GuardedSlot cursor (.driveWait pins g) 0 cursor.tx cursor.rx
  | stream (armed : cursor.slots = some slots) (inside : slot < slots) :
      GuardedSlot cursor (.stream cell (some g)) slot
        (cursor.tx + if cell.transmit then slot + 1 else 0)
        (cursor.rx + if cell.receive then slot else 0)

structure TimeoutSpan (registered : Bool) (rows : List Row) (budget : Nat) (cursor : Cursor)
    (slot tx rx : Nat) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (last : Values Core.Input) : Prop where
  active : ActiveClocks registered s inputs
  row : ∃ instruction, rows[cursor.pc]? = some (.cell instruction) ∧
    GuardedSlot cursor instruction slot tx rx ∧
    run registered s inputs (.base .currentWord) = Pinwheel.Program.StreamingReady.encode instruction
  legal : ∃ following, successors rows budget cursor = some (.next following)
  pc : (run registered s inputs (.base .pc)).toNat = cursor.pc
  txCount : (run registered s inputs (.base .txConsumed)).toNat = tx
  rxCount : (run registered s inputs (.base .rxProduced)).toNat = rx
  deadline : ProtocolOwnership.AtDeadline last (run registered s inputs)

private def SameIdle (s after : Values (Register a)) : Prop :=
  after (.base .idleLevels) = s (.base .idleLevels) ∧
    after (.base .idleEnabled) = s (.base .idleEnabled)

set_option linter.unusedSimpArgs false in
private theorem idle_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (noCommit : s (.base .phase) ≠ 0#3 ∨ i .command ≠ 2#4) :
    SameIdle s ((circuit a registered).step i s) := by
  rcases noCommit with active | cmd <;>
    refine ⟨?_, ?_⟩ <;>
    change (bindWord (word registered) (next _)).eval i s = _ <;>
    rw [bindWord_eval] <;>
    simp [next, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
      withFetch, Expr.eval, Core.next, Core.nextRaw, Core.committing, Core.free, Core.cold,
      Core.cmd, Core.both, Core.isPhase, ordinary.1, *]

private theorem idle_run (span : @ActiveClocks registered a s inputs) :
    SameIdle s (run registered s inputs) := by
  induction span with
  | nil => exact ⟨rfl, rfl⟩
  | cons ordinary notFree _ _ _ ih =>
    have idle := idle_step registered _ _ ordinary (.inl notFree)
    exact ⟨ih.1.trans idle.1, ih.2.trans idle.2⟩

private theorem start_idle (registered : Bool) (start : Values Core.Input) (s : Values (Register a))
    (admitted : Core.starting.eval start (project s) = 1#1) :
    SameIdle s ((circuit a registered).step start s) := by
  have command : start .command = 3#4 := by
    by_cases known : start .command = 3#4
    · exact known
    · simp [Core.starting, Core.cmd, Core.both, Expr.eval, known] at admitted
  have init : start .initialize = 0#1 := by
    rcases BitVec.eq_zero_or_eq_one (start .initialize) with zero | one
    · exact zero
    · simp [Core.starting, Core.free, Core.cmd, Core.both, Core.either, Core.resetting,
        Core.cold, Core.warm, Expr.eval, one, command] at admitted
  exact idle_step registered start s ⟨init, by simp [command]⟩ (.inr (by simp [command]))

/-- Admitted START and the subsequent active clocks preserve the installed idle pose. -/
theorem idle_from_start (registered : Bool) (s : Values (Register a)) (start : Values Core.Input)
    (admitted : Core.starting.eval start (project s) = 1#1)
    (clocks : ActiveClocks registered ((circuit a registered).step start s) inputs) :
    let aperture : Values (Register a) := run registered ((circuit a registered).step start s) inputs
    aperture (.base .idleLevels) = s (.base .idleLevels) ∧
      aperture (.base .idleEnabled) = s (.base .idleEnabled) := by
  have continued := idle_run clocks
  have started := start_idle registered start s admitted
  exact ⟨continued.1.trans started.1, continued.2.trans started.2⟩

/-- The final poll takes place at the certified guard site. The failed poll
    preserves the counters of the aperture and returns to the idle pad pose. -/
theorem TimeoutSpan.expires
    (span : @TimeoutSpan a registered rows budget cursor slot tx rx s inputs last) :
    let aperture : Values (Register a) := run registered s inputs
    let after : Values (Register a) := run registered s (inputs ++ [@last])
    SegmentTiming.TimeoutCut aperture after ∧ OwnerFrame s after ∧
      after (.base .levels) = s (.base .idleLevels) ∧ after (.base .enabled) = s (.base .idleEnabled) ∧
      (after (.base .txConsumed)).toNat = tx ∧ (after (.base .rxProduced)).toNat = rx := by
  have hit := SegmentTiming.timeout_edge registered last _ span.deadline
  have idle := idle_run span.active
  let poll : Values (Register a) := run registered s inputs
  have live : poll (.base .phase) = 7#3 := span.deadline.waiting
  have activeLast : ActiveClocks registered poll [@last] :=
    .cons ⟨span.deadline.ordinary.1, by simp [span.deadline.ordinary.2.1]⟩
      (by simp [live]) (by simp [live]) (by simp [live]) .nil
  have used := congrArg ProtocolOwnership.TerminalCut.reserved hit.retained
  have captured := congrArg ProtocolOwnership.TerminalCut.captured hit.retained
  have owner := (span.active.append activeLast).owner
  rw [SegmentTiming.run_append] at owner ⊢
  exact ⟨hit, owner,
    hit.levels.trans idle.1, hit.enabled.trans idle.2,
    (congrArg BitVec.toNat used).trans span.txCount,
    (congrArg BitVec.toNat captured).trans span.rxCount⟩

/-- The same guard expiry certificate accounts for the exact acknowledged RX
    interval, the unsent TX suffix and the subsequent warm cancellation. -/
theorem TimeoutSpan.after_drain
    (span : @TimeoutSpan a registered rows budget cursor slot tx rx s inputs last)
    (accepted : tx ≤ (run registered s inputs (.base .txAccepted)).toNat)
    (drain : List (Values Core.Input)) (ordinary : ∀ i ∈ drain, ProtocolOwnership.DrainInput i)
    (front : Values Streaming.Frontend.Register) :
    let aperture : Values (Register a) := run registered s inputs
    let fault : Values (Register a) := (circuit a registered).step last aperture
    let drained : Values (Register a) := run registered fault drain
    let owned := (aperture (.base .txAccepted)).toNat - tx
    ProtocolOwnership.AcknowledgedReceive drained front →
      (ProtocolOwnership.segmentedReport .timeout .retained 0 owned drained drained front).Valid ∧
      drained (.base .phase) = 6#3 ∧ (front .ackOffset).toNat = rx ∧
      ∀ cancel : Values Core.Input, cancel .initialize = 0#1 → cancel .command = 15#4 →
        let after : Values (Register a) := (circuit a registered).step cancel drained
        (ProtocolOwnership.segmentedReport .timeout .cancelled 0 owned drained after front).Valid ∧
          after (.base .phase) = 0#3 ∧ after (.base .valid) = 0#1 := by
  intro aperture fault drained owned received
  have consumed : (aperture (.base .txConsumed)).toNat = tx := span.txCount
  have order : (aperture (.base .txConsumed)).toNat ≤ (aperture (.base .txAccepted)).toNat := by
    rw [consumed]
    exact accepted
  obtain ⟨retained, phase, receivedCount, _, _, cancelled⟩ :=
    ProtocolOwnership.timeout_after_drain registered last aperture span.deadline order drain ordinary front received
  have offset := ((received.exact.symm.trans (congrArg BitVec.toNat receivedCount))).trans span.rxCount
  exact ⟨by simpa only [owned, drained, fault, SegmentTiming.run, consumed] using retained, phase, offset,
    fun cancel init command => by
      simpa only [owned, drained, fault, SegmentTiming.run, consumed] using cancelled cancel init command⟩

/-- An admitted START followed by a checked prefix and an expired poll
    retains exactly the expected prefix and accepted owner in FAULT. -/
theorem from_start (registered : Bool) (s : Values (Register a)) (start : Values Core.Input)
    (installed : Installed rows s) (admitted : Core.starting.eval start (project s) = 1#1)
    (walk : Prefix registered rows budget {} none ((circuit a registered).step start s) before cursor capture)
    (span : Cut registered rows cursor capture (run registered ((circuit a registered).step start s) before) →
      TimeoutSpan registered rows budget cursor slot tx rx
        (run registered ((circuit a registered).step start s) before) polling last) :
    let after : Values (Register a) := run registered s (@start :: (before ++ polling ++ [@last]))
    after (.base .phase) = 6#3 ∧ (after (.base .txConsumed)).toNat = tx ∧ (after (.base .rxProduced)).toNat = rx ∧
      after (.base .levels) = s (.base .idleLevels) ∧ after (.base .enabled) = s (.base .idleEnabled) ∧
      after (.base .generation) = s (.base .generation) ∧
      after (.base .transfer) = s (.base .transfer) + 1 ∧ after (.base .total) = start .startCount := by
  obtain ⟨boundary, generation, transfer, total, _, _, consumed, produced⟩ :=
    start_at_boundary registered start s installed admitted
  have first : Cut registered rows {} none ((circuit a registered).step start s) :=
    ⟨boundary, by simp, by simp, by simp [consumed], by simp [produced]⟩
  obtain ⟨cut, active⟩ := walk.refines first
  obtain ⟨timeout, frame, levels, enabled, tx, rx⟩ := (span cut).expires
  have owner := active.owner
  have idle := idle_run active
  have startedIdle := start_idle registered start s admitted
  change _ ∧ _
  simp only [SegmentTiming.run, List.foldl_cons, List.foldl_append] at *
  exact ⟨congrArg ProtocolOwnership.TerminalCut.phase timeout.retained, tx, rx,
    levels.trans (idle.1.trans startedIdle.1), enabled.trans (idle.2.trans startedIdle.2),
    frame.generation.trans (owner.generation.trans generation), frame.transfer.trans (owner.transfer.trans transfer),
    frame.total.trans (owner.total.trans total)⟩

end Pinwheel.Hardware.StreamingReady.SegmentTransactionTimeout
