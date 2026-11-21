import Pinwheel.Hardware.StreamingReady.SegmentCore

/-! At an early halt the recorded consumption count distinguishes physically
    transmitted bits from accepted bits canceled by the program. Capture and
    ownership remain available for the usual drain and RELEASE. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentCustody
open Pinwheel.Hardware SegmentCore

structure AtDiscard (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) : Prop where
  initialized : i .initialize = 0
  ordinary : i .command ≠ 15#4
  fetching : s (.base .phase) = 1
  inBounds : (s (.base .pc)).toNat < (s (.base .count)).toNat
  instruction : (word registered).eval i s = 7

structure Discarded (before after : Values (Register a)) : Prop where
  completed : after (.base .phase) = 5
  closed : after .txClosed = 1
  txEmpty : after (.base .txCount) = 0 ∧ after (.base .txValid) = 0
  accepted : after (.base .txAccepted) = before (.base .txAccepted)
  sent : after (.base .txConsumed) = before (.base .txConsumed)
  captured : after (.base .rxProduced) = before (.base .rxProduced)
  rxPartial : after (.base .rxPartial) = before (.base .rxPartial) ∧
    after (.base .rxUsed) = before (.base .rxUsed)
  rxWords : ∀ k, after (.base (.rxWord k)) = before (.base (.rxWord k)) ∧
    after (.base (.rxBits k)) = before (.base (.rxBits k))
  owner : after (.base .generation) = before (.base .generation) ∧
    after (.base .transfer) = before (.base .transfer)

/-- Sent bits and the discarded suffix account for every accepted bit. -/
theorem Discarded.accounted {before after : Values (Register a)} (h : Discarded before after)
    (ordered : (before (.base .txConsumed)).toNat ≤ (before (.base .txAccepted)).toNat) :
    (after (.base .txAccepted)).toNat = (after (.base .txConsumed)).toNat +
      ((before (.base .txAccepted)).toNat - (before (.base .txConsumed)).toNat) := by
  rw [h.accepted, h.sent]
  omega
  done

private theorem notZero : ~~~(0#1) = 1 := rfl
private theorem notOne : ~~~(1#1) = 0 := rfl
private theorem oneAnd (value : BitVec 1) : 1#1 &&& value = value := by decide +revert +kernel
private theorem andOne (value : BitVec 1) : value &&& 1#1 = value := by decide +revert +kernel
private theorem orTrue (value : BitVec 1) : ~~~(~~~value &&& ~~~(1#1)) = 1 := by decide +revert +kernel
private theorem trueOr (value : BitVec 1) : ~~~(~~~(1#1) &&& ~~~value) = 1 := by decide +revert +kernel

private theorem lift_eval (expr : Core.E a w) (i : Values Core.Input) (s : Values (Register a)) :
    (lift expr).eval i s = expr.eval i (project s) := Expr.eval_bind .input _ expr i s

private theorem selected_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) :
    (circuit a registered).step i s (.base r) = (nextBase r).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

private theorem selected_close (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .txClosed = (next .txClosed).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

private theorem discard_enabled (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (h : AtDiscard registered i s) : SegmentCore.discard.eval i (withFetch s ((word registered).eval i s)) = 1#1 := by
  simp [SegmentCore.discard, fetching, both, lift_eval, Core.fetching, Core.entryBounds, Core.resetting,
    Core.either, Core.both, Core.cold, Core.warm, Core.cmd, Core.isPhase, Expr.eval, project, withFetch,
    h.initialized, h.ordinary, h.fetching, h.inBounds, h.instruction]
  done

set_option linter.unusedSimpArgs false in
/-- The hardware closes the transmit side and preserves counters, captured
    data and the owner across the instruction, regardless of a pending offer. -/
theorem discard_preserves_custody (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (h : AtDiscard registered i s) : Discarded s ((circuit a registered).step i s) := by
  have discardNow := discard_enabled registered i s h
  have deny : denyTX.eval i (withFetch s ((word registered).eval i s)) = 1#1 := by
    simp only [denyTX, SegmentCore.either, Expr.eval, discardNow, orTrue]
    rfl
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  all_goals try simp only [selected_step, selected_close, nextBase, next, Expr.eval, discardNow, if_pos]
  all_goals try simp [originalNext, Expr.eval_bind, usesEntryWord, runtimeInput, Expr.eval,
    Core.next, Core.nextRaw, lift_eval, withFetch, project, Core.clearedRuntime, Core.resetting,
    Core.cold, Core.warm, Core.cmd, Core.either, Core.both, Core.starting, Core.releasing,
    Core.free, Core.retained, Core.isPhase, Core.committing, Core.pushing, Core.takingTX, Core.reserving,
    Core.capturingRX, Core.capture, Core.lowEnd, Core.waitSuccess, Core.waitFault, Core.normalEmit,
    Core.timeoutFlush, Core.emittingRX, SegmentCore.either, both, deny, discardNow,
    h.initialized, h.ordinary, h.fetching, andOne, oneAnd, notZero, notOne, trueOr]

private theorem rejects_denied (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (notInitializing : i .initialize = 0#1) (ordinary : i .command ≠ 15#4) (pushing : i .txPush = 1#1)
    (deny : denyTX.eval i (withFetch s ((word registered).eval i s)) = 1#1) :
    (circuit a registered).observe i s .rejected = 1#1 := by
  change (bindWord (word registered) (output .rejected)).eval i s = 1#1
  rw [bindWord_eval]
  simp [output, SegmentCore.either, SegmentCore.both, Expr.eval, lift_eval, Core.resetting, Core.either,
    Core.warm, Core.cold, Core.both, Core.cmd, notInitializing, ordinary, pushing, deny]
  done

theorem discard_rejects_tx (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (h : AtDiscard registered i s) (pushing : i .txPush = 1#1) :
    (circuit a registered).observe i s .rejected = 1#1 := by
  apply rejects_denied registered i s h.initialized h.ordinary pushing
  simp only [denyTX, SegmentCore.either, Expr.eval, discard_enabled registered i s h, orTrue]
  rfl
  done

theorem closed_rejects_tx (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (notInitializing : i .initialize = 0#1) (ordinary : i .command ≠ 15#4) (pushing : i .txPush = 1#1)
    (closed : s .txClosed = 1#1) : (circuit a registered).observe i s .rejected = 1#1 := by
  apply rejects_denied registered i s notInitializing ordinary pushing
  simp only [denyTX, SegmentCore.either, Expr.eval, withFetch, closed, trueOr]
  rfl
  done

/-- The control words and TX closure leave the usual owner-checked RX
    drain running, including an acknowledgment on the discard edge. -/
theorem rx_queue_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    let actual : Values (Register a) := (circuit a registered).step i s
    let original : Values (Core.Register a) := (Core.circuit a).step i (project s)
    actual (.base .rxHead) = original .rxHead ∧ actual (.base .rxTail) = original .rxTail ∧
      actual (.base .rxCount) = original .rxCount ∧ actual (.base .rxPopped) = original .rxPopped := by
  dsimp only
  rw [selected_step, selected_step, selected_step, selected_step]
  simp [nextBase, originalNext, Expr.eval_bind, usesEntryWord, Circuit.step,
    Core.circuit, runtimeInput, withFetch, project, Expr.eval,
    Core.next, Core.nextRaw, Core.resetting, Core.either, Core.both, Core.cold, Core.warm,
    Core.cmd, Core.releasing, Core.starting, Core.retained, Core.free, Core.isPhase, Core.drained,
    Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.space, Core.popping, Core.queueCount,
    Core.emittingRX, Core.normalEmit, Core.timeoutFlush, Core.capturingRX, Core.capture,
    Core.lowEnd, Core.waitSuccess, Core.waitFault, Core.waitReady, Core.highGuard,
    Core.guardMask, Core.guardExpected, Core.guardBudget, Core.lastCell, Core.receive,
    Core.stream, Core.field, Core.inc, Core.add, Core.rxHeadBits, Execution.readTree_correct]
  exact ⟨rfl, rfl, rfl, rfl⟩
  done

structure AtRelease (i : Values Core.Input) (s : Values (Register a)) : Prop where
  initialized : i .initialize = 0#1
  command : i .command = 4#4
  generation : i .expectedGeneration = s (.base .generation)
  transfer : i .expectedTransfer = s (.base .transfer)
  completed : s (.base .phase) = 5#3
  drainedTX : s (.base .txCount) = 0#4 ∧ s (.base .txValid) = 0#6
  drainedRX : s (.base .rxCount) = 0#4 ∧ s (.base .rxUsed) = 0#6

set_option linter.unusedSimpArgs false in
/-- A legitimate owner can release once RX is drained. RELEASE returns the
    pins to the installed idle drive and keeps both owner counters. -/
theorem release_after_drain (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (h : AtRelease i s) :
    let after : Values (Register a) := (circuit a registered).step i s
    after (.base .phase) = 0#3 ∧ after .txClosed = 0#1 ∧
      after (.base .levels) = s (.base .idleLevels) ∧
      after (.base .enabled) = s (.base .idleEnabled) ∧
      after (.base .generation) = s (.base .generation) ∧
      after (.base .transfer) = s (.base .transfer) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [selected_step, selected_close, nextBase, next, originalNext, Expr.eval_bind,
    SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, SegmentCore.either, SegmentCore.both,
    Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift_eval, project, withFetch,
    Core.next, Core.nextRaw, Core.nextPins, Core.isPhase, Core.fetching, Core.clearedRuntime,
    Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
    Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
    Core.drained, Core.committing, h.initialized, h.command, h.generation, h.transfer, h.completed,
    h.drainedTX.1, h.drainedTX.2, h.drainedRX.1, h.drainedRX.2, andOne, oneAnd, notZero, notOne]
  done

end Pinwheel.Hardware.StreamingReady.SegmentCustody
