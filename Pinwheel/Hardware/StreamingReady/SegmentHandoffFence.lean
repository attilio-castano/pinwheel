import Pinwheel.Hardware.StreamingReady.ProtocolOwnership
import Pinwheel.Hardware.StreamingReady.SegmentPathControl

/-! A rejected programming edge leaves the image and transfer intact, while
an admitted release or explicit cancellation empties the old owner. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentHandoffFence

open Pinwheel.Hardware SegmentCore

/-- All registers relevant to the installed image, pads, and custody.
The input synchronizer keeps sampling and the registered reader may refresh. -/
def handoffView (s : Values (Register a)) : Values (Register a)
  | _, .base .stage1 | _, .base .stage2 | _, .fetched => 0
  | _, r => s r

structure EmptyCustody (s : Values (Register a)) : Prop where
  txCount : s (.base .txCount) = 0#4
  txValid : s (.base .txValid) = 0#6
  rxCount : s (.base .rxCount) = 0#4
  rxUsed : s (.base .rxUsed) = 0#6
  txAccepted : s (.base .txAccepted) = 0#16
  txConsumed : s (.base .txConsumed) = 0#16
  rxProduced : s (.base .rxProduced) = 0#16
  rxPopped : s (.base .rxPopped) = 0#16
  txClosed : s .txClosed = 0#1
  captureValid : s .captureValid = 0#1

structure FreeCut (registered : Bool) (s : Values (Register a)) : Prop where
  phase : s (.base .phase) = 0#3
  empty : EmptyCustody s
  coherent : registered = true → SegmentStore.Coherent s

private theorem reader_coherent (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    registered = true → SegmentStore.Coherent ((circuit a registered).step i s) := by
  intro h
  subst registered
  exact SegmentStore.coherent_after_edge i s

private theorem step_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) :
    (circuit a registered).step i s (.base r) =
      (nextBase r).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

private theorem inv_one_inv (x : BitVec 1) : ~~~(1#1 &&& ~~~x) = x := by decide +revert +kernel

set_option linter.unusedSimpArgs false in
/-- A stale generation cannot acquire a free owner even if the image is valid.
The rejected START preserves the entire installed image and runtime state. -/
theorem stale_start (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (init : i .initialize = 0#1) (start : i .command = 3#4)
    (free : s (.base .phase) = 0#3)
    (stale : i .expectedGeneration ≠ s (.base .generation)) :
    (circuit a registered).observe i s .rejected = 1#1 ∧
      @handoffView a ((circuit a registered).step i s) = @handoffView a s := by
  constructor
  · change (bindWord (word registered) (output .rejected)).eval i s = 1#1
    rw [bindWord_eval]
    simp [output, Core.output, Core.rejected, SegmentCore.discard, fetching, denyTX,
      SegmentCore.either, SegmentCore.both, Expr.eval_bind, Expr.eval, lift, withFetch,
      Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.cold, Core.warm, Core.resetting,
      Core.cmd, Core.either, Core.both, Core.releasing, Core.starting, Core.free, Core.hostOwner,
      Core.owned, Core.busy, Core.identity, Core.retained, Core.writing, Core.committing,
      Core.pushing, Core.popping, init, start, free, stale]
  · funext w r
    cases r with
    | base r =>
      cases r <;>
        simp [handoffView, step_base, nextBase, originalNext, Expr.eval_bind,
          SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, denyTX,
          SegmentCore.either, SegmentCore.both, Expr.eval, usesEntryWord, runtimeInput,
          decodedRegister, lift, withFetch, Core.next, Core.nextRaw, Core.isPhase, Core.fetching,
          Core.clearedRuntime, Core.cold, Core.warm, Core.resetting, Core.cmd, Core.either, Core.both,
          Core.releasing, Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity,
          Core.retained, Core.writing, Core.committing, Core.pushing, Core.popping, Core.takingTX,
          Core.reserving, Core.lowEnd, Core.highEnd, Core.capturingRX, Core.capture,
          Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault,
          Core.waitDecrement, Core.loadingTX, Core.timeoutFlush, Core.emittingRX, Core.normalEmit,
          Core.queueCount, Core.nextPins, Core.enteringCell, Core.advancing, init, start, free, stale]
    | lastCapture | captureValid | txClosed =>
      simp [handoffView, Circuit.step, circuit, bindWord_eval, next, SegmentCore.control, setCount,
        branch, SegmentCore.discard, fetching, SegmentCore.either, SegmentCore.both,
        Expr.eval, Expr.eval_bind, lift, withFetch,
        Core.clearedRuntime, Core.cold, Core.warm, Core.resetting, Core.cmd, Core.either, Core.both,
        Core.releasing, Core.starting, Core.free, Core.isPhase, Core.fetching, Core.capturingRX,
        Core.capture, Core.lowEnd, Core.waitSuccess, init, start, free, stale, inv_one_inv]
    | fetched => rfl
  done

private theorem step_extra (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Register a w) (nonLatch : ∀ eq : w = 64, eq ▸ r ≠ .fetched) :
    (circuit a registered).step i s r =
      (next r).eval i (withFetch s ((word registered).eval i s)) := by
  cases r with
  | fetched => exact (nonLatch rfl rfl).elim
  | base | txClosed | lastCapture | captureValid => exact bindWord_eval _ _ _ _

set_option linter.unusedSimpArgs false in
/-- On an ordinary accepted RELEASE, the settled owner leaves an empty free
cut with unchanged program, generation and transfer. -/
theorem release_to_free (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (release : SegmentCustody.AtRelease i s) :
    let after : Values (Register a) := (circuit a registered).step i s
    FreeCut registered after ∧ SegmentPathControl.ImageFrame s after ∧
      after (.base .transfer) = s (.base .transfer) ∧
      after (.base .levels) = s (.base .idleLevels) ∧ after (.base .enabled) = s (.base .idleEnabled) := by
  obtain ⟨free, closed, levels, enabled, _, transfer⟩ := SegmentCustody.release_after_drain registered i s release
  have image := SegmentPathControl.image_frame registered i s
    ⟨release.initialized, by simp [release.command]⟩
    (Or.inl (by simp [release.completed]))
  refine ⟨⟨free, ?_, reader_coherent registered i s⟩, image, transfer, levels, enabled⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, closed, ?_⟩ <;>
    simp [step_base, step_extra, nextBase, next, originalNext, Expr.eval_bind, usesEntryWord,
      runtimeInput, decodedRegister, lift, withFetch, Expr.eval, SegmentCore.either, SegmentCore.both,
      Core.next, Core.nextRaw, Core.clearedRuntime, Core.cold, Core.warm, Core.cmd, Core.resetting,
      Core.either, Core.both, Core.releasing, Core.hostOwner, Core.owned, Core.busy, Core.retained,
      Core.identity, Core.isPhase, Core.drained, release.initialized, release.command,
      release.generation, release.transfer, release.completed,
      release.drainedTX.1, release.drainedTX.2, release.drainedRX.1, release.drainedRX.2]
  done

set_option linter.unusedSimpArgs false in
/-- Explicit cancellation clears all pending and recorded custody, including
the branch latch. The free cut is uninstalled and preserves owner counters. -/
theorem warm_cancel (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (init : i .initialize = 0#1) (cancel : i .command = 15#4) :
    let after : Values (Register a) := (circuit a registered).step i s
    FreeCut registered after ∧ after (.base .valid) = 0#1 ∧
      after (.base .generation) = s (.base .generation) ∧ after (.base .transfer) = s (.base .transfer) := by
  obtain ⟨free, closed, invalid, txCount, txValid, rxCount, rxUsed, generation, transfer⟩ :=
    ProtocolOwnership.cancel_step registered i s init cancel
  refine ⟨⟨free, ?_, reader_coherent registered i s⟩, invalid, generation, transfer⟩
  refine ⟨txCount, txValid, rxCount, rxUsed, ?_, ?_, ?_, ?_, closed, ?_⟩ <;>
    simp [step_base, step_extra, nextBase, next, originalNext, Expr.eval_bind, usesEntryWord,
      runtimeInput, decodedRegister, lift, withFetch, Expr.eval, SegmentCore.either, SegmentCore.both,
      Core.next, Core.nextRaw, Core.clearedRuntime, Core.cold, Core.warm, Core.cmd, Core.resetting,
      Core.either, Core.both, init, cancel]
  done

set_option linter.unusedSimpArgs false in
/-- A programming or START command, delivered without queue service, cannot
change the installed image, pins or custody of a retained owner. This
includes an owner kept live by a sampled guard timeout. -/
theorem retained_fences (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (init : i .initialize = 0#1) (noPush : i .txPush = 0#1) (noPop : i .rxPop = 0#1)
    (retained : s (.base .phase) = 5#3 ∨ s (.base .phase) = 6#3)
    (attempt : i .command = 1#4 ∨ i .command = 2#4 ∨ i .command = 3#4) :
    (circuit a registered).observe i s .rejected = 1#1 ∧
      @handoffView a ((circuit a registered).step i s) = @handoffView a s := by
  have ⟨nonzero, notRelease, ordinary⟩ : i .command ≠ 0#4 ∧ i .command ≠ 4#4 ∧
      i .command ≠ 15#4 := by
    rcases attempt with op | op | op <;> simp [op]
  rcases retained with phase | phase
  all_goals constructor
  all_goals first
    | change (bindWord (word registered) (output .rejected)).eval i s = 1#1
      rw [bindWord_eval]
      simp [output, Core.output, Core.rejected, SegmentCore.discard, fetching, denyTX,
        SegmentCore.either, SegmentCore.both, Expr.eval_bind, Expr.eval, lift, withFetch,
        Core.isPhase, Core.fetching, Core.cold, Core.warm, Core.resetting, Core.cmd, Core.either,
        Core.both, Core.releasing, Core.starting, Core.free, Core.writing, Core.committing,
        init, nonzero, notRelease, ordinary, phase, noPush, noPop]
    | funext w r
      cases r with
      | base r =>
        cases r <;>
          simp [handoffView, step_base, nextBase, originalNext, Expr.eval_bind,
            SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, denyTX,
            SegmentCore.either, SegmentCore.both, Expr.eval, usesEntryWord, runtimeInput,
            decodedRegister, lift, withFetch, Core.next, Core.nextRaw, Core.isPhase, Core.fetching,
            Core.clearedRuntime, Core.cold, Core.warm, Core.resetting, Core.cmd, Core.either, Core.both,
            Core.releasing, Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity,
            Core.retained, Core.writing, Core.committing, Core.pushing, Core.popping, Core.takingTX,
            Core.reserving, Core.lowEnd, Core.highEnd, Core.capturingRX, Core.capture,
            Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault,
            Core.waitDecrement, Core.loadingTX, Core.timeoutFlush, Core.emittingRX, Core.normalEmit,
            Core.queueCount, Core.nextPins, Core.enteringCell, Core.advancing, init, notRelease,
            ordinary, phase, noPush, noPop]
      | lastCapture | captureValid | txClosed =>
        simp [handoffView, step_extra, next, SegmentCore.control, setCount,
          branch, SegmentCore.discard, fetching, SegmentCore.either, SegmentCore.both,
          Expr.eval, Expr.eval_bind, lift, withFetch,
          Core.clearedRuntime, Core.cold, Core.warm, Core.resetting, Core.cmd, Core.either, Core.both,
          Core.releasing, Core.starting, Core.free, Core.isPhase, Core.fetching, Core.capturingRX,
          Core.capture, Core.lowEnd, Core.waitSuccess, init, notRelease, ordinary, phase, inv_one_inv]
      | fetched => rfl
  done

set_option linter.unusedSimpArgs false in
/-- RELEASE against a timed-out owner with unspent TX keeps the same
installed image and terminal transfer ledger. -/
theorem timeout_release_fenced (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (init : i .initialize = 0#1) (command : i .command = 4#4) (fault : s (.base .phase) = 6#3)
    (noPush : i .txPush = 0#1)
    (owned : s (.base .txCount) ≠ 0#4 ∨ s (.base .txValid) ≠ 0#6) :
    let after : Values (Register a) := (circuit a registered).step i s
    (circuit a registered).observe i s .rejected = 1#1 ∧
      ProtocolOwnership.TerminalCut.of after = ProtocolOwnership.TerminalCut.of s ∧
      SegmentPathControl.ImageFrame s after := by
  have rejected := ProtocolOwnership.timeout_rejects_release registered i s init command fault owned
  have image := SegmentPathControl.image_frame registered i s
    ⟨init, by simp [command]⟩ (Or.inl (by simp [fault]))
  refine ⟨rejected.1, ?_, image⟩
  rcases owned with pending | pending <;>
    simp [ProtocolOwnership.TerminalCut.of, rejected.2, step_base, step_extra, nextBase, next,
      originalNext, Expr.eval_bind, SegmentCore.discard, fetching, SegmentCore.either, SegmentCore.both,
      Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
      Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
      Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
      Core.drained, Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity,
      Core.retained, Core.committing, Core.pushing, Core.takingTX, Core.reserving, Core.lowEnd,
      Core.capturingRX, Core.capture, Core.waitSuccess, init, command, fault, noPush, pending, inv_one_inv]
  done

end Pinwheel.Hardware.StreamingReady.SegmentHandoffFence
