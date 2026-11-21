import Pinwheel.Hardware.StreamingReady.SegmentTiming

/-! Standalone drive-and-wait rows on the segmented hardware. They poll the
same sampler as guarded stream cells and return to FETCH without consuming a
cell or replacing its last qualified capture. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentWaitRefinement

open Pinwheel.Hardware SegmentCore SegmentTiming
open ProtocolOwnership (DrainInput)
open Pinwheel.Program.StreamingReady (Guard Pins Instruction WaitLimit encode encode_fields driveWait_unused)

private def selected (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    Values (Register a) := withFetch s ((word registered).eval i s)

private theorem step_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) :
    (circuit a registered).step i s (.base r) = (nextBase r).eval i (selected registered i s) :=
  bindWord_eval _ _ _ _

private theorem step_capture (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .lastCapture = (next .lastCapture).eval i (selected registered i s) :=
  bindWord_eval _ _ _ _

private theorem step_valid (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .captureValid = (next .captureValid).eval i (selected registered i s) :=
  bindWord_eval _ _ _ _

private theorem inv_one_inv (x : BitVec 1) : ~~~(1#1 &&& ~~~x) = x := by decide +revert +kernel

structure WaitSuccess (s after : Values (Register a)) : Prop where
  phase : after (.base .phase) = 1#3
  pc : after (.base .pc) = s (.base .pc) + 1#7
  countdown : after (.base .countdown) = 0#8
  pose : WaitPose s after
  captured : after (.base .rxProduced) = s (.base .rxProduced)
  latched : after .lastCapture = s .lastCapture
  valid : after .captureValid = s .captureValid

/-- The encoded guard tests the pre-edge second sampler, even if the raw
sample on this clock changes. -/
theorem ready_from_wait (i : Values Core.Input) (s : Values (Register a)) (pins : Pins) (g : Guard)
    (loaded : s (.base .currentWord) = encode (.driveWait pins g)) :
    ready i s = BitVec.ofBool (g.matches (s (.base .stage2))) := by
  have fields := encode_fields (.driveWait pins g)
  have mask : (s (.base .currentWord)).extractLsb' 50 2 = g.mask := loaded ▸ fields.guardMask
  have expected : (s (.base .currentWord)).extractLsb' 52 2 = g.expected := loaded ▸ fields.guardExpected
  simp only [ready, Core.waitReady, Core.guardMask, Core.guardExpected, Core.field, Expr.eval,
    project, mask, expected, Guard.matches, Bool.beq_eq_decide_eq]

set_option linter.unusedSimpArgs false in
/-- A qualified standalone poll resumes FETCH on the next program row. -/
theorem success_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : DrainInput i) (waiting : s (.base .phase) = 7#3)
    (pins : Pins) (g : Guard) (loaded : s (.base .currentWord) = encode (.driveWait pins g))
    (qualified : g.matches (s (.base .stage2)) = true) :
    WaitSuccess s ((circuit a registered).step i s) := by
  obtain ⟨init, command, _⟩ := ordinary
  have matching : (s (.base .stage2) &&& g.mask) = g.expected := by
    simpa [Guard.matches] using qualified
  have fields := encode_fields (.driveWait pins g)
  have op : (encode (.driveWait pins g)).extractLsb' 0 3 = 4#3 := fields.operation
  have inc (x : BitVec 7) : x - 127#7 = x + 1 := by decide +revert +kernel
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals
    simp [step_base, step_capture, step_valid, selected, next, nextBase, originalNext,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, both, either,
      Expr.eval_bind, Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
      Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
      Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
      Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
      Core.enteringCell, Core.reserving, Core.lowEnd, Core.highEnd, Core.capturingRX, Core.capture,
      Core.advancing, Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault, Core.waitDecrement,
      Core.waitReady, Core.guardBudget, Core.guardMask, Core.guardExpected, Core.field,
      Core.nextPins, Core.inc, Core.stream, init, command, waiting, loaded, matching, op,
      fields.guardMask, fields.guardExpected, Instruction.guard, inv_one_inv, inc]
  all_goals done

set_option linter.unusedSimpArgs false in
private theorem miss_pc_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : DrainInput i) (waiting : s (.base .phase) = 7#3)
    (missed : ready i s = 0#1) :
    ((circuit a registered).step i s) (.base .pc) = s (.base .pc) := by
  obtain ⟨init, command, _⟩ := ordinary
  have mismatch :
      (s (.base .stage2) &&& (s (.base .currentWord)).extractLsb' 50 2) ≠
        (s (.base .currentWord)).extractLsb' 52 2 := by
    simp [ready, Core.waitReady, Core.guardMask, Core.guardExpected, Core.field, Expr.eval,
      project] at missed
    exact of_decide_eq_false missed
  simp [step_base, selected, nextBase, originalNext, SegmentCore.control, setCount, branch,
    fetching, both, either, Expr.eval_bind, Expr.eval, usesEntryWord, runtimeInput, decodedRegister,
    lift, withFetch, Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
    Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.starting,
    Core.free, Core.releasing, Core.advancing, Core.highEnd, Core.standaloneSuccess, Core.waitSuccess,
    Core.waitReady, Core.guardMask, Core.guardExpected, Core.field,
    init, command, waiting, mismatch, inv_one_inv]
  done

private theorem miss_pc_prefix (registered : Bool) (s : Values (Register a))
    (inputs : List (Values Core.Input))
    (waiting : s (.base .phase) = 7#3) (bounded : guardBudget s ≠ 0#8)
    (missed : MissHistory registered s inputs) (within : inputs.length ≤ (s (.base .countdown)).toNat) :
    run registered s inputs (.base .pc) = s (.base .pc) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i tail ih =>
    obtain ⟨ordinary, miss, history⟩ := missed
    let mid : Values (Register a) := (circuit a registered).step i s
    have first : MissCut s mid 1 := miss_prefix registered s [@i] waiting bounded
      ⟨ordinary, miss, trivial⟩ (by simp only [List.length_cons, List.length_nil] at within ⊢; omega)
    have midBounded : guardBudget mid ≠ 0#8 := by
      simpa only [guardBudget, first.pose.current] using bounded
    have tailWithin : tail.length ≤ (mid (.base .countdown)).toNat := by
      rw [first.countdown]
      simp only [List.length_cons] at within
      omega
    exact (ih mid first.phase midBounded history tailWithin).trans
      (miss_pc_step registered i s ordinary waiting miss)

structure WaitWindow (g : Guard) (registered : Bool) (s : Values (Register a))
    (misses : List (Values Core.Input)) (last : Values Core.Input) : Prop where
  waitingPrefix : MissCut s (run registered s misses) misses.length
  position : run registered s misses (.base .pc) = s (.base .pc)
  qualified : g.matches (run registered s misses (.base .stage2)) = true →
    WaitSuccess s (run registered s (misses ++ [@last]))
  expired : g.matches (run registered s misses (.base .stage2)) = false →
    misses.length = (s (.base .countdown)).toNat →
    TimeoutCut (run registered s misses) (run registered s (misses ++ [@last]))

/-- An admitted standalone wait preserves the previous capture throughout
its bounded aperture. On the last poll the qualified edge advances to
FETCH, while a miss retains the owner and restores installed idle drive. -/
theorem wait_window (registered : Bool) (s : Values (Register a))
    (misses : List (Values Core.Input)) (last : Values Core.Input)
    (waiting : s (.base .phase) = 7#3) (pins : Pins) (g : Guard)
    (loaded : s (.base .currentWord) = encode (.driveWait pins g))
    (bounded : guardBudget s ≠ 0#8) (history : MissHistory registered s misses)
    (within : misses.length ≤ (s (.base .countdown)).toNat) (ordinary : DrainInput last) :
    WaitWindow g registered s misses last := by
  let poll : Values (Register a) := run registered s misses
  have window := bounded_poll registered s misses last waiting bounded history within ordinary
  have pc := miss_pc_prefix registered s misses waiting bounded history within
  have wordAtPoll : poll (.base .currentWord) = encode (.driveWait pins g) :=
    window.waitingPrefix.pose.current.trans loaded
  refine ⟨window.waitingPrefix, pc, ?_, ?_⟩
  · intro qualified
    rw [run_append]
    have advance := success_step registered last poll ordinary window.waitingPrefix.phase pins g wordAtPoll qualified
    refine ⟨advance.phase, advance.pc.trans (congrArg (· + 1#7) pc), advance.countdown,
      ⟨advance.pose.current.trans window.waitingPrefix.pose.current,
        advance.pose.remaining.trans window.waitingPrefix.pose.remaining,
        advance.pose.levels.trans window.waitingPrefix.pose.levels,
        advance.pose.enabled.trans window.waitingPrefix.pose.enabled⟩,
      advance.captured.trans window.waitingPrefix.captured, advance.latched.trans window.waitingPrefix.latched,
      advance.valid.trans window.waitingPrefix.valid⟩
  · intro unqualified elapsed
    exact window.timeout (by rw [ready_from_wait last poll pins g wordAtPoll, unqualified]; rfl) elapsed

structure LoadedWait (pins : Pins) (g : Guard) (s after : Values (Register a)) : Prop where
  phase : after (.base .phase) = 7#3
  pc : after (.base .pc) = s (.base .pc)
  current : after (.base .currentWord) = encode (.driveWait pins g)
  countdown : after (.base .countdown) = g.limit.initialCountdown
  levels : after (.base .levels) = pins.levels
  enabled : after (.base .enabled) = pins.enabled
  latched : after .lastCapture = s .lastCapture
  valid : after .captureValid = s .captureValid

set_option linter.unusedSimpArgs false in
/-- A canonical standalone wait is fetched with its encoded pad pose and
initial poll counter. The row remains current until a qualified poll. -/
theorem load_wait (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (fetch : SegmentControl.AtFetch i s) (pins : Pins) (g : Guard)
    (canonical : (Instruction.driveWait pins g).Canonical)
    (loaded : (word registered).eval i s = encode (.driveWait pins g)) :
    LoadedWait pins g s ((circuit a registered).step i s) := by
  have fields := encode_fields (.driveWait pins g)
  have op : (encode (.driveWait pins g)).extractLsb' 0 3 = 4#3 := fields.operation
  have two := SourceRefinement.encode_ne_terminal (.driveWait pins g) 2 (by change 4#3 ≠ 2#3; decide)
  have three := SourceRefinement.encode_ne_terminal (.driveWait pins g) 3 (by change 4#3 ≠ 3#3; decide)
  have seven := SourceRefinement.encode_ne_terminal (.driveWait pins g) 7 (by change 4#3 ≠ 7#3; decide)
  obtain ⟨unusedDuration, unusedHigh, unusedTop⟩ := driveWait_unused pins g
  have guardOK : g.expected &&& ~~~g.mask = 0#2 := canonical
  have countdown : (if g.limit.budget = 0#8 then 0#8 else g.limit.budget - 1#8) =
      g.limit.initialCountdown := SourceRefinement.budget_initial g.limit
  have padMask (bits : BitVec 3) : ~~~(~~~bits &&& 7#3) = bits := by decide +revert +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [step_base, step_capture, step_valid, selected, next, nextBase, originalNext,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, both, either,
      kind, field, count, target, Expr.eval_bind, Expr.eval, usesEntryWord, runtimeInput,
      decodedRegister, lift, withFetch, Core.next, Core.nextRaw, Core.isPhase, Core.fetching,
      Core.clearedRuntime, Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both,
      Core.releasing, Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity,
      Core.retained, Core.enteringCell, Core.reserving, Core.advancing, Core.lowEnd, Core.highEnd,
      Core.capture, Core.capturingRX, Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess,
      Core.waitFault, Core.nextPins, Core.entryLow, Core.entryLast, Core.entryBad, Core.entryCanonical,
      Core.entryBounds, Core.entryTerminal, Core.entryHalt, Core.entryFault, Core.entryWait,
      Core.entrySkip, Core.entryStream, Core.entryPulse, Core.entryGuardCanonical,
      Core.entryGuardBudget, Core.entryGuardCountdown, Core.entryGuardExpected, Core.entryGuardMask,
      Core.entryKind, Core.entryField, Core.entryWord, Execution.readTree_correct, loaded, op,
      fields.guardMask, fields.guardExpected, fields.guardBudget, Instruction.guard, fields.lowLevels,
      fields.lowEnabled, Instruction.cell, guardOK, two, three, seven, unusedDuration, unusedHigh,
      unusedTop, fetch.initialized, fetch.ordinary, fetch.phase, fetch.inBounds, inv_one_inv, countdown, padMask]
  all_goals done

/-- A fetched bounded wait uses exactly the aperture specified in its row.
The guard tests the qualified sampler before the final edge is executed. -/
theorem run_wait_row (registered : Bool) (s : Values (Register a))
    (entry last : Values Core.Input) (misses : List (Values Core.Input))
    (fetch : SegmentControl.AtFetch entry s) (pins : Pins) (g : Guard) (n : Fin 255)
    (canonical : (Instruction.driveWait pins g).Canonical)
    (loaded : (word registered).eval entry s = encode (.driveWait pins g))
    (bounded : g.limit = .misses n)
    (history : MissHistory registered ((circuit a registered).step entry s) misses)
    (within : misses.length ≤ n.val) (ordinary : DrainInput last) :
    let entered : Values (Register a) := (circuit a registered).step entry s
    LoadedWait pins g s entered ∧ WaitWindow g registered entered misses last := by
  let entered : Values (Register a) := (circuit a registered).step entry s
  have cut : LoadedWait pins g s entered := load_wait registered entry s fetch pins g canonical loaded
  have budget : guardBudget entered ≠ 0#8 := by
    rw [guardBudget, cut.current, (encode_fields (.driveWait pins g)).guardBudget]
    change g.limit.budget ≠ 0#8
    rw [bounded]
    exact SourceRefinement.budget_nonzero n
  have count : (entered (.base .countdown)).toNat = n.val := by
    rw [cut.countdown, bounded]
    simpa only [WaitLimit.initialCountdown, BitVec.toNat_ofNat] using
      (Nat.mod_eq_of_lt (show n.val < 256 by omega))
  exact ⟨cut, wait_window registered entered misses last cut.phase pins g cut.current budget
    history (count ▸ within) ordinary⟩

end Pinwheel.Hardware.StreamingReady.SegmentWaitRefinement
