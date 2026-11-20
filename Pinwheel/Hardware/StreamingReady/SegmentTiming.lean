import Pinwheel.Hardware.StreamingReady.ProtocolOwnership
import Pinwheel.Hardware.StreamingReady.SegmentControl

/-! Timing at reached instruction cuts of the segmented Ready circuit.
The same guarded poll window serves both instruction-store layouts. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTiming

open Pinwheel.Hardware SegmentCore
open ProtocolOwnership (DrainInput)
open Pinwheel.Program.StreamingReady (Cell Guard WaitLimit encode encode_fields)

def run (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input)) :
    Values (Register a) :=
  inputs.foldl (α := Values (Register a))
    (fun state input => @Circuit.step _ _ _ (circuit a registered) input state) s

theorem run_append (registered : Bool) (s : Values (Register a))
    (before after : List (Values Core.Input)) :
    @run a registered s (before ++ after) = @run a registered (run registered s before) after := by
  unfold run
  rw [List.foldl_append]

def ready (i : Values Core.Input) (s : Values (Register a)) : BitVec 1 :=
  Core.waitReady.eval i (project s)

def guardBudget (s : Values (Register a)) : BitVec 8 :=
  (s (.base .currentWord)).extractLsb' 54 8

def rxBit (s : Values (Register a)) : BitVec 1 :=
  if (s (.base .currentWord)).extractLsb' 33 1 = 1#1 then
    (s (.base .stage2)).extractLsb' 1 1 else (s (.base .stage2)).extractLsb' 0 1

structure WaitPose (s after : Values (Register a)) : Prop where
  current : after (.base .currentWord) = s (.base .currentWord)
  remaining : after (.base .remaining) = s (.base .remaining)
  levels : after (.base .levels) = s (.base .levels)
  enabled : after (.base .enabled) = s (.base .enabled)

structure MissCut (s after : Values (Register a)) (edges : Nat) : Prop where
  phase : after (.base .phase) = 7#3
  countdown : (after (.base .countdown)).toNat = (s (.base .countdown)).toNat - edges
  pose : WaitPose s after
  captured : after (.base .rxProduced) = s (.base .rxProduced)
  latched : after .lastCapture = s .lastCapture
  valid : after .captureValid = s .captureValid

def MissHistory (registered : Bool) (s : Values (Register a)) : List (Values Core.Input) → Prop
  | [] => True
  | i :: inputs => DrainInput i ∧ ready i s = 0#1 ∧
      MissHistory registered ((circuit a registered).step i s) inputs

private def selected (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    Values (Register a) := withFetch s ((word registered).eval i s)

private theorem selected_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) :
    (circuit a registered).step i s (.base r) = (nextBase r).eval i (selected registered i s) :=
  bindWord_eval _ _ _ _

private theorem selected_capture (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .lastCapture = (next .lastCapture).eval i (selected registered i s) :=
  bindWord_eval _ _ _ _

private theorem selected_valid (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .captureValid = (next .captureValid).eval i (selected registered i s) :=
  bindWord_eval _ _ _ _

private theorem inv_one_inv (x : BitVec 1) : ~~~(1#1 &&& ~~~x) = x := by decide +revert +kernel

set_option linter.unusedSimpArgs false in
private theorem miss_edge (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : DrainInput i) (waiting : s (.base .phase) = 7#3) (miss : ready i s = 0#1)
    (bounded : guardBudget s ≠ 0#8) (positive : 0 < (s (.base .countdown)).toNat) :
    MissCut s ((circuit a registered).step i s) 1 := by
  obtain ⟨init, command, _⟩ := ordinary
  have nonzero : s (.base .countdown) ≠ 0#8 := by
    intro zero
    simp [zero] at positive
  have mismatch :
      (s (.base .stage2) &&& (s (.base .currentWord)).extractLsb' 50 2) ≠
        (s (.base .currentWord)).extractLsb' 52 2 := by
    simp [ready, Core.waitReady, Core.guardMask, Core.guardExpected, Core.field, Expr.eval,
      project] at miss
    exact of_decide_eq_false miss
  simp only [guardBudget] at bounded
  have subtract : (s (.base .countdown) - 1#8).toNat = (s (.base .countdown)).toNat - 1 := by
    apply BitVec.toNat_sub_of_le
    change 1 ≤ (s (.base .countdown)).toNat
    omega
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp [selected_base, selected_capture, selected_valid, selected, next, nextBase, originalNext, Expr.eval_bind,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, both, either,
      Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
      Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
      Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
      Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
      Core.enteringCell, Core.reserving, Core.lowEnd, Core.highEnd, Core.capturingRX, Core.capture,
      Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault, Core.waitDecrement,
      Core.waitReady, Core.guardBudget, Core.guardMask, Core.guardExpected, Core.field, Core.nextPins,
      init, command, waiting, nonzero, mismatch, bounded, subtract, inv_one_inv] <;> done

/-- Prior missed polls consume exactly one count per clock and leave the
    waiting pad pose and prior RX captures unchanged. -/
theorem miss_prefix (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (waiting : s (.base .phase) = 7#3) (bounded : guardBudget s ≠ 0#8)
    (missed : MissHistory registered s inputs) (within : inputs.length ≤ (s (.base .countdown)).toNat) :
    MissCut s (run registered s inputs) inputs.length := by
  induction inputs generalizing s with
  | nil => exact ⟨waiting, (Nat.sub_zero _).symm, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  | cons i rest ih =>
    obtain ⟨ordinary, miss, later⟩ := missed
    have positive : 0 < (s (.base .countdown)).toNat := by
      simp only [List.length_cons] at within
      omega
    let after : Values (Register a) := (circuit a registered).step i s
    have first : MissCut s after 1 := miss_edge registered i s ordinary waiting miss bounded positive
    have nextBudget : guardBudget after ≠ 0#8 := by
      simpa only [guardBudget, first.pose.current] using bounded
    have nextWithin : rest.length ≤ (after (.base .countdown)).toNat := by
      rw [first.countdown]
      simp only [List.length_cons] at within
      omega
    have tail := ih after first.phase nextBudget later nextWithin
    refine ⟨tail.phase, ?_, ⟨tail.pose.current.trans first.pose.current,
      tail.pose.remaining.trans first.pose.remaining, tail.pose.levels.trans first.pose.levels,
      tail.pose.enabled.trans first.pose.enabled⟩, tail.captured.trans first.captured,
      tail.latched.trans first.latched, tail.valid.trans first.valid⟩
    change (run registered after rest (.base .countdown)).toNat = _
    rw [tail.countdown, first.countdown]
    simp only [List.length_cons, Nat.sub_sub, Nat.add_comm]

structure ReceiveCut (s poll after : Values (Register a)) : Prop where
  phase : after (.base .phase) = 4#3
  pose : WaitPose s after
  produced : after (.base .rxProduced) = s (.base .rxProduced) + 1
  valid : after .captureValid = 1#1
  sample : after .lastCapture = rxBit poll

structure TimeoutCut (s after : Values (Register a)) : Prop where
  retained : ProtocolOwnership.TerminalCut.of after =
    { ProtocolOwnership.TerminalCut.of s with phase := 6#3 }
  txCount : after (.base .txCount) = s (.base .txCount)
  txValid : after (.base .txValid) = s (.base .txValid)
  remaining : after (.base .remaining) = s (.base .remaining)
  partialFlushed : after (.base .rxUsed) = 0#6
  levels : after (.base .levels) = s (.base .idleLevels)
  enabled : after (.base .enabled) = s (.base .idleEnabled)
  latched : after .lastCapture = s .lastCapture
  valid : after .captureValid = s .captureValid

set_option linter.unusedSimpArgs false in
private theorem receive_edge (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : DrainInput i) (waiting : s (.base .phase) = 7#3) (qualified : ready i s = 1#1)
    (stream : (s (.base .currentWord)).extractLsb' 0 3 = 1#3)
    (receives : (s (.base .currentWord)).extractLsb' 35 1 = 1#1) :
    ReceiveCut s s ((circuit a registered).step i s) := by
  obtain ⟨init, command, _⟩ := ordinary
  have matching :
      (s (.base .stage2) &&& (s (.base .currentWord)).extractLsb' 50 2) =
        (s (.base .currentWord)).extractLsb' 52 2 := by
    simp [ready, Core.waitReady, Core.guardMask, Core.guardExpected, Core.field, Expr.eval,
      project] at qualified
    exact of_decide_eq_true qualified
  have capture : (lift Core.capturingRX).eval i s = 1#1 := by
    simp [lift, Expr.eval_bind, Expr.eval, Core.capturingRX, Core.capture, Core.lowEnd,
      Core.waitSuccess, Core.waitReady, Core.guardMask, Core.guardExpected, Core.receive, Core.field,
      Core.stream, Core.both, Core.either, Core.resetting, Core.cold, Core.warm, Core.cmd, Core.isPhase,
      init, command, waiting, matching, stream, receives]
  obtain ⟨valid, sample⟩ := SegmentControl.guarded_capture registered i s init (by simp [command]) waiting capture
  have increment (x : BitVec 16) : x - 65535#16 = x + 1#16 := by
    rw [BitVec.sub_eq_add_neg, show -(65535#16) = 1#16 by decide]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, valid, sample⟩ <;>
    simp [selected_base, selected, nextBase, originalNext, Expr.eval_bind,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, both, either,
      Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
      Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
      Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
      Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
      Core.enteringCell, Core.reserving, Core.lowEnd, Core.highEnd, Core.capturingRX, Core.capture,
      Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault,
      Core.waitReady, Core.guardMask, Core.guardExpected, Core.field, Core.nextPins,
      Core.receive, Core.stream, Core.inc,
      init, command, waiting, matching, stream, receives, increment, inv_one_inv] <;> done

set_option linter.unusedSimpArgs false in
private theorem timeout_edge (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (deadline : ProtocolOwnership.AtDeadline i s) :
    TimeoutCut s ((circuit a registered).step i s) := by
  obtain ⟨retained, txCount, txValid, partialFlushed⟩ := ProtocolOwnership.deadline_step registered i s deadline
  obtain ⟨init, command, _⟩ := deadline.ordinary
  have miss := deadline.ready
  have bounded := deadline.bounded
  simp [Core.waitReady, Core.guardMask, Core.guardExpected, Core.field, Expr.eval, project] at miss
  have mismatch := of_decide_eq_false miss
  simp [Core.guardBudget, Core.field, Expr.eval, project] at bounded
  refine ⟨retained, txCount, txValid, ?_, partialFlushed, ?_, ?_, ?_, ?_⟩ <;>
    simp [selected_base, selected_capture, selected_valid, selected, next, nextBase, originalNext, Expr.eval_bind,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, both, either,
      Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
      Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
      Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
      Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
      Core.enteringCell, Core.reserving, Core.lowEnd, Core.highEnd, Core.capturingRX, Core.capture,
      Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault,
      Core.waitReady, Core.guardBudget, Core.guardMask, Core.guardExpected, Core.field, Core.nextPins,
      init, command, deadline.waiting, deadline.expired, mismatch, bounded, inv_one_inv] <;> done

structure BoundedPoll (registered : Bool) (s : Values (Register a))
    (misses : List (Values Core.Input)) (last : Values Core.Input) : Prop where
  waitingPrefix : MissCut s (run registered s misses) misses.length
  receive : ready last (run registered s misses) = 1#1 →
    (s (.base .currentWord)).extractLsb' 0 3 = 1#3 →
    (s (.base .currentWord)).extractLsb' 35 1 = 1#1 →
    ReceiveCut s (run registered s misses) (run registered s (misses ++ [@last]))
  timeout : ready last (run registered s misses) = 0#1 →
    misses.length = (s (.base .countdown)).toNat →
    TimeoutCut (run registered s misses) (run registered s (misses ++ [@last]))

/-- Inclusive deadline on the selected-word circuit. A qualified sample on
    the last allowed edge wins. A miss at that edge retains the owner and
    returns the pads to the installed idle drive. -/
theorem bounded_poll (registered : Bool) (s : Values (Register a))
    (misses : List (Values Core.Input)) (last : Values Core.Input)
    (waiting : s (.base .phase) = 7#3) (bounded : guardBudget s ≠ 0#8)
    (missed : MissHistory registered s misses) (within : misses.length ≤ (s (.base .countdown)).toNat)
    (ordinary : DrainInput last) :
    BoundedPoll registered s misses last := by
  let poll : Values (Register a) := run registered s misses
  have cut : MissCut s poll misses.length := miss_prefix registered s misses waiting bounded missed within
  have final : @run a registered s (misses ++ [@last]) =
      @Circuit.step _ _ _ (circuit a registered) last poll := by
    rw [run_append]
    rfl
  refine ⟨cut, ?_, ?_⟩
  · intro qualified stream receives
    rw [final]
    have result := receive_edge registered last poll ordinary cut.phase qualified
      (by simpa only [cut.pose.current] using stream) (by simpa only [cut.pose.current] using receives)
    exact ⟨result.phase,
      ⟨result.pose.current.trans cut.pose.current, result.pose.remaining.trans cut.pose.remaining,
        result.pose.levels.trans cut.pose.levels, result.pose.enabled.trans cut.pose.enabled⟩,
      result.produced.trans (congrArg (· + 1) cut.captured), result.valid, result.sample⟩
  · intro miss elapsed
    rw [final]
    have expired : poll (.base .countdown) = 0#8 := by
      apply BitVec.eq_of_toNat_eq
      simp only [cut.countdown, elapsed, Nat.sub_self, BitVec.toNat_zero]
    have budget : Core.guardBudget.eval last (project poll) ≠ 0#8 := by
      change guardBudget poll ≠ 0#8
      simpa only [guardBudget, cut.pose.current] using bounded
    exact timeout_edge registered last poll ⟨ordinary, cut.phase, miss, budget, expired⟩

structure GuardEntry (g : Guard) (s after : Values (Register a)) : Prop where
  phase : after (.base .phase) = 7#3
  countdown : after (.base .countdown) = g.limit.initialCountdown
  current : after (.base .currentWord) = s (.base .currentWord)
  remaining : after (.base .remaining) = s (.base .remaining)

set_option linter.unusedSimpArgs false in
/-- The end of LOW on a loaded guarded stream row starts that row's encoded
    aperture. The slot count stays with the in-flight cell. -/
theorem enter_guarded_aperture (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (cell : Cell) (g : Guard) (ordinary : DrainInput i)
    (low : s (.base .phase) = 3#3) (elapsed : s (.base .countdown) = 0#8)
    (loaded : s (.base .currentWord) = encode (.stream cell (some g))) :
    GuardEntry g s ((circuit a registered).step i s) := by
  obtain ⟨init, command, _⟩ := ordinary
  have fields := encode_fields (.stream cell (some g))
  have stream : (s (.base .currentWord)).extractLsb' 0 3 = 1#3 := loaded ▸ fields.operation
  have guarded : (s (.base .currentWord)).extractLsb' 62 1 = 1#1 := loaded ▸ fields.highGuard
  have budget : (s (.base .currentWord)).extractLsb' 54 8 = g.limit.budget := loaded ▸ fields.guardBudget
  have count : (if (s (.base .currentWord)).extractLsb' 54 8 = 0#8 then 0#8
      else (s (.base .currentWord)).extractLsb' 54 8 - 1#8) = g.limit.initialCountdown := by
    rw [budget]
    exact SourceRefinement.budget_initial _
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [selected_base, selected, nextBase, originalNext, Expr.eval_bind,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, both, either,
      Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch,
      Core.next, Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime,
      Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing,
      Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained,
      Core.enteringCell, Core.reserving, Core.lowEnd, Core.highEnd, Core.capture, Core.highGuard,
      Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault, Core.waitDecrement,
      Core.guardCountdown, Core.guardBudget, Core.field, Core.stream,
      init, command, low, elapsed, stream, guarded, count, inv_one_inv]
  by_cases zero : (s (.base .currentWord)).extractLsb' 54 8 = 0#8 <;>
    simpa [zero] using count

/-- On a loaded guarded stream, the compiled predicate is evaluated on the
    second sampler at the poll cut. -/
theorem ready_from_row (i : Values Core.Input) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (loaded : s (.base .currentWord) = encode (.stream cell (some g))) :
    ready i s = BitVec.ofBool (g.matches (s (.base .stage2))) := by
  have fields := encode_fields (.stream cell (some g))
  have mask : (s (.base .currentWord)).extractLsb' 50 2 = g.mask := loaded ▸ fields.guardMask
  have expected : (s (.base .currentWord)).extractLsb' 52 2 = g.expected := loaded ▸ fields.guardExpected
  simp only [ready, Core.waitReady, Core.guardMask, Core.guardExpected, Core.field, Expr.eval,
    project, mask, expected, Guard.matches, Bool.beq_eq_decide_eq]

/-- From the reached end of LOW, the source row fixes the available miss
    count and the second-sampler predicate. Both terminal outcomes refer to the
    real execution of the same list of circuit inputs. -/
theorem guarded_stream_window (registered : Bool) (s : Values (Register a)) (cell : Cell) (g : Guard)
    (n : Fin 255) (limit : g.limit = .misses n)
    (arm last : Values Core.Input) (misses : List (Values Core.Input))
    (armOrdinary : DrainInput arm) (lastOrdinary : DrainInput last)
    (low : s (.base .phase) = 3#3) (elapsed : s (.base .countdown) = 0#8)
    (loaded : s (.base .currentWord) = encode (.stream cell (some g)))
    (history : MissHistory registered ((circuit a registered).step arm s) misses)
    (within : misses.length ≤ n.val) :
    let entered : Values (Register a) := (circuit a registered).step arm s
    let poll : Values (Register a) := run registered entered misses
    let after : Values (Register a) := run registered s ((@arm) :: misses ++ [@last])
    GuardEntry g s entered ∧ MissCut entered poll misses.length ∧
      (g.matches (poll (.base .stage2)) = true → cell.receive = true → ReceiveCut entered poll after) ∧
      (g.matches (poll (.base .stage2)) = false → misses.length = n.val → TimeoutCut poll after) := by
  let entered : Values (Register a) := (circuit a registered).step arm s
  let poll : Values (Register a) := run registered entered misses
  have entry : GuardEntry g s entered := enter_guarded_aperture registered arm s cell g armOrdinary low elapsed loaded
  have fields := encode_fields (.stream cell (some g))
  have entryWord : entered (.base .currentWord) = encode (.stream cell (some g)) := entry.current.trans loaded
  have budget : guardBudget entered ≠ 0#8 := by
    change (entered (.base .currentWord)).extractLsb' 54 8 ≠ 0#8
    rw [entryWord, fields.guardBudget]
    change g.limit.budget ≠ 0#8
    rw [limit]
    exact SourceRefinement.budget_nonzero n
  have count : (entered (.base .countdown)).toNat = n.val := by
    rw [entry.countdown, limit]
    simpa [WaitLimit.initialCountdown, BitVec.toNat_ofNat] using (Nat.mod_eq_of_lt (show n.val < 256 by omega))
  have window := bounded_poll registered entered misses last entry.phase budget history
    (count ▸ within) lastOrdinary
  have pollWord : poll (.base .currentWord) = encode (.stream cell (some g)) :=
    window.waitingPrefix.pose.current.trans entryWord
  have sample : ready last poll = BitVec.ofBool (g.matches (poll (.base .stage2))) :=
    ready_from_row last poll cell g pollWord
  refine ⟨entry, window.waitingPrefix, ?_, ?_⟩
  · intro qualifies receives
    have stream : (entered (.base .currentWord)).extractLsb' 0 3 = 1#3 := entryWord ▸ fields.operation
    have receiveBit : (entered (.base .currentWord)).extractLsb' 35 1 = 1#1 := by
      rw [entryWord, fields.receive]
      change BitVec.ofBool cell.receive = 1#1
      rw [receives]
      rfl
    exact window.receive (by rw [sample, qualifies]; rfl) stream receiveBit
  · intro miss deadline
    exact window.timeout (by rw [sample, miss]; rfl) (count ▸ deadline)

end Pinwheel.Hardware.StreamingReady.SegmentTiming
