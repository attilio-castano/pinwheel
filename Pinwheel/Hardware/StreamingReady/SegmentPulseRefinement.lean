import Pinwheel.Hardware.StreamingReady.SegmentStreamStep

/-! Timed pulse rows of the segmented Ready core. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentPulseRefinement

open Pinwheel.Hardware SegmentCore SegmentPathControl
open Pinwheel.Program.StreamingReady

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

private theorem pad_mask (bits : BitVec 3) : ~~~(~~~bits &&& 7#3) = bits := by decide +revert +kernel

structure LoadedPulse (cell : Cell) (s after : Values (Register a)) : Prop where
  phase : after (.base .phase) = 2#3
  current : after (.base .currentWord) = encode (.pulse cell)
  pc : after (.base .pc) = s (.base .pc)
  levels : after (.base .levels) = cell.lowPins.levels
  enabled : after (.base .enabled) = cell.lowPins.enabled
  latched : after .lastCapture = s .lastCapture
  valid : after .captureValid = s .captureValid

set_option linter.unusedSimpArgs false in
/-- A canonical pulse presents the selected row's configured LOW pose at FETCH. -/
theorem load_pulse (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) (cell : Cell)
    (fetch : SegmentControl.AtFetch i s) (canonical : (Instruction.pulse cell).Canonical)
    (loaded : (word registered).eval i s = encode (.pulse cell)) :
    LoadedPulse cell s ((circuit a registered).step i s) := by
  have fields := encode_fields (.pulse cell)
  have op : (encode (.pulse cell)).extractLsb' 0 3 = 0#3 := fields.operation
  have upper : (encode (.pulse cell)).extractLsb' 31 33 = 0 := by
    simpa only [encode, cellWord_legacy] using
      Pinwheel.Program.Streaming.cellWord_pulse_upper cell canonical
  have two := SourceRefinement.encode_ne_terminal (.pulse cell) 2 (by change 0#3 ≠ 2#3; decide)
  have three := SourceRefinement.encode_ne_terminal (.pulse cell) 3 (by change 0#3 ≠ 3#3; decide)
  have seven := SourceRefinement.encode_ne_terminal (.pulse cell) 7 (by change 0#3 ≠ 7#3; decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [step_base, step_capture, step_valid, selected, next, nextBase, originalNext,
      SegmentCore.discard, SegmentCore.control,
      setCount, branch, fetching, both, either, kind, field, count, target, Expr.eval_bind,
      Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch, Core.next,
      Core.nextRaw, Core.isPhase, Core.fetching, Core.clearedRuntime, Core.cold, Core.warm,
      Core.cmd, Core.resetting, Core.either, Core.both, Core.releasing, Core.starting, Core.free,
      Core.hostOwner, Core.owned, Core.busy, Core.identity, Core.retained, Core.enteringCell,
      Core.reserving, Core.advancing, Core.lowEnd, Core.highEnd, Core.capture, Core.capturingRX, Core.guardedLowEnd,
      Core.waitSuccess, Core.standaloneSuccess, Core.waitFault, Core.nextPins, Core.entryLow,
      Core.entryLast, Core.entryBad, Core.entryCanonical, Core.entryBounds, Core.entryTerminal,
      Core.entryHalt, Core.entryFault, Core.entryWait, Core.entrySkip, Core.entryStream,
      Core.entryPulse, Core.entryKind, Core.entryField, Core.entryWord, Execution.readTree_correct,
      loaded, op, upper, two, three, seven, fields.lowLevels, fields.lowEnabled, Instruction.cell,
      fetch.initialized, fetch.ordinary, fetch.phase, fetch.inBounds, inv_one_inv, pad_mask]
  all_goals done

private theorem slices_3 (bits : BitVec 3) :
    bits.extractLsb' 2 1 ++ bits.extractLsb' 1 1 ++ bits.extractLsb' 0 1 = bits :=
  by decide +revert +kernel

structure PulsePhase (cell : Cell) (high : Bool) (s after : Values (Register a)) : Prop where
  phase : after (.base .phase) = if high then 4#3 else 3#3
  current : after (.base .currentWord) = s (.base .currentWord)
  remaining : after (.base .remaining) = s (.base .remaining)
  countdown : after (.base .countdown) =
    BitVec.ofNat 8 (if high then cell.highDuration.val else cell.lowDuration.val)
  pc : after (.base .pc) = s (.base .pc)
  levels : after (.base .levels) = (if high then cell.highPins else cell.lowPins).levels
  enabled : after (.base .enabled) = (if high then cell.highPins else cell.lowPins).enabled
  reserved : after (.base .txConsumed) = s (.base .txConsumed)
  produced : after (.base .rxProduced) = s (.base .rxProduced)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
/-- A loaded pulse reserves no TX or RX capacity. Its LOW and HIGH entry
    edges carry the duration and pad pose encoded in the pulse. -/
theorem enter_phase (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (cell : Cell) (high : Bool) (ordinary : NoReset i)
    (beforePhase : s (.base .phase) = if high then 3#3 else 2#3)
    (elapsed : high = true → s (.base .countdown) = 0#8)
    (loaded : s (.base .currentWord) = encode (.pulse cell)) :
    PulsePhase cell high s ((circuit a registered).step i s) := by
  have fields := encode_fields (.pulse cell)
  have op : (s (.base .currentWord)).extractLsb' 0 3 = 0#3 := loaded ▸ fields.operation
  have low : (s (.base .currentWord)).extractLsb' 3 8 = BitVec.ofNat 8 cell.lowDuration.val :=
    loaded ▸ fields.lowDuration
  have highPeriod : (s (.base .currentWord)).extractLsb' 11 8 = BitVec.ofNat 8 cell.highDuration.val :=
    loaded ▸ fields.highDuration
  have lowLevels : (s (.base .currentWord)).extractLsb' 19 3 = cell.lowPins.levels := loaded ▸ fields.lowLevels
  have lowEnabled : (s (.base .currentWord)).extractLsb' 22 3 = cell.lowPins.enabled := loaded ▸ fields.lowEnabled
  have highLevels : (s (.base .currentWord)).extractLsb' 25 3 = cell.highPins.levels := loaded ▸ fields.highLevels
  have highEnabled : (s (.base .currentWord)).extractLsb' 28 3 = cell.highPins.enabled := loaded ▸ fields.highEnabled
  cases high <;>
    simp only [Bool.false_eq_true, if_false, if_true, true_implies] at beforePhase elapsed <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [step_base, selected, nextBase, originalNext, SegmentCore.discard, SegmentCore.control,
      setCount, branch, fetching, both, either, kind, field, count, target, Expr.eval_bind, Expr.eval,
      usesEntryWord, runtimeInput, decodedRegister, lift, withFetch, Core.next, Core.nextRaw,
      Core.isPhase, Core.fetching, Core.clearedRuntime, Core.cold, Core.warm, Core.cmd, Core.resetting,
      Core.either, Core.both, Core.releasing, Core.starting, Core.free, Core.hostOwner, Core.owned,
      Core.busy, Core.identity, Core.retained, Core.enteringCell, Core.reserving, Core.takingTX,
      Core.advancing, Core.lowEnd, Core.highEnd, Core.capture, Core.guardedLowEnd, Core.waitSuccess,
      Core.standaloneSuccess, Core.waitFault, Core.waitDecrement, Core.capturingRX, Core.stream,
      Core.receive, Core.transmit, Core.credit, Core.guardBudget, Core.highGuard, Core.field,
      Core.nextPins, Core.driven, Core.basePins, Core.lastCell, Core.pack, ordinary.1, ordinary.2,
      beforePhase, elapsed, op, low, highPeriod, lowLevels, lowEnabled, highLevels, highEnabled,
      inv_one_inv, pad_mask, slices_3] <;> done

private theorem copy_capture {s after : Values (Register a)}
    (latched : after .lastCapture = s .lastCapture) (valid : after .captureValid = s .captureValid)
    (held : HasCapture s capture) : HasCapture after capture := by
  cases capture <;> simpa only [HasCapture, latched, valid] using held

set_option linter.unusedSimpArgs false in
private theorem capture_held (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (cell : Cell) (ordinary : NoReset i) (phase : s (.base .phase) = 2#3 ∨ s (.base .phase) = 3#3)
    (loaded : s (.base .currentWord) = encode (.pulse cell)) (capture : HasCapture s bit) :
    HasCapture ((circuit a registered).step i s) bit := by
  have op : (s (.base .currentWord)).extractLsb' 0 3 = 0#3 := loaded ▸ (encode_fields (.pulse cell)).operation
  refine copy_capture ?_ ?_ capture <;>
    rcases phase with phase | phase <;>
    simp [step_capture, step_valid, selected, next, Expr.eval_bind, withFetch, lift, Expr.eval,
      SegmentCore.control, setCount, branch, fetching, both, either, Core.clearedRuntime,
      Core.resetting, Core.cold, Core.warm, Core.cmd, Core.isPhase, Core.either, Core.both,
      Core.starting, Core.releasing, Core.free, Core.hostOwner, Core.owned, Core.retained, Core.busy,
      Core.identity, Core.capturingRX, Core.capture, Core.lowEnd, Core.waitSuccess, Core.fetching,
      Core.receive, Core.stream, Core.field, op, phase, ordinary.1, ordinary.2, inv_one_inv] <;> done

private theorem low_capture_held (registered : Bool) (s : Values (Register a)) (cell : Cell)
    (inputs : List (Values Core.Input)) (phase : s (.base .phase) = 3#3)
    (loaded : s (.base .currentWord) = encode (.pulse cell))
    (within : inputs.length ≤ (s (.base .countdown)).toNat)
    (ordinary : ∀ i ∈ inputs, ProtocolOwnership.DrainInput i) (capture : HasCapture s bit) :
    HasCapture (SegmentTiming.run registered s inputs) bit := by
  induction inputs generalizing s with
  | nil => exact capture
  | cons i rest ih =>
    let after : Values (Register a) := (circuit a registered).step i s
    have one : [@i].length ≤ (s (.base .countdown)).toNat := by
      simp only [List.length_cons, List.length_nil]
      simp only [List.length_cons] at within
      omega
    have drain := ordinary i (by simp)
    have edge : SegmentStreamStep.LowSpan s after 1 :=
      SegmentStreamStep.low_span registered s [@i] phase one (by simpa using drain)
    have preserved := capture_held registered i s cell ⟨drain.1, by simp [drain.2.1]⟩
      (.inr phase) loaded capture
    have nextWithin : rest.length ≤ (after (.base .countdown)).toNat := by
      rw [edge.countdown]
      simp only [List.length_cons] at within
      omega
    exact ih after edge.phase (edge.pose.current.trans loaded) nextWithin
      (fun j hj => ordinary j (List.mem_cons_of_mem (α := Values Core.Input) i hj)) preserved

/-- The selected pulse starts without a queue reservation, presents its
    encoded LOW and HIGH poses, and advances after the declared durations.
    The installed image and previous qualified capture reach the next FETCH. -/
theorem run_pulse_row (registered : Bool) (s : Values (Register a)) (cell : Cell)
    (atFetch : AtBoundary registered rows pc capture s)
    (row : rows[pc]? = some (.cell (.pulse cell)))
    (canonical : (Instruction.pulse cell).Canonical)
    (entry reserveInput rise fall : Values Core.Input)
    (lowHolds highHolds : List (Values Core.Input))
    (entryOrdinary : NoReset entry) (reserveOrdinary : NoReset reserveInput)
    (riseOrdinary : NoReset rise) (fallOrdinary : NoReset fall)
    (lowOrdinary : ∀ i ∈ lowHolds, ProtocolOwnership.DrainInput i)
    (highOrdinary : ∀ i ∈ highHolds, NoReset i)
    (lowDuration : lowHolds.length = cell.lowDuration.val)
    (highDuration : highHolds.length = cell.highDuration.val) :
    let loaded : Values (Register a) := (circuit a registered).step entry s
    let reserved : Values (Register a) := (circuit a registered).step reserveInput loaded
    let low : Values (Register a) := SegmentTiming.run registered reserved lowHolds
    let high : Values (Register a) := (circuit a registered).step rise low
    let after : Values (Register a) := SegmentTiming.run registered high (highHolds ++ [@fall])
    LoadedPulse cell s loaded ∧ PulsePhase cell false loaded reserved ∧
      SegmentStreamStep.LowSpan reserved low lowHolds.length ∧ PulsePhase cell true low high ∧
      AtBoundary registered rows (pc + 1) capture after := by
  let loaded : Values (Register a) := (circuit a registered).step entry s
  let reserved : Values (Register a) := (circuit a registered).step reserveInput loaded
  let low : Values (Register a) := SegmentTiming.run registered reserved lowHolds
  let high : Values (Register a) := (circuit a registered).step rise low
  have inBounds := (List.getElem?_eq_some_iff.mp row).1
  have fetch : SegmentControl.AtFetch entry s := ⟨entryOrdinary.1, entryOrdinary.2, atFetch.phase, by
    rw [atFetch.position, atFetch.installed.count]
    exact inBounds⟩
  have load := load_pulse registered entry s cell fetch canonical (selected_row atFetch entry row)
  have atLoad : loaded (.base .phase) = 2#3 := load.phase
  have reserve := enter_phase registered reserveInput loaded cell false reserveOrdinary atLoad
    (by intro impossible; cases impossible) load.current
  have reservedPhase : reserved (.base .phase) = 3#3 := reserve.phase
  have reservedDuration : reserved (.base .countdown) = BitVec.ofNat 8 cell.lowDuration.val := reserve.countdown
  have lows : lowHolds.length = (reserved (.base .countdown)).toNat := by
    rw [reservedDuration, lowDuration, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cell.lowDuration.isLt]
  have held := SegmentStreamStep.low_span registered reserved lowHolds reservedPhase (Nat.le_of_eq lows) lowOrdinary
  have elapsed : low (.base .countdown) = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    exact held.countdown.trans (by simp [lows])
  have lowWord : low (.base .currentWord) = encode (.pulse cell) :=
    held.pose.current.trans (reserve.current.trans load.current)
  have risePose := enter_phase registered rise low cell true riseOrdinary held.phase (fun _ => elapsed) lowWord
  have highPhase : high (.base .phase) = 4#3 := risePose.phase
  have highPeriod : high (.base .countdown) = BitVec.ofNat 8 cell.highDuration.val := risePose.countdown
  have highs : highHolds.length = (high (.base .countdown)).toNat := by
    rw [highPeriod, highDuration, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cell.highDuration.isLt]
  have loadedImage := (image_frame registered entry s entryOrdinary (.inl (by simp [atFetch.phase]))).installed
    atFetch.installed
  have reservedImage := (image_frame registered reserveInput loaded reserveOrdinary (.inl (by simp [atLoad]))).installed
    loadedImage
  have lowPhase : low (.base .phase) = 3#3 := held.phase
  have highImage := (image_frame registered rise low riseOrdinary (.inl (by simp [lowPhase]))).installed
    (held.image.installed reservedImage)
  have current : high (.base .currentWord) = encode (.pulse cell) :=
    risePose.current.trans lowWord
  have notStream : ¬ IsStream high := by
    change ¬((high (.base .currentWord)).extractLsb' 0 3 = 1#3)
    rw [current, (encode_fields (.pulse cell)).operation]
    change 0#3 ≠ 1#3
    decide
  have place : (high (.base .pc)).toNat = pc :=
    (congrArg BitVec.toNat (risePose.pc.trans (held.pc.trans (reserve.pc.trans load.pc)))).trans atFetch.position
  have loadedCapture : HasCapture loaded capture := copy_capture load.latched load.valid atFetch.latched
  have reservedCapture : HasCapture reserved capture :=
    capture_held registered reserveInput loaded cell reserveOrdinary (.inl atLoad) load.current loadedCapture
  have lowCapture : HasCapture low capture := low_capture_held registered reserved cell lowHolds reservedPhase
    (reserve.current.trans load.current) (Nat.le_of_eq lows) lowOrdinary reservedCapture
  have highCapture : HasCapture high capture :=
    capture_held registered rise low cell riseOrdinary (.inr lowPhase) lowWord lowCapture
  exact ⟨load, reserve, held, risePose, high_to_boundary registered high highHolds fall highOrdinary fallOrdinary
    highPhase highs (fun repeatCell => notStream repeatCell.1) highImage place inBounds highCapture⟩

end Pinwheel.Hardware.StreamingReady.SegmentPulseRefinement
