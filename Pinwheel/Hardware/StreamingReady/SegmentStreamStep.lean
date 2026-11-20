import Pinwheel.Hardware.StreamingReady.SegmentControl
import Pinwheel.Hardware.StreamingReady.SegmentPathControl
import Pinwheel.Hardware.StreamingReady.SegmentPollRefinement
import Pinwheel.Hardware.StreamingReady.SegmentTiming

/-! From an encoded stream fetch to the LOW cut consumed by the guarded
poll theorem. Reservations use pre-edge credit and the pre-edge TX bit. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentStreamStep

open Pinwheel.Hardware SegmentCore
open Pinwheel.Program.StreamingReady

private def selected (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    Values (Register a) := withFetch s ((word registered).eval i s)

private theorem step_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) :
    (circuit a registered).step i s (.base r) = (nextBase r).eval i (selected registered i s) :=
  bindWord_eval _ _ _ _

private theorem inv_one_inv (x : BitVec 1) : ~~~(1#1 &&& ~~~x) = x := by decide +revert +kernel

private theorem credit_eval (i : Values Core.Input) (s : Values (Register a)) (fetched : BitVec 64)
    (decode : Bool) :
    Core.credit.eval (fun input => (runtimeInput input).eval i (withFetch s fetched))
      (fun r => (if decode then decodedRegister r else .reg (.base r)).eval i (withFetch s fetched)) =
      Core.credit.eval i (project s) := by
  cases decode <;> rfl

structure Reservation (cell : Cell) (i : Values Core.Input) (s after : Values (Register a)) : Prop where
  phase : after (.base .phase) = 3#3
  current : after (.base .currentWord) = s (.base .currentWord)
  remaining : after (.base .remaining) = s (.base .remaining)
  pc : after (.base .pc) = s (.base .pc)
  countdown : after (.base .countdown) = cell.lowDuration
  bit : after (.base .cellBit) =
    (if cell.transmit then Core.nextBit.eval i (project s) else 0#1)
  txConsumed : after (.base .txConsumed) =
    s (.base .txConsumed) + (if cell.transmit then 1#16 else 0#16)

set_option linter.unusedSimpArgs false in
/-- A stream at a credit-bearing boundary enters LOW with the same row and
slot count. The TX bit and reservation counter refer to the old queue. -/
theorem reserve_runtime (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (cell : Cell) (guard : Option Guard) (ordinary : SegmentPathControl.NoReset i)
    (boundary : s (.base .phase) = 2#3)
    (loaded : s (.base .currentWord) = encode (.stream cell guard))
    (credit : Core.credit.eval i (project s) = 1#1) :
    Reservation cell i s ((circuit a registered).step i s) := by
  obtain ⟨init, cmd⟩ := ordinary
  have fields := encode_fields (.stream cell guard)
  have operation : (s (.base .currentWord)).extractLsb' 0 3 = 1#3 := loaded ▸ fields.operation
  have transmit : (s (.base .currentWord)).extractLsb' 34 1 = BitVec.ofBool cell.transmit :=
    loaded ▸ fields.transmit
  have low : (s (.base .currentWord)).extractLsb' 3 8 = cell.lowDuration := loaded ▸ fields.lowDuration
  have inc (count : BitVec 16) : count - 65535#16 = count + 1 := by decide +revert +kernel
  have decoded := (credit_eval i s ((word registered).eval i s) true).trans credit
  have base := (credit_eval i s ((word registered).eval i s) false).trans credit
  simp [runtimeInput, decodedRegister, Expr.eval, withFetch, both] at decoded base
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [step_base, selected, nextBase, originalNext, Expr.eval_bind, SegmentCore.discard,
      SegmentCore.control, setCount, branch, fetching, both, either, Expr.eval, usesEntryWord,
      runtimeInput, decodedRegister, lift, withFetch, Core.next, Core.nextRaw, Core.isPhase,
      Core.fetching, Core.clearedRuntime, Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either,
      Core.both, Core.releasing, Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy,
      Core.retained, Core.identity, Core.enteringCell, Core.reserving, Core.takingTX, Core.advancing,
      Core.lowEnd, Core.highEnd, Core.capture, Core.guardedLowEnd, Core.waitSuccess,
      Core.standaloneSuccess, Core.waitFault, Core.waitDecrement, Core.stream, Core.transmit,
      Core.field, Core.inc, Core.nextBit, Core.txSource, Core.txHeadWord, Execution.readTree_correct, project,
      init, cmd, boundary, operation, transmit, low, inv_one_inv, decoded, base, inc]
  all_goals cases h : cell.transmit <;> simp [h] <;> rfl
  all_goals done

theorem reserve (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (cell : Cell) (guard : Option Guard) (ordinary : ProtocolOwnership.DrainInput i)
    (boundary : s (.base .phase) = 2#3)
    (loaded : s (.base .currentWord) = encode (.stream cell guard))
    (credit : Core.credit.eval i (project s) = 1#1) :
    Reservation cell i s ((circuit a registered).step i s) :=
  reserve_runtime registered i s cell guard ⟨ordinary.1, by simp [ordinary.2.1]⟩ boundary loaded credit

structure CreditPark (s after : Values (Register a)) : Prop where
  phase : after (.base .phase) = 2#3
  pose : SegmentTiming.WaitPose s after
  pc : after (.base .pc) = s (.base .pc)
  reserved : after (.base .txConsumed) = s (.base .txConsumed)
  produced : after (.base .rxProduced) = s (.base .rxProduced)

set_option linter.unusedSimpArgs false in
/-- With no pre-edge credit, a boundary holds its pad pose and takes no
    reservation or sample. This includes an edge that frees future RX credit. -/
theorem park_runtime (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : SegmentPathControl.NoReset i) (boundary : s (.base .phase) = 2#3)
    (credit : Core.credit.eval i (project s) = 0#1) :
    CreditPark s ((circuit a registered).step i s) := by
  obtain ⟨init, cmd⟩ := ordinary
  have decoded := (credit_eval i s ((word registered).eval i s) true).trans credit
  have base := (credit_eval i s ((word registered).eval i s) false).trans credit
  simp [runtimeInput, decodedRegister, Expr.eval, withFetch, both] at decoded base
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp [step_base, selected, nextBase, originalNext, Expr.eval_bind, SegmentCore.discard,
      SegmentCore.control, setCount, branch, fetching, both, either, Expr.eval, usesEntryWord,
      runtimeInput, decodedRegister, lift, withFetch, Core.next, Core.nextRaw, Core.isPhase,
      Core.fetching, Core.clearedRuntime, Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either,
      Core.both, Core.releasing, Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy,
      Core.retained, Core.identity, Core.enteringCell, Core.reserving, Core.takingTX, Core.advancing,
      Core.lowEnd, Core.highEnd, Core.capture, Core.guardedLowEnd, Core.waitSuccess,
      Core.standaloneSuccess, Core.waitFault, Core.waitDecrement, Core.nextPins, Core.capturingRX,
      init, cmd, boundary, decoded, base, inv_one_inv] <;> done

theorem park (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : ProtocolOwnership.DrainInput i) (boundary : s (.base .phase) = 2#3)
    (credit : Core.credit.eval i (project s) = 0#1) :
    CreditPark s ((circuit a registered).step i s) :=
  park_runtime registered i s ⟨ordinary.1, by simp [ordinary.2.1]⟩ boundary credit

structure LowSpan (s after : Values (Register a)) (clocks : Nat) : Prop where
  phase : after (.base .phase) = 3#3
  countdown : (after (.base .countdown)).toNat = (s (.base .countdown)).toNat - clocks
  pose : SegmentTiming.WaitPose s after
  pc : after (.base .pc) = s (.base .pc)
  reserved : after (.base .txConsumed) = s (.base .txConsumed)
  image : SegmentPathControl.ImageFrame s after

set_option linter.unusedSimpArgs false in
private theorem low_tick (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : SegmentPathControl.NoReset i) (phase : s (.base .phase) = 3#3)
    (positive : 0 < (s (.base .countdown)).toNat) :
    LowSpan s ((circuit a registered).step i s) 1 := by
  obtain ⟨init, cmd⟩ := ordinary
  have nonzero : s (.base .countdown) ≠ 0#8 := by
    intro zero
    simp [zero] at positive
  have tick : (s (.base .countdown) - 1#8).toNat = (s (.base .countdown)).toNat - 1 :=
    BitVec.toNat_sub_of_le positive
  have image := SegmentPathControl.image_frame registered i s
    ⟨init, cmd⟩ (Or.inl (by simp [phase]))
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, image⟩ <;>
    simp [step_base, selected, nextBase, originalNext, Expr.eval_bind, SegmentCore.discard,
      SegmentCore.control, setCount, branch, fetching, both, either, Expr.eval, usesEntryWord,
      runtimeInput, decodedRegister, lift, withFetch, Core.next, Core.nextRaw, Core.isPhase,
      Core.fetching, Core.clearedRuntime, Core.cold, Core.warm, Core.cmd, Core.resetting, Core.either,
      Core.both, Core.releasing, Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy,
      Core.retained, Core.identity, Core.enteringCell, Core.reserving, Core.takingTX, Core.advancing,
      Core.lowEnd, Core.highEnd, Core.capture, Core.guardedLowEnd, Core.waitSuccess,
      Core.standaloneSuccess, Core.waitFault, Core.waitDecrement, Core.nextPins,
      init, cmd, phase, nonzero, tick, inv_one_inv] <;> done

/-- A LOW prefix spends exactly its elapsed clocks and keeps the same row,
pad pose, reservation and instruction position even during a host refill. -/
theorem low_span_runtime (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (phase : s (.base .phase) = 3#3) (within : inputs.length ≤ (s (.base .countdown)).toNat)
    (ordinary : ∀ i ∈ inputs, SegmentPathControl.NoReset i) :
    LowSpan s (SegmentTiming.run registered s inputs) inputs.length := by
  induction inputs generalizing s with
  | nil => exact ⟨phase, (Nat.sub_zero _).symm, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl, fun _ => rfl, rfl⟩⟩
  | cons i rest ih =>
    have positive : 0 < (s (.base .countdown)).toNat := by
      simp only [List.length_cons] at within
      omega
    let after : Values (Register a) := (circuit a registered).step i s
    have first : LowSpan s after 1 := low_tick registered i s (ordinary i (by simp)) phase positive
    have nextWithin : rest.length ≤ (after (.base .countdown)).toNat := by
      rw [first.countdown]
      simp only [List.length_cons] at within
      omega
    have tail := ih after first.phase nextWithin (fun r member => ordinary r (List.mem_cons_of_mem _ member))
    refine ⟨tail.phase, ?_, ⟨tail.pose.current.trans first.pose.current,
      tail.pose.remaining.trans first.pose.remaining, tail.pose.levels.trans first.pose.levels,
      tail.pose.enabled.trans first.pose.enabled⟩, tail.pc.trans first.pc, tail.reserved.trans first.reserved,
      ⟨tail.image.count.trans first.image.count, tail.image.valid.trans first.image.valid,
        fun addr => (tail.image.word addr).trans (first.image.word addr),
        tail.image.generation.trans first.image.generation⟩⟩
    change (SegmentTiming.run registered after rest (.base .countdown)).toNat = _
    rw [tail.countdown, first.countdown]
    simp only [List.length_cons, Nat.sub_sub, Nat.add_comm]

theorem low_span (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (phase : s (.base .phase) = 3#3) (within : inputs.length ≤ (s (.base .countdown)).toNat)
    (ordinary : ∀ i ∈ inputs, ProtocolOwnership.DrainInput i) :
    LowSpan s (SegmentTiming.run registered s inputs) inputs.length :=
  low_span_runtime registered s inputs phase within fun i member =>
    let drain := ordinary i member
    ⟨drain.1, by simp [drain.2.1]⟩

structure LoadedStream (cell : Cell) (guard : Option Guard) (s after : Values (Register a)) : Prop where
  phase : after (.base .phase) = 2#3
  current : after (.base .currentWord) = encode (.stream cell guard)
  remaining : after (.base .remaining) = s (.base .remaining)
  pc : after (.base .pc) = s (.base .pc)

set_option linter.unusedSimpArgs false in
/-- The fetched canonical row becomes the live stream row. FETCH
does not reserve credit and keeps the count already supplied by COUNT. -/
theorem load_stream (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (cell : Cell) (guard : Option Guard) (fetch : SegmentControl.AtFetch i s)
    (canonical : (Instruction.stream cell guard).Canonical)
    (slots : s (.base .remaining) ≠ 0#16)
    (loaded : (word registered).eval i s = encode (.stream cell guard)) :
    LoadedStream cell guard s ((circuit a registered).step i s) := by
  have fields := encode_fields (.stream cell guard)
  have op : (encode (.stream cell guard)).extractLsb' 0 3 = 1#3 := fields.operation
  have two := SourceRefinement.encode_ne_terminal (.stream cell guard) 2 (by change 1#3 ≠ 2#3; decide)
  have three := SourceRefinement.encode_ne_terminal (.stream cell guard) 3 (by change 1#3 ≠ 3#3; decide)
  have seven := SourceRefinement.encode_ne_terminal (.stream cell guard) 7 (by change 1#3 ≠ 7#3; decide)
  have selector : cell.txOutput.val % 4 < 3 := by
    have bound := cell.txOutput.isLt
    omega
  have unused : (encode (.stream cell none)).extractLsb' 50 12 = 0 := by
    unfold encode cellWord guardWord
    repeat first
      | rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
      | rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
    simp [WaitLimit.budget]
  cases guard
  case' some g => change g.expected &&& ~~~g.mask = 0#2 at canonical
  all_goals refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp [step_base, selected, nextBase, originalNext, Expr.eval_bind, SegmentCore.discard,
      SegmentCore.control, setCount, branch, fetching, both, either, kind, field, count, target,
      Expr.eval, usesEntryWord, runtimeInput, decodedRegister, lift, withFetch, Core.next, Core.nextRaw,
      Core.isPhase, Core.fetching, Core.clearedRuntime, Core.cold, Core.warm, Core.cmd, Core.resetting,
      Core.either, Core.both, Core.releasing, Core.starting, Core.free, Core.hostOwner, Core.owned, Core.busy,
      Core.retained, Core.identity, Core.enteringCell, Core.reserving, Core.advancing, Core.lowEnd, Core.highEnd,
      Core.capture, Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault,
      Core.entryBad, Core.entryCanonical, Core.entryBounds, Core.entryTerminal, Core.entryHalt,
      Core.entryFault, Core.entryWait, Core.entrySkip, Core.entryStream, Core.entryPulse,
      Core.entryGuardCanonical, Core.entryGuardExpected, Core.entryGuardMask, Core.entryKind, Core.entryField,
      Core.entryWord, Execution.readTree_correct, loaded, op, fields.reserved, fields.highGuard,
      Instruction.hasHighGuard, fields.guardMask, fields.guardExpected, Instruction.guard,
      fields.transmit, fields.txOutput, Instruction.cell, selector, canonical, unused, two, three, seven, slots,
      fetch.initialized, fetch.ordinary, fetch.phase, fetch.inBounds, inv_one_inv]
  all_goals done

theorem load_guarded_stream (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (cell : Cell) (guard : Guard) (fetch : SegmentControl.AtFetch i s)
    (canonical : (Instruction.stream cell (some guard)).Canonical)
    (slots : s (.base .remaining) ≠ 0#16)
    (loaded : (word registered).eval i s = encode (.stream cell (some guard))) :
    LoadedStream cell (some guard) s ((circuit a registered).step i s) :=
  load_stream registered i s cell (some guard) fetch canonical slots loaded

/-- The installed stream row and COUNT survive the complete run from FETCH
through an available-credit reservation and the programmed LOW duration. -/
theorem guarded_low_from_fetch (registered : Bool) (s : Values (Register a))
    (cell : Cell) (guard : Guard) (fetch admit : Values Core.Input)
    (low : List (Values Core.Input))
    (boundary : SegmentPathControl.AtBoundary registered rows pc capture s)
    (fetchOrdinary : SegmentPathControl.NoReset fetch)
    (row : rows[pc]? = some (.cell (.stream cell (some guard))))
    (canonical : (Instruction.stream cell (some guard)).Canonical)
    (slots : s (.base .remaining) ≠ 0#16)
    (ordinary : ProtocolOwnership.DrainInput admit)
    (credit : Core.credit.eval admit (project ((circuit a registered).step fetch s)) = 1#1)
    (duration : low.length = cell.lowDuration.val)
    (lowOrdinary : ∀ i ∈ low, ProtocolOwnership.DrainInput i) :
    let armed : Values (Register a) := SegmentTiming.run registered s ((@fetch) :: (@admit) :: low)
    armed (.base .phase) = 3#3 ∧
      armed (.base .countdown) = 0#8 ∧
      armed (.base .currentWord) = encode (.stream cell (some guard)) ∧
      armed (.base .pc) = s (.base .pc) ∧
      armed (.base .remaining) = s (.base .remaining) ∧
      SegmentPathControl.Installed rows armed := by
  let reached : Values (Register a) := (circuit a registered).step fetch s
  let reserved : Values (Register a) := (circuit a registered).step admit reached
  have atFetch : SegmentControl.AtFetch fetch s := by
    refine ⟨fetchOrdinary.1, fetchOrdinary.2, boundary.phase, ?_⟩
    rw [boundary.position, boundary.installed.count]
    exact (List.getElem?_eq_some_iff.mp row).1
  have loaded := SegmentPathControl.selected_row boundary fetch row
  have entry := load_guarded_stream registered fetch s cell guard atFetch canonical slots loaded
  have first := reserve registered admit reached cell (some guard) ordinary entry.phase entry.current credit
  have timer : (reserved (.base .countdown)).toNat = cell.lowDuration.val := by
    have programmed := congrArg BitVec.toNat first.countdown
    change (reserved (.base .countdown)).toNat = (BitVec.ofNat 8 cell.lowDuration.val).toNat at programmed
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show cell.lowDuration.val < 256 from cell.lowDuration.isLt)]
      using programmed
  have pulse := low_span registered reserved low first.phase (Nat.le_of_eq (duration.trans timer.symm)) lowOrdinary
  have firstImage := SegmentPathControl.image_frame registered fetch s fetchOrdinary
    (Or.inl (by simp [boundary.phase]))
  have reachedPhase : reached (.base .phase) = 2#3 := entry.phase
  have nextImage := SegmentPathControl.image_frame registered admit reached
    ⟨ordinary.1, by simp [ordinary.2.1]⟩ (Or.inl (by simp [reachedPhase]))
  have image := pulse.image.installed (nextImage.installed (firstImage.installed boundary.installed))
  refine ⟨pulse.phase, ?_, pulse.pose.current.trans (first.current.trans entry.current),
    pulse.pc.trans (first.pc.trans entry.pc), pulse.pose.remaining.trans (first.remaining.trans entry.remaining), image⟩
  apply BitVec.eq_of_toNat_eq
  change (SegmentTiming.run registered reserved low (.base .countdown)).toNat = 0
  rw [pulse.countdown, timer, duration, Nat.sub_self]

/-- The FETCH, reservation, LOW and HIGH dwells, and encoded branch form
one run. The executable source poll determines the actual successor. -/
theorem one_slot_to_branch (registered : Bool) (s : Values (Register a))
    (cell : Cell) (guard : Guard) (n : Fin 255) (limit : guard.limit = .misses n)
    (receive : cell.receive = true) (fetch admit arm pollLast highLast branchInput : Values Core.Input)
    (low misses high : List (Values Core.Input))
    (boundary : SegmentPathControl.AtBoundary registered rows pc capture s)
    (fetchOrdinary : SegmentPathControl.NoReset fetch)
    (row : rows[pc]? = some (.cell (.stream cell (some guard))))
    (canonical : (Instruction.stream cell (some guard)).Canonical)
    (slot : s (.base .remaining) = 1#16)
    (admitOrdinary : ProtocolOwnership.DrainInput admit)
    (credit : Core.credit.eval admit (project ((circuit a registered).step fetch s)) = 1#1)
    (lowDuration : low.length = cell.lowDuration.val)
    (lowOrdinary : ∀ i ∈ low, ProtocolOwnership.DrainInput i)
    (armOrdinary : ProtocolOwnership.DrainInput arm)
    (pollOrdinary : ProtocolOwnership.DrainInput pollLast)
    (history : SegmentTiming.MissHistory registered
      ((circuit a registered).step arm (SegmentTiming.run registered s ((@fetch) :: (@admit) :: low))) misses)
    (within : misses.length ≤ n.val)
    (qualified : guard.matches
      (SegmentTiming.run registered
        ((circuit a registered).step arm (SegmentTiming.run registered s ((@fetch) :: (@admit) :: low)))
        misses (.base .stage2)) = true)
    (highDuration : high.length = cell.highDuration.val)
    (highOrdinary : ∀ i ∈ high, SegmentPathControl.NoReset i)
    (endOrdinary : SegmentPathControl.NoReset highLast)
    (branchOrdinary : SegmentPathControl.NoReset branchInput)
    (destination : BitVec 6) (onBit : Bool) (branch : rows[pc + 1]? = some (.branch destination onBit))
    (forward : pc + 1 < destination.toNat) (inBounds : destination.toNat < rows.length) :
    let armed : Values (Register a) := SegmentTiming.run registered s ((@fetch) :: (@admit) :: low)
    let entered : Values (Register a) := (circuit a registered).step arm armed
    let sample := SegmentTiming.run registered entered misses (.base .stage2)
    let acquired : Values (Register a) := SegmentTiming.run registered armed ((@arm) :: misses ++ [@pollLast])
    let fetched : Values (Register a) := SegmentTiming.run registered acquired (high ++ [@highLast])
    let after : Values (Register a) := (circuit a registered).step branchInput fetched
    Program.StreamingReadySegments.Execution.pollWindow guard
      (SegmentPollRefinement.stage2Samples registered entered misses ++ [sample]) = some (some sample) ∧
    SegmentPathControl.AtBoundary registered rows
      (if sample[cell.rxInput.val] = onBit then destination.toNat else pc + 2) none after := by
  obtain ⟨phase, timer, word, position, remaining, installed⟩ :=
    guarded_low_from_fetch registered s cell guard fetch admit low boundary fetchOrdinary row canonical
      (by simp [slot]) admitOrdinary credit lowDuration lowOrdinary
  obtain ⟨verdict, branched, _⟩ := SegmentPollRefinement.qualified_last_slot_to_branch registered
    (SegmentTiming.run registered s ((@fetch) :: (@admit) :: low)) rows pc cell guard n limit receive
    arm pollLast highLast branchInput misses high armOrdinary pollOrdinary highOrdinary endOrdinary branchOrdinary
    phase timer word installed ((congrArg BitVec.toNat position).trans boundary.position) (remaining.trans slot)
    history within highDuration qualified destination onBit branch forward inBounds
  exact ⟨verdict, branched⟩

end Pinwheel.Hardware.StreamingReady.SegmentStreamStep
