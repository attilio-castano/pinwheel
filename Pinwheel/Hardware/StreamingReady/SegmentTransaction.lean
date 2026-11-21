import Pinwheel.Hardware.StreamingReady.SegmentPathControl
import Pinwheel.Hardware.StreamingReady.SegmentPulseRefinement
import Pinwheel.Hardware.StreamingReady.SegmentWaitRefinement

/-! Composition of reached FETCH cuts for a checked segmented transaction.
The input trace is partitioned by the actual circuit. Local cell service
evidence accounts for the clocks delivered between consecutive FETCH cuts. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentTransaction

open Pinwheel.Hardware SegmentCore SegmentPathControl
open Pinwheel.Program.StreamingReadySegments
open Pinwheel.Program.StreamingReady (Cell Guard Instruction Pins)
open SegmentTiming (run)

structure Cut (registered : Bool) (rows : List Row) (cursor : Cursor)
    (capture : Option Bool) (s : Values (Register a)) : Prop where
  boundary : AtBoundary registered rows cursor.pc capture s
  qualified : cursor.capture = true → capture.isSome = true
  slots : ∀ slots, cursor.slots = some slots → (s (.base .remaining)).toNat = slots
  tx : (s (.base .txConsumed)).toNat = cursor.tx
  rx : (s (.base .rxProduced)).toNat = cursor.rx

/-- Every supplied edge runs in an active phase and preserves the owner. -/
inductive ActiveClocks (registered : Bool) :
    Values (Register a) → List (Values Core.Input) → Prop where
  | nil {s : Values (Register a)} : ActiveClocks registered s []
  | cons {s : Values (Register a)} {i : Values Core.Input} {rest : List (Values Core.Input)}
      (ordinary : NoReset i) (notFree : s (.base .phase) ≠ 0#3)
      (notComplete : s (.base .phase) ≠ 5#3) (notFault : s (.base .phase) ≠ 6#3)
      (tail : ActiveClocks registered ((circuit a registered).step i s) rest) :
      ActiveClocks registered s (i :: rest)

private theorem frame_trans {s middle after : Values (Register a)}
    (left : OwnerFrame s middle) (right : OwnerFrame middle after) :
    OwnerFrame s after :=
  ⟨right.generation.trans left.generation, right.transfer.trans left.transfer,
    right.total.trans left.total⟩

theorem ActiveClocks.owner (span : @ActiveClocks registered a s inputs) :
    OwnerFrame s (run registered s inputs) := by
  induction span with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons ordinary notFree notComplete notFault _ ih =>
    exact frame_trans (active_owner_frame registered _ _ ordinary notFree notComplete notFault) ih

theorem ActiveClocks.image (span : @ActiveClocks registered a s inputs) :
    Installed rows s → Installed rows (run registered s inputs) := by
  induction span with
  | nil => exact id
  | cons ordinary notFree _ _ _ ih =>
    exact fun installed => ih ((image_frame registered _ _ ordinary (.inl notFree)).installed installed)

theorem ActiveClocks.append (left : @ActiveClocks registered a s before)
    (right : ActiveClocks registered (run registered s before) after) :
    ActiveClocks registered s (before ++ after) := by
  induction left with
  | nil => exact right
  | cons ordinary notFree notComplete notFault _ ih =>
    exact .cons ordinary notFree notComplete notFault (ih right)

theorem ActiveClocks.of_prefixes (registered : Bool) (s : Values (Register a))
    (inputs : List (Values Core.Input)) (phase : BitVec 3)
    (notFree : phase ≠ 0#3) (notComplete : phase ≠ 5#3) (notFault : phase ≠ 6#3)
    (ordinary : ∀ i ∈ inputs, NoReset i)
    (prefixPhase : ∀ (before after : List (Values Core.Input)) (i : Values Core.Input),
      inputs = before ++ @i :: after → run registered s before (.base .phase) = phase) :
    ActiveClocks registered s inputs := by
  induction inputs generalizing s with
  | nil => exact .nil
  | cons i rest ih =>
    have start : s (.base .phase) = phase := prefixPhase [] rest i rfl
    apply ActiveClocks.cons (ordinary i (by simp))
      (start ▸ notFree) (start ▸ notComplete) (start ▸ notFault)
    apply ih
    · exact fun j hj => ordinary j (List.mem_cons_of_mem (α := Values Core.Input) i hj)
    · intro before after j split
      exact prefixPhase (@i :: before) after j (congrArg (List.cons (α := Values Core.Input) i) split)

private theorem drain_ordinary {i : Values Core.Input} (drain : ProtocolOwnership.DrainInput i) :
    NoReset i := ⟨drain.1, by simp [drain.2.1]⟩

inductive Serviced : Instruction → Prop where
  | pulse : Serviced (.pulse cell)
  | wait : Serviced (.driveWait pins g)
  | stream : Serviced (.stream cell g)

/-- A local service witness ends at the next actual FETCH, with the cell's
    slot/capture and TX/RX effects accounted for by the compiled successor.
    `inputs` are physical clocks. `following.coreClocks` is the checker's
    successful-path cost and is not a bound on unspecified service stalls. -/
structure ServiceSpan (registered : Bool) (rows : List Row) (following : Cursor)
    (capture : Option Bool) (s : Values (Register a)) (inputs : List (Values Core.Input)) : Prop where
  nonempty : inputs ≠ []
  active : ActiveClocks registered s inputs
  finish : Cut registered rows following capture (run registered s inputs)

def countCursor (cursor : Cursor) (slots : BitVec 16) : Cursor :=
  {cursor with
    pc := cursor.pc + 1
    slots := some slots.toNat
    capture := false
    coreClocks := cursor.coreClocks + 1}

def branchCursor (cursor : Cursor) (destination : BitVec 6) (taken : Bool) : Cursor :=
  {cursor with
    pc := if taken then destination.toNat else cursor.pc + 1
    capture := false
    coreClocks := cursor.coreClocks + 1}

def terminalRow : Exit → Row
  | .complete => .cell .halt
  | .discard => .discard
  | .fault => .cell .fault

def terminalPhase : Exit → BitVec 3
  | .complete | .discard => 5#3
  | .fault => 6#3

def endOf (cursor : Cursor) (exit : Exit) : PathEnd :=
  ⟨exit, cursor.tx, cursor.rx, cursor.coreClocks + 1⟩

/-- A delivered path contains the actual inputs for each instruction. COUNT and
    BRANCH take one edge. The BRANCH successor uses the qualified capture that
    indexes its entry cut. The only multiedge cases are serviced cells. -/
inductive Delivered (registered : Bool) (rows : List Row) (budget : Nat) :
    Cursor → Option Bool → Values (Register a) → List (Values Core.Input) → PathEnd → Prop where
  | count {s : Values (Register a)} {i : Values Core.Input}
      (row : rows[cursor.pc]? = some (.count slots)) (nonzero : slots ≠ 0#16)
      (ordinary : NoReset i)
      (entry : successors rows budget cursor = some (.next (countCursor cursor slots)))
      (tail : Delivered registered rows budget (countCursor cursor slots) none
        ((circuit a registered).step i s) rest result) :
      Delivered registered rows budget cursor capture s (i :: rest) result
  | branch {s : Values (Register a)} {i : Values Core.Input}
      (row : rows[cursor.pc]? = some (.branch destination onBit)) (ordinary : NoReset i)
      (forward : cursor.pc < destination.toNat) (inBounds : destination.toNat < rows.length)
      (entry : successors rows budget cursor =
        some (.both (branchCursor cursor destination false) (branchCursor cursor destination true)))
      (tail : Delivered registered rows budget (branchCursor cursor destination (decide (capture = onBit))) none
        ((circuit a registered).step i s) rest result) :
      Delivered registered rows budget cursor (some capture) s (i :: rest) result
  | cell {s : Values (Register a)} (kind : Serviced instruction) (row : rows[cursor.pc]? = some (.cell instruction))
      (entry : successors rows budget cursor = some (.next following))
      (service : Cut registered rows cursor capture s → ServiceSpan registered rows following sample s clocks)
      (tail : Delivered registered rows budget following sample (run registered s clocks) rest result) :
      Delivered registered rows budget cursor capture s (clocks ++ rest) result
  | finish {s : Values (Register a)} {i : Values Core.Input}
      (row : rows[cursor.pc]? = some (terminalRow exit)) (drain : ProtocolOwnership.DrainInput i)
      (entry : successors rows budget cursor = some (.finish (endOf cursor exit))) :
      Delivered registered rows budget cursor capture s [i] (endOf cursor exit)

structure RetainedEnd (result : PathEnd) (s : Values (Register a)) : Prop where
  phase : s (.base .phase) = terminalPhase result.exit
  tx : (s (.base .txConsumed)).toNat = result.tx
  rx : (s (.base .rxProduced)).toNat = result.rx

private theorem fetch_owner {s : Values (Register a)}
    (h : AtBoundary registered rows pc capture s) (i : Values Core.Input)
    (ordinary : NoReset i) : OwnerFrame s ((circuit a registered).step i s) :=
  active_owner_frame registered i s ordinary (by simp [h.phase]) (by simp [h.phase]) (by simp [h.phase])

private theorem step_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (reg : Core.Register a w) :
    (circuit a registered).step i s (.base reg) =
      (nextBase reg).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

private theorem inv_one_inv (value : BitVec 1) : ~~~(1#1 &&& ~~~value) = value :=
  by decide +revert +kernel

set_option linter.unusedSimpArgs false in
theorem fetch_counts {s : Values (Register a)}
    (h : AtBoundary registered rows pc capture s) (i : Values Core.Input)
    (ordinary : NoReset i) :
    let after : Values (Register a) := (circuit a registered).step i s
    after (.base .txConsumed) = s (.base .txConsumed) ∧
      after (.base .rxProduced) = s (.base .rxProduced) := by
  simp [step_base, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
    decodedRegister, withFetch, Expr.eval, lift, SegmentCore.discard, SegmentCore.control,
    setCount, branch, fetching, SegmentCore.both, SegmentCore.either, Core.next, Core.nextRaw,
    Core.cold, Core.warm, Core.resetting, Core.cmd, Core.both, Core.either, Core.free, Core.starting,
    Core.releasing, Core.retained, Core.hostOwner, Core.owned, Core.busy, Core.identity,
    Core.isPhase, Core.clearedRuntime, Core.capturingRX, Core.capture, Core.takingTX, Core.reserving,
    Core.lowEnd, Core.guardedLowEnd, Core.highEnd, Core.waitSuccess, Core.standaloneSuccess,
    Core.waitFault, ordinary.1, ordinary.2, h.phase, inv_one_inv]

private theorem active_step {s : Values (Register a)} {i : Values Core.Input}
    (ordinary : NoReset i) (phase : s (.base .phase) = tag)
    (active : tag = 1#3 ∨ tag = 2#3 ∨ tag = 3#3 ∨ tag = 4#3 ∨ tag = 7#3)
    (restActive : ActiveClocks registered ((circuit a registered).step i s) rest) :
    ActiveClocks registered s (@i :: rest) := by
  rcases active with h | h | h | h | h <;> exact .cons ordinary
    (by simp [phase, h]) (by simp [phase, h]) (by simp [phase, h]) restActive

private theorem prefix_le {α : Type} {span before after : List α} {last : α}
    (split : span = before ++ last :: after) : before.length ≤ span.length := by
  rw [split, List.length_append]
  omega

set_option linter.unusedSimpArgs false in
private theorem low_rx_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (phase : s (.base .phase) = 3#3) (pending : s (.base .countdown) ≠ 0#8) :
    ((circuit a registered).step i s) (.base .rxProduced) = s (.base .rxProduced) := by
  simp [step_base, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
    withFetch, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting, Core.cmd,
    Core.both, Core.either, Core.free, Core.starting, Core.releasing, Core.retained, Core.hostOwner,
    Core.owned, Core.busy, Core.identity, Core.isPhase, Core.clearedRuntime, Core.capturingRX,
    Core.capture, Core.lowEnd, Core.waitSuccess, ordinary.1, ordinary.2, phase, pending, inv_one_inv]

private theorem low_rx_prefix (registered : Bool) (s : Values (Register a))
    (holds : List (Values Core.Input)) (phase : s (.base .phase) = 3#3)
    (within : holds.length ≤ (s (.base .countdown)).toNat)
    (ordinary : ∀ i ∈ holds, ProtocolOwnership.DrainInput i) :
    run registered s holds (.base .rxProduced) = s (.base .rxProduced) := by
  induction holds generalizing s with
  | nil => rfl
  | cons i rest ih =>
    let nextState : Values (Register a) := (circuit a registered).step i s
    have positive : 0 < (s (.base .countdown)).toNat := by
      simp only [List.length_cons] at within
      omega
    have pending : s (.base .countdown) ≠ 0#8 := by
      intro zero
      simp [zero] at positive
    have input := ordinary i (by simp)
    have edge : SegmentStreamStep.LowSpan s nextState 1 :=
      SegmentStreamStep.low_span registered s [@i] phase positive (by simpa using input)
    have restWithin : rest.length ≤ (nextState (.base .countdown)).toNat := by
      rw [edge.countdown]
      simp only [List.length_cons] at within
      omega
    exact (ih nextState edge.phase restWithin
      (fun j hj => ordinary j (List.mem_cons_of_mem (α := Values Core.Input) i hj))).trans
      (low_rx_step registered i s (drain_ordinary input) phase pending)

private theorem successor_pulse {cursor following : Cursor} (row : rows[cursor.pc]? = some (.cell (.pulse cell)))
    (entry : successors rows budget cursor = some (.next following)) :
    following.pc = cursor.pc + 1 ∧ following.slots = none ∧ following.capture = cursor.capture ∧
      following.tx = cursor.tx ∧ following.rx = cursor.rx ∧
      following.coreClocks = cursor.coreClocks + (4 + cell.lowDuration.val + cell.highDuration.val) ∧
      (Instruction.pulse cell).Canonical := by
  simp [successors, row] at entry
  obtain ⟨valid, empty, rfl⟩ := entry
  refine ⟨rfl, empty, rfl, rfl, rfl, ?_, valid⟩
  change cursor.coreClocks + (1 + (1 + (cell.lowDuration.val + 1) + (cell.highDuration.val + 1))) = _
  omega

private theorem capture_exists (s : Values (Register a)) : ∃ bit, HasCapture s bit := by
  have bitCases (value : BitVec 1) : value = 0#1 ∨ value = 1#1 := by decide +revert +kernel
  rcases bitCases (s .captureValid) with absent | present
  · exact ⟨none, absent⟩
  · rcases bitCases (s .lastCapture) with low | high
    · exact ⟨some false, present, low⟩
    · exact ⟨some true, present, high⟩

/-- A serviced PULSE follows its encoded LOW and HIGH durations and preserves
    both accounting totals and the previous qualified capture. -/
theorem service_pulse (registered : Bool) (s : Values (Register a)) (cell : Cell)
    (cut : Cut registered rows cursor capture s) (row : rows[cursor.pc]? = some (.cell (.pulse cell)))
    (checked : successors rows budget cursor = some (.next following))
    (entry reserveInput rise fall : Values Core.Input) (lowHolds highHolds : List (Values Core.Input))
    (entryOrdinary : NoReset entry) (reserveOrdinary : NoReset reserveInput)
    (riseOrdinary : NoReset rise) (fallOrdinary : NoReset fall)
    (lowOrdinary : ∀ i ∈ lowHolds, ProtocolOwnership.DrainInput i)
    (highOrdinary : ∀ i ∈ highHolds, NoReset i)
    (lowDuration : lowHolds.length = cell.lowDuration.val)
    (highDuration : highHolds.length = cell.highDuration.val) :
    ServiceSpan registered rows following capture s
      (@entry :: @reserveInput :: (lowHolds ++ @rise :: (highHolds ++ [@fall]))) := by
  obtain ⟨nextPC, nextSlots, nextCapture, nextTX, nextRX, _, canonical⟩ := successor_pulse row checked
  let loaded : Values (Register a) := (circuit a registered).step entry s
  let reserved : Values (Register a) := (circuit a registered).step reserveInput loaded
  let low : Values (Register a) := run registered reserved lowHolds
  let high : Values (Register a) := (circuit a registered).step rise low
  obtain ⟨load, reserve, lowSpan, riseEdge, boundary⟩ :=
    SegmentPulseRefinement.run_pulse_row registered s cell cut.boundary row canonical entry reserveInput rise fall
      lowHolds highHolds entryOrdinary reserveOrdinary riseOrdinary fallOrdinary lowOrdinary highOrdinary
      lowDuration highDuration
  have lows : lowHolds.length ≤ (reserved (.base .countdown)).toNat := by
    have delay : reserved (.base .countdown) = BitVec.ofNat 8 cell.lowDuration.val := reserve.countdown
    rw [delay, lowDuration, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cell.lowDuration.isLt]
    exact Nat.le_refl _
  have highs : highHolds.length = (high (.base .countdown)).toNat := by
    have delay : high (.base .countdown) = BitVec.ofNat 8 cell.highDuration.val := riseEdge.countdown
    rw [delay, highDuration, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cell.highDuration.isLt]
  have lowActive : ActiveClocks registered reserved lowHolds := by
    apply ActiveClocks.of_prefixes registered reserved lowHolds 3#3 (by decide) (by decide) (by decide)
      (fun i member => drain_ordinary (lowOrdinary i member))
    intro before after i split
    exact (SegmentStreamStep.low_span registered reserved before reserve.phase
      (Nat.le_trans (prefix_le split) lows) (fun j member => lowOrdinary j
        (split ▸ List.mem_append_left (α := Values Core.Input) (@i :: after) member))).phase
  obtain ⟨_, highCapture⟩ := capture_exists high
  have highSpan := high_prefix registered high highHolds highOrdinary riseEdge.phase (Nat.le_of_eq highs) highCapture
  have highActive : ActiveClocks registered high highHolds := by
    apply ActiveClocks.of_prefixes registered high highHolds 4#3 (by decide) (by decide) (by decide) highOrdinary
    intro before after i split
    exact (high_prefix registered high before (fun j member => highOrdinary j
      (split ▸ List.mem_append_left (α := Values Core.Input) (@i :: after) member)) riseEdge.phase
      (Nat.le_trans (prefix_le split) (Nat.le_of_eq highs)) highCapture).phase
  have activity := active_step entryOrdinary cut.boundary.phase (.inl rfl)
    (active_step reserveOrdinary load.phase (.inr (.inl rfl))
      (lowActive.append (active_step riseOrdinary lowSpan.phase (.inr (.inr (.inl rfl)))
        (highActive.append (active_step fallOrdinary highSpan.phase (.inr (.inr (.inr (.inl rfl)))) .nil)))))
  have fallEdge := high_step registered fall (run registered high highHolds) fallOrdinary highSpan.phase
  have entryCounts := fetch_counts cut.boundary entry entryOrdinary
  have consumed := fallEdge.reserved.trans (highSpan.reserved.trans (riseEdge.reserved.trans
    (lowSpan.reserved.trans (reserve.reserved.trans entryCounts.1))))
  have produced := fallEdge.produced.trans (highSpan.produced.trans (riseEdge.produced.trans
    ((low_rx_prefix registered reserved lowHolds reserve.phase lows lowOrdinary).trans
      (reserve.produced.trans entryCounts.2))))
  refine ⟨by simp, activity, ?_⟩
  change Cut registered rows following capture (run registered reserved (lowHolds ++ @rise :: (highHolds ++ [@fall])))
  rw [SegmentTiming.run_append]
  change Cut registered rows following capture (run registered high (highHolds ++ [@fall]))
  refine ⟨nextPC ▸ boundary, fun active => cut.qualified (nextCapture ▸ active), by simp [nextSlots], ?_, ?_⟩
  · rw [SegmentTiming.run_append]
    exact (congrArg BitVec.toNat consumed).trans (cut.tx.trans nextTX.symm)
  · rw [SegmentTiming.run_append]
    exact (congrArg BitVec.toNat produced).trans (cut.rx.trans nextRX.symm)

theorem pulse_clocks (row : rows[cursor.pc]? = some (.cell (.pulse cell)))
    (checked : successors rows budget cursor = some (.next following))
    {entry reserveInput rise fall : Values Core.Input} {lowHolds highHolds : List (Values Core.Input)}
    (lowDuration : lowHolds.length = cell.lowDuration.val)
    (highDuration : highHolds.length = cell.highDuration.val) :
    following.coreClocks = cursor.coreClocks +
      (List.cons (α := Values Core.Input) entry
        (@reserveInput :: (lowHolds ++ @rise :: (highHolds ++ [@fall])))).length := by
  rw [(successor_pulse row checked).2.2.2.2.2.1]
  simp only [List.length_cons, List.length_append, List.length_nil, lowDuration, highDuration]
  omega

set_option linter.unusedSimpArgs false in
private theorem wait_tx_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (phase : s (.base .phase) = 7#3) :
    ((circuit a registered).step i s) (.base .txConsumed) = s (.base .txConsumed) := by
  simp [step_base, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
    withFetch, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting, Core.cmd,
    Core.both, Core.either, Core.free, Core.starting, Core.releasing, Core.retained, Core.hostOwner,
    Core.owned, Core.busy, Core.identity, Core.isPhase, Core.clearedRuntime, Core.takingTX,
    Core.reserving, ordinary.1, ordinary.2, phase, inv_one_inv]

theorem wait_prefix (registered : Bool) (s : Values (Register a))
    (misses : List (Values Core.Input)) (phase : s (.base .phase) = 7#3)
    (bounded : SegmentTiming.guardBudget s ≠ 0#8) (history : SegmentTiming.MissHistory registered s misses)
    (within : misses.length ≤ (s (.base .countdown)).toNat) :
    ActiveClocks registered s misses ∧ run registered s misses (.base .txConsumed) = s (.base .txConsumed) := by
  induction misses generalizing s with
  | nil => exact ⟨.nil, rfl⟩
  | cons i rest ih =>
    obtain ⟨input, miss, tail⟩ := history
    let nextState : Values (Register a) := (circuit a registered).step i s
    have positive : 0 < (s (.base .countdown)).toNat := by
      simp only [List.length_cons] at within
      omega
    have edge : SegmentTiming.MissCut s nextState 1 :=
      SegmentTiming.miss_prefix registered s [@i] phase bounded ⟨input, miss, trivial⟩ positive
    have nextBudget : SegmentTiming.guardBudget nextState ≠ 0#8 := by
      change (nextState (.base .currentWord)).extractLsb' 54 8 ≠ 0#8
      rw [edge.pose.current]
      exact bounded
    have nextWithin : rest.length ≤ (nextState (.base .countdown)).toNat := by
      rw [edge.countdown]
      simp only [List.length_cons] at within
      omega
    obtain ⟨active, count⟩ := ih nextState edge.phase nextBudget tail nextWithin
    exact ⟨active_step (drain_ordinary input) phase (.inr (.inr (.inr (.inr rfl)))) active,
      count.trans (wait_tx_step registered i s (drain_ordinary input) phase)⟩

theorem successor_wait (row : rows[cursor.pc]? = some (.cell (.driveWait pins g)))
    (entry : successors rows budget cursor = some (.next following))
    (limit : g.limit = .misses n) :
    following.pc = cursor.pc + 1 ∧ following.slots = none ∧ following.capture = cursor.capture ∧
      following.tx = cursor.tx ∧ following.rx = cursor.rx ∧
      following.coreClocks = cursor.coreClocks + (1 + (n.val + 1)) ∧
      (Instruction.driveWait pins g).Canonical := by
  simp [successors, row] at entry
  obtain ⟨canonical, advance⟩ := entry
  rw [limit] at advance
  change (if cursor.slots = none then some (Successors.next
    {cursor with pc := cursor.pc + 1, coreClocks := cursor.coreClocks + (1 + (n.val + 1))}) else none) =
      some (.next following) at advance
  simp at advance
  obtain ⟨empty, rfl⟩ := advance
  exact ⟨rfl, empty, rfl, rfl, rfl, rfl, canonical⟩

/-- A timely bounded DRIVE_WAIT reaches the next FETCH with the previous
    capture and accounting. The external inputs establish the miss history
    and the final sample that qualifies the guard. -/
theorem service_wait (registered : Bool) (s : Values (Register a)) (pins : Pins) (g : Guard) (n : Fin 255)
    (cut : Cut registered rows cursor capture s)
    (row : rows[cursor.pc]? = some (.cell (.driveWait pins g)))
    (checked : successors rows budget cursor = some (.next following))
    (entry last : Values Core.Input) (misses : List (Values Core.Input))
    (entryOrdinary : NoReset entry) (lastOrdinary : ProtocolOwnership.DrainInput last)
    (limit : g.limit = .misses n) (within : misses.length ≤ n.val)
    (history : SegmentTiming.MissHistory registered ((circuit a registered).step entry s) misses)
    (ready : g.matches (run registered ((circuit a registered).step entry s) misses (.base .stage2)) = true) :
    ServiceSpan registered rows following capture s (@entry :: (misses ++ [@last])) := by
  obtain ⟨nextPC, nextSlots, nextCapture, nextTX, nextRX, _, canonical⟩ := successor_wait row checked limit
  let loaded : Values (Register a) := (circuit a registered).step entry s
  let poll : Values (Register a) := run registered loaded misses
  let after : Values (Register a) := (circuit a registered).step last poll
  have rowInBounds := (List.getElem?_eq_some_iff.mp row).1
  have fetch : SegmentControl.AtFetch entry s :=
    ⟨entryOrdinary.1, entryOrdinary.2, cut.boundary.phase, by
      rw [cut.boundary.position, cut.boundary.installed.count]
      exact rowInBounds⟩
  obtain ⟨loadedWait, window⟩ := SegmentWaitRefinement.run_wait_row registered s entry last misses fetch
    pins g n canonical (selected_row cut.boundary entry row) limit history within lastOrdinary
  have qualified := window.qualified ready
  change SegmentWaitRefinement.WaitSuccess loaded (run registered loaded (misses ++ [@last])) at qualified
  rw [SegmentTiming.run_append] at qualified
  have bounded : SegmentTiming.guardBudget loaded ≠ 0#8 := by
    have current : loaded (.base .currentWord) = _ := loadedWait.current
    rw [SegmentTiming.guardBudget, current, (Pinwheel.Program.StreamingReady.encode_fields (.driveWait pins g)).guardBudget]
    change g.limit.budget ≠ 0#8
    rw [limit]
    exact SourceRefinement.budget_nonzero n
  have admissible : misses.length ≤ (loaded (.base .countdown)).toNat := by
    have delay : loaded (.base .countdown) = g.limit.initialCountdown := loadedWait.countdown
    rw [delay, limit]
    simpa only [Pinwheel.Program.StreamingReady.WaitLimit.initialCountdown, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show n.val < 256 by omega)] using within
  obtain ⟨missActive, counts⟩ := wait_prefix registered loaded misses loadedWait.phase bounded history admissible
  have localActive := missActive.append
    (active_step (drain_ordinary lastOrdinary) window.waitingPrefix.phase (.inr (.inr (.inr (.inr rfl)))) .nil)
  have activity := active_step entryOrdinary cut.boundary.phase (.inl rfl) localActive
  have installed := activity.image cut.boundary.installed
  have entryCounts := fetch_counts cut.boundary entry entryOrdinary
  have counted := (wait_tx_step registered last poll (drain_ordinary lastOrdinary)
    window.waitingPrefix.phase).trans (counts.trans entryCounts.1)
  have pc : (after (.base .pc)).toNat = following.pc := by
    have advanced : after (.base .pc) = loaded (.base .pc) + 1#7 := qualified.pc
    have loadedPC : loaded (.base .pc) = s (.base .pc) := loadedWait.pc
    rw [advanced, loadedPC, BitVec.toNat_add, cut.boundary.position, nextPC]
    change (cursor.pc + 1) % 128 = cursor.pc + 1
    exact Nat.mod_eq_of_lt (by have := cut.boundary.installed.size; omega)
  have prior := cut.boundary.latched
  have held : HasCapture after capture := by
    have sample : after .lastCapture = s .lastCapture := qualified.latched.trans loadedWait.latched
    have valid : after .captureValid = s .captureValid := qualified.valid.trans loadedWait.valid
    cases capture <;> simpa only [HasCapture, sample, valid] using prior
  refine ⟨by simp, activity, ?_⟩
  change Cut registered rows following capture (run registered loaded (misses ++ [@last]))
  rw [SegmentTiming.run_append]
  refine ⟨⟨?_, qualified.phase, pc, held, ?_⟩, fun active => cut.qualified (nextCapture ▸ active),
    by simp [nextSlots], (congrArg BitVec.toNat counted).trans (cut.tx.trans nextTX.symm), ?_⟩
  · change Installed rows after
    change Installed rows (run registered loaded (misses ++ [@last])) at installed
    rw [SegmentTiming.run_append] at installed
    exact installed
  · intro cached
    subst registered
    exact SegmentStore.coherent_after_edge last poll
  · exact (congrArg BitVec.toNat (qualified.captured.trans entryCounts.2)).trans (cut.rx.trans nextRX.symm)

theorem wait_clock_bound (row : rows[cursor.pc]? = some (.cell (.driveWait pins g)))
    (checked : successors rows budget cursor = some (.next following))
    (limit : g.limit = .misses n) {entry last : Values Core.Input} {misses : List (Values Core.Input)}
    (within : misses.length ≤ n.val) :
    cursor.coreClocks + (List.cons (α := Values Core.Input) entry (misses ++ [@last])).length ≤
      following.coreClocks := by
  rw [(successor_wait row checked limit).2.2.2.2.2.1]
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

theorem terminal_end {s : Values (Register a)}
    (h : Cut registered rows cursor capture s) (i : Values Core.Input)
    (drain : ProtocolOwnership.DrainInput i) (row : rows[cursor.pc]? = some (terminalRow exit)) :
    RetainedEnd (endOf cursor exit) ((circuit a registered).step i s) := by
  have ordinary : NoReset i := ⟨drain.1, by simp [drain.2.1]⟩
  have counts := fetch_counts h.boundary i ordinary
  have phase : ((circuit a registered).step i s) (.base .phase) = terminalPhase exit := by
    cases exit with
    | complete =>
      exact congrArg ProtocolOwnership.TerminalCut.phase
        (terminal_step h.boundary i drain false row).1
    | discard => exact (discard_step h.boundary i ordinary row).completed
    | fault =>
      exact congrArg ProtocolOwnership.TerminalCut.phase
        (terminal_step h.boundary i drain true row).1
  exact ⟨phase, (congrArg BitVec.toNat counts.1).trans h.tx,
    (congrArg BitVec.toNat counts.2).trans h.rx⟩

/-- COUNT realizes the next checked cut and resets the branch latch. -/
theorem count_cut {s : Values (Register a)} (cut : Cut registered rows cursor capture s)
    (i : Values Core.Input) (ordinary : NoReset i)
    (row : rows[cursor.pc]? = some (.count slots)) (nonzero : slots ≠ 0#16) :
    Cut registered rows (countCursor cursor slots) none ((circuit a registered).step i s) := by
  obtain ⟨boundary, armed⟩ := count_step cut.boundary i ordinary row nonzero
  have counts := fetch_counts cut.boundary i ordinary
  exact ⟨boundary, by simp [countCursor], by simp [countCursor, armed],
    (congrArg BitVec.toNat counts.1).trans cut.tx, (congrArg BitVec.toNat counts.2).trans cut.rx⟩

/-- BRANCH uses the actual sampled bit and clears its qualification on exit. -/
theorem branch_cut {s : Values (Register a)} (cut : Cut registered rows cursor (some capture) s)
    (i : Values Core.Input) (ordinary : NoReset i)
    (row : rows[cursor.pc]? = some (.branch destination onBit)) (forward : cursor.pc < destination.toNat)
    (inBounds : destination.toNat < rows.length)
    (entry : successors rows budget cursor =
      some (.both (branchCursor cursor destination false) (branchCursor cursor destination true))) :
    Cut registered rows (branchCursor cursor destination (decide (capture = onBit))) none
      ((circuit a registered).step i s) := by
  have boundary := branch_step cut.boundary i ordinary row forward inBounds
  have counts := fetch_counts cut.boundary i ordinary
  have emptySlots : cursor.slots = none := by
    simp only [successors, row] at entry
    split at entry <;> simp_all
  exact ⟨by simpa [branchCursor] using boundary, by simp [branchCursor], by simp [branchCursor, emptySlots],
    (congrArg BitVec.toNat counts.1).trans cut.tx, (congrArg BitVec.toNat counts.2).trans cut.rx⟩

/-- One checked instruction that returns to FETCH. Its proof obligations refer
    only to the clocks for that instruction. -/
inductive Advance (registered : Bool) (rows : List Row) (budget : Nat) :
    Cursor → Option Bool → Values (Register a) → List (Values Core.Input) → Cursor → Option Bool → Prop where
  | count {s : Values (Register a)} {i : Values Core.Input}
      (row : rows[cursor.pc]? = some (.count slots)) (nonzero : slots ≠ 0#16)
      (ordinary : NoReset i)
      (entry : successors rows budget cursor = some (.next (countCursor cursor slots))) :
      Advance registered rows budget cursor capture s [i] (countCursor cursor slots) none
  | branch {s : Values (Register a)} {i : Values Core.Input}
      (row : rows[cursor.pc]? = some (.branch destination onBit)) (ordinary : NoReset i)
      (forward : cursor.pc < destination.toNat) (inBounds : destination.toNat < rows.length)
      (entry : successors rows budget cursor =
        some (.both (branchCursor cursor destination false) (branchCursor cursor destination true))) :
      Advance registered rows budget cursor (some capture) s [i]
        (branchCursor cursor destination (decide (capture = onBit))) none
  | cell {s : Values (Register a)} (kind : Serviced instruction) (row : rows[cursor.pc]? = some (.cell instruction))
      (entry : successors rows budget cursor = some (.next following))
      (service : Cut registered rows cursor capture s → ServiceSpan registered rows following sample s clocks) :
      Advance registered rows budget cursor capture s clocks following sample

theorem Advance.refines (step : @Advance registered rows budget a cursor capture s inputs following sample)
    (cut : Cut registered rows cursor capture s) :
    Cut registered rows following sample (run registered s inputs) ∧ ActiveClocks registered s inputs := by
  cases step with
  | count row nonzero ordinary _ =>
    exact ⟨count_cut cut _ ordinary row nonzero, active_step ordinary cut.boundary.phase (.inl rfl) .nil⟩
  | branch row ordinary forward inBounds entry =>
    exact ⟨branch_cut cut _ ordinary row forward inBounds entry,
      active_step ordinary cut.boundary.phase (.inl rfl) .nil⟩
  | cell _ _ _ service =>
    exact ⟨(service cut).finish, (service cut).active⟩

/-- A finite checked prefix may end before a dynamic guard expires. -/
inductive Prefix (registered : Bool) (rows : List Row) (budget : Nat) :
    Cursor → Option Bool → Values (Register a) → List (Values Core.Input) → Cursor → Option Bool → Prop where
  | nil {s : Values (Register a)} : Prefix registered rows budget cursor capture s [] cursor capture
  | next {s : Values (Register a)}
      (head : Advance registered rows budget cursor capture s clocks middle bit)
      (tail : Prefix registered rows budget middle bit (run registered s clocks) rest following sample) :
      Prefix registered rows budget cursor capture s (clocks ++ rest) following sample

theorem Prefix.refines (walk : @Prefix registered rows budget a cursor capture s inputs following sample)
    (cut : Cut registered rows cursor capture s) :
    Cut registered rows following sample (run registered s inputs) ∧ ActiveClocks registered s inputs := by
  induction walk with
  | nil => exact ⟨cut, .nil⟩
  | next head _ ih =>
    obtain ⟨nextCut, headActive⟩ := head.refines cut
    obtain ⟨finalCut, tailActive⟩ := ih nextCut
    rw [SegmentTiming.run_append]
    exact ⟨finalCut, headActive.append tailActive⟩

/-- The checked abstract path and retained endpoint describe the same actual
    sequence of circuit steps, under the supplied local service witnesses. -/
theorem Delivered.refines (delivered : @Delivered registered rows budget a cursor capture s inputs result)
    (cut : Cut registered rows cursor capture s) :
    Reaches rows budget cursor result ∧ RetainedEnd result (run registered s inputs) ∧
      OwnerFrame s (run registered s inputs) := by
  induction delivered with
  | @count slots cursor _ _ _ _ _ row nonzero ordinary entry _ ih =>
    obtain ⟨reached, ending, owner⟩ := ih (count_cut cut _ ordinary row nonzero)
    exact ⟨.next entry reached, ending, frame_trans (fetch_owner cut.boundary _ ordinary) owner⟩
  | @branch cursor destination capture onBit _ result _ _ row ordinary forward inBounds entry _ ih =>
    obtain ⟨reached, ending, owner⟩ := ih (branch_cut cut _ ordinary row forward inBounds entry)
    have continued : Reaches rows budget
        (if decide (capture = onBit) then branchCursor cursor destination true
          else branchCursor cursor destination false) result := by
      by_cases chosen : capture = onBit <;> simpa [chosen] using reached
    exact ⟨.branch entry (decide (capture = onBit)) continued, ending,
      frame_trans (fetch_owner cut.boundary _ ordinary) owner⟩
  | cell _ _ entry service _ ih =>
    have serviced := service cut
    obtain ⟨reached, ending, owner⟩ := ih serviced.finish
    rw [SegmentTiming.run_append]
    exact ⟨.next entry reached, ending, frame_trans serviced.active.owner owner⟩
  | finish row drain entry =>
    exact ⟨.finish entry, terminal_end cut _ drain row,
      fetch_owner cut.boundary _ ⟨drain.1, by simp [drain.2.1]⟩⟩

/-- An admitted START creates the initial cursor and a fresh retained owner
    for the checked transaction endpoint. -/
theorem from_start (image : Image rows budget) (registered : Bool) (s : Values (Register a))
    (start : Values Core.Input) (installed : Installed rows s)
    (admitted : Core.starting.eval start (project s) = 1#1)
    (delivered : Delivered registered rows budget {} none ((circuit a registered).step start s) inputs result) :
    let after : Values (Register a) := run registered s (start :: inputs)
    result ∈ image.outcomes ∧ RetainedEnd result after ∧
      after (.base .generation) = s (.base .generation) ∧
      after (.base .transfer) = s (.base .transfer) + 1 ∧ after (.base .total) = start .startCount := by
  obtain ⟨boundary, generation, transfer, total, _, _, tx, rx⟩ :=
    start_at_boundary registered start s installed admitted
  have initial : Cut registered rows {} none ((circuit a registered).step start s) :=
    ⟨boundary, by simp, by simp, by simp [tx], by simp [rx]⟩
  obtain ⟨reached, ending, owner⟩ := delivered.refines initial
  exact ⟨image.covers reached, ending, owner.generation.trans generation,
    owner.transfer.trans transfer, owner.total.trans total⟩

end Pinwheel.Hardware.StreamingReady.SegmentTransaction
