import Pinwheel.Hardware.StreamingReady.SegmentControl
import Pinwheel.Hardware.StreamingReady.SegmentStore
import Pinwheel.Hardware.StreamingReady.SegmentTiming

/-! Checked instruction boundaries of the segmented core. The installed words
justify each fetch, and a branch consumes the bit latched by the circuit. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentPathControl

open Pinwheel.Hardware SegmentCore
open Pinwheel.Program.StreamingReadySegments (Row)

structure Installed (rows : List Row) (s : Values (Register a)) : Prop where
  size : rows.length ≤ 64
  count : (s (.base .count)).toNat = rows.length
  valid : s (.base .valid) = 1#1
  word : ∀ (atIndex : Fin rows.length),
    s (.base (.word (BitVec.ofNat 6 atIndex.val))) = rows[atIndex].encode

def NoReset (i : Values Core.Input) : Prop :=
  i .initialize = 0#1 ∧ i .command ≠ 15#4

def HasCapture (s : Values (Register a)) : Option Bool → Prop
  | none => s .captureValid = 0#1
  | some bit => s .captureValid = 1#1 ∧ s .lastCapture = BitVec.ofBool bit

structure AtBoundary (registered : Bool) (rows : List Row) (pc : Nat)
    (capture : Option Bool) (s : Values (Register a)) : Prop where
  installed : Installed rows s
  phase : s (.base .phase) = 1#3
  position : (s (.base .pc)).toNat = pc
  latched : HasCapture s capture
  coherent : registered = true → SegmentStore.Coherent s

private theorem boundary_fetch (h : AtBoundary registered rows pc capture s) (i : Values Core.Input)
    (runtime : NoReset i) (row : rows[pc]? = some instr) : SegmentControl.AtFetch i s := by
  refine ⟨runtime.1, runtime.2, h.phase, ?_⟩
  rw [h.position, h.installed.count]
  exact List.getElem?_eq_some_iff.mp row |>.1

theorem selected_row (h : AtBoundary registered rows pc capture s) (i : Values Core.Input)
    (row : rows[pc]? = some instr) : (word registered).eval i s = instr.encode := by
  have existsRow := List.getElem?_eq_some_iff.mp row
  have addressEq : (s (.base .pc)).extractLsb' 0 6 = BitVec.ofNat 6 pc := by
    apply BitVec.eq_of_toNat_eq
    simp [h.position]
  have installed := h.installed.word ⟨pc, existsRow.1⟩
  change s (.base (.word (BitVec.ofNat 6 pc))) = (rows[pc]'existsRow.1).encode at installed
  rw [existsRow.2] at installed
  have fetched : (word registered).eval i s = s (.base (.word ((s (.base .pc)).extractLsb' 0 6))) := by
    cases registered with
    | false =>
      simp only [word, Bool.false_eq_true, if_false, lift, Expr.eval_bind, Core.entryWord,
        Execution.readTree_correct, Expr.eval]
    | true => exact h.coherent rfl
  rw [fetched, addressEq]
  exact installed

private theorem step_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (reg : Core.Register a w) :
    (circuit a registered).step i s (.base reg) =
      (nextBase reg).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

structure ImageFrame (s after : Values (Register a)) : Prop where
  count : after (.base .count) = s (.base .count)
  valid : after (.base .valid) = s (.base .valid)
  word : ∀ address, after (.base (.word address)) = s (.base (.word address))
  generation : after (.base .generation) = s (.base .generation)

theorem ImageFrame.installed (same : ImageFrame s after) (old : Installed rows s) :
    Installed rows after :=
  ⟨old.size, congrArg BitVec.toNat same.count |>.trans old.count, same.valid.trans old.valid,
    fun atIndex => (same.word _).trans (old.word atIndex)⟩

set_option linter.unusedSimpArgs false in
/-- The instruction store and generation survive an ordinary active edge
    or a free-owner edge that sends neither WRITE nor COMMIT. -/
theorem image_frame (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i)
    (noProgramming : s (.base .phase) ≠ 0#3 ∨ (i .command ≠ 1#4 ∧ i .command ≠ 2#4)) :
    ImageFrame s ((circuit a registered).step i s) := by
  rcases noProgramming with busy | ⟨noWrite, noCommit⟩
  · refine ⟨?_, ?_, fun address => ?_, ?_⟩ <;>
      simp [step_base, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
        withFetch, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting,
        Core.cmd, Core.both, Core.either, Core.free, Core.writing, Core.committing,
        ordinary.1, ordinary.2, busy]
  · refine ⟨?_, ?_, fun address => ?_, ?_⟩ <;>
      simp [step_base, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
        withFetch, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting,
        Core.cmd, Core.both, Core.either, Core.free, Core.writing, Core.committing,
        ordinary.1, ordinary.2, noWrite, noCommit]

private theorem reader_coherent (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    registered = true → SegmentStore.Coherent ((circuit a registered).step i s) := by
  intro cached
  subst registered
  exact SegmentStore.coherent_after_edge i s

private theorem and_one (left right : BitVec 1) : (left &&& right = 1#1) ↔ left = 1#1 ∧ right = 1#1 :=
  by decide +revert +kernel

private theorem inv_one (value : BitVec 1) : (~~~value = 1#1) ↔ value = 0#1 :=
  by decide +revert +kernel

private theorem inv_one_inv (value : BitVec 1) : ~~~(1#1 &&& ~~~value) = value :=
  by decide +revert +kernel

private theorem one_and_one (value : BitVec 1) : 1#1 &&& value = value :=
  by decide +revert +kernel

private theorem start_flags (i : Values Core.Input) (s : Values (Register a))
    (admission : Core.starting.eval i (project s) = 1#1) :
    NoReset i ∧ i .command = 3#4 ∧ s (.base .phase) = 0#3 := by
  simp [Core.starting, Core.free, Core.resetting, Core.either, Core.both,
    Core.warm, Core.cold, Core.cmd, Expr.eval, project, and_one, inv_one] at admission
  have command : i .command = 3#4 := of_decide_eq_true admission.2.1
  exact ⟨⟨admission.1.1.1, by simp [command]⟩, command, of_decide_eq_true admission.1.2⟩
  done

private theorem step_captureValid (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .captureValid =
      (next .captureValid).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

set_option linter.unusedSimpArgs false in
/-- A START accepted by the real segmented core reaches the first encoded
    row with a fresh owner and without a branch capture. -/
theorem start_at_boundary (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (installed : Installed rows s) (admission : Core.starting.eval i (project s) = 1#1) :
    let after : Values (Register a) := (circuit a registered).step i s
    AtBoundary registered rows 0 none after ∧
      after (.base .generation) = s (.base .generation) ∧
      after (.base .transfer) = s (.base .transfer) + 1 ∧
      after (.base .total) = i .startCount ∧ after (.base .remaining) = i .startCount ∧
      after (.base .txAccepted) = 0#16 ∧ after (.base .txConsumed) = 0#16 ∧
      after (.base .rxProduced) = 0#16 := by
  obtain ⟨ordinary, command, free⟩ := start_flags i s admission
  have image := image_frame registered i s ordinary (Or.inr ⟨by simp [command], by simp [command]⟩)
  simp [Core.starting, Core.free, Core.space, Core.cold, Core.warm, Core.resetting,
    Core.cmd, Core.both, Core.either, Expr.eval, project, ordinary.1, command, free, one_and_one] at admission
  have allowed : s (.base .transfer) ≠ 65535#16 ∧ i .expectedGeneration = s (.base .generation) := by
    have bits := (and_one _ _).mp admission |>.2
    simp at bits
    exact ⟨of_decide_eq_false bits.1, of_decide_eq_true bits.2⟩
  refine ⟨⟨image.installed installed, ?_, ?_, ?_, reader_coherent registered i s⟩,
    image.generation, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [step_base, step_captureValid, HasCapture, next, nextBase, originalNext, Expr.eval_bind,
      usesEntryWord, decodedRegister, runtimeInput, lift, withFetch, project, Expr.eval,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, both, either,
      Core.next, Core.nextRaw, Core.fetching, Core.isPhase, Core.clearedRuntime,
      Core.releasing, Core.retained, Core.hostOwner, Core.owned, Core.busy, Core.identity,
      Core.cold, Core.warm, Core.resetting, Core.cmd, Core.both, Core.either, Core.inc,
      Core.starting, Core.free, Core.space, ordinary.1, command, free, installed.valid,
      allowed.1, allowed.2, inv_one_inv, one_and_one]
  rw [BitVec.sub_eq_add_neg]
  rfl

private theorem advance_pc (s : Values (Register a)) (old : (s (.base .pc)).toNat = pc)
    (bound : pc < 64) : (s (.base .pc) + 1).toNat = pc + 1 := by
  rw [BitVec.toNat_add, old]
  change (pc + 1) % 128 = pc + 1
  exact Nat.mod_eq_of_lt (by omega)

/-- The checked count advances the actual PC and arms precisely the
    declared number of slots, clearing any capture from the previous row. -/
theorem count_step {s : Values (Register a)} (h : AtBoundary registered rows pc capture s) (i : Values Core.Input)
    (runtime : NoReset i) (row : rows[pc]? = some (.count slots)) (nonzero : slots ≠ 0#16) :
    let after : Values (Register a) := (circuit a registered).step i s
    AtBoundary registered rows (pc + 1) none after ∧ after (.base .remaining) = slots := by
  have fetch := boundary_fetch h i runtime row
  have loaded := selected_row h i row
  have frame := image_frame registered i s runtime (.inl (by simp [h.phase]))
  obtain ⟨position, remaining, phase, valid⟩ := SegmentControl.set_count registered i s fetch slots nonzero loaded
  have bound : pc < 64 := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp row |>.1) h.installed.size
  refine ⟨⟨frame.installed h.installed, phase, ?_, valid, reader_coherent registered i s⟩, remaining⟩
  exact (congrArg BitVec.toNat position).trans (advance_pc s h.position bound)

/-- The encoded branch selects its successor using the certified capture
    carried from the prior row. A fetch after the branch has no valid capture. -/
theorem branch_step {s : Values (Register a)} (h : AtBoundary registered rows pc (some captured) s)
    (i : Values Core.Input)
    (runtime : NoReset i) (row : rows[pc]? = some (.branch destination onBit))
    (forward : pc < destination.toNat) (inBounds : destination.toNat < rows.length) :
    let after : Values (Register a) := (circuit a registered).step i s
    AtBoundary registered rows (if captured = onBit then destination.toNat else pc + 1) none after := by
  have fetch := boundary_fetch h i runtime row
  have loaded := selected_row h i row
  have frame := image_frame registered i s runtime (.inl (by simp [h.phase]))
  obtain ⟨valid, sample⟩ := h.latched
  obtain ⟨position, phase, noCapture⟩ := SegmentControl.take_branch registered i s fetch destination
    onBit (h.position ▸ forward) (h.installed.count ▸ inBounds) valid loaded
  have bound : pc < 64 := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp row |>.1) h.installed.size
  refine ⟨frame.installed h.installed, phase, ?_, noCapture, reader_coherent registered i s⟩
  change s .lastCapture = BitVec.ofBool captured at sample
  rw [position, sample]
  by_cases taken : captured = onBit
  · subst onBit
    simp only [if_true]
    rw [BitVec.toNat_append]
    simp
  · have different : BitVec.ofBool captured ≠ BitVec.ofBool onBit := by
      cases captured <;> cases onBit <;> simp_all
    rw [if_neg different, if_neg taken]
    exact advance_pc s h.position bound

structure OwnerFrame (s after : Values (Register a)) : Prop where
  generation : after (.base .generation) = s (.base .generation)
  transfer : after (.base .transfer) = s (.base .transfer)
  total : after (.base .total) = s (.base .total)

set_option linter.unusedSimpArgs false in
theorem active_owner_frame (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (notFree : s (.base .phase) ≠ 0#3)
    (notComplete : s (.base .phase) ≠ 5#3) (notFault : s (.base .phase) ≠ 6#3) :
    OwnerFrame s ((circuit a registered).step i s) := by
  refine ⟨(image_frame registered i s ordinary (.inl notFree)).generation, ?_, ?_⟩ <;>
    simp [step_base, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput,
      withFetch, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting,
      Core.cmd, Core.both, Core.either, Core.free, Core.starting, Core.releasing, Core.hostOwner,
      Core.owned, Core.retained, Core.isPhase, ordinary.1, ordinary.2, notFree, notComplete, notFault,
      inv_one_inv]

private theorem step_lastCapture (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .lastCapture =
      (next .lastCapture).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

set_option linter.unusedSimpArgs false in
/-- HIGH edges preserve the qualified bit while the RX wire may change. -/
theorem high_capture_frame (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (high : s (.base .phase) = 4#3) (latched : HasCapture s capture) :
    HasCapture ((circuit a registered).step i s) capture := by
  cases capture <;>
    simp_all [HasCapture, step_lastCapture, step_captureValid, next, Expr.eval_bind, withFetch,
      lift, Expr.eval, SegmentCore.control, setCount, branch, fetching, both, either,
      Core.clearedRuntime, Core.resetting, Core.cold, Core.warm, Core.cmd, Core.isPhase,
      Core.either, Core.both, Core.starting, Core.releasing, Core.free, Core.hostOwner, Core.owned,
      Core.retained, Core.busy, Core.identity, Core.capturingRX, Core.capture, Core.lowEnd,
      Core.waitSuccess, Core.fetching, ordinary.1, ordinary.2, inv_one_inv]

abbrev IsStream (s : Values (Register a)) : Prop :=
  (s (.base .currentWord)).extractLsb' 0 3 = 1#3

structure HighStep (s after : Values (Register a)) (expired stream repeatCell : Bool) : Prop where
  phase : after (.base .phase) = (if expired then if repeatCell then 2#3 else 1#3 else 4#3)
  pc : after (.base .pc) = (if expired && !repeatCell then s (.base .pc) + 1 else s (.base .pc))
  countdown : after (.base .countdown) =
    (if expired then s (.base .countdown) else s (.base .countdown) - 1)
  remaining : after (.base .remaining) =
    (if expired && stream then s (.base .remaining) - 1 else s (.base .remaining))
  current : after (.base .currentWord) = s (.base .currentWord)
  reserved : after (.base .txConsumed) = s (.base .txConsumed)
  produced : after (.base .rxProduced) = s (.base .rxProduced)

set_option linter.unusedSimpArgs false in
/-- A high-phase tick consumes only time. On expiration, it advances the row
    or starts the next slot under the same instruction. -/
theorem high_step (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (ordinary : NoReset i) (high : s (.base .phase) = 4#3) :
    HighStep s ((circuit a registered).step i s)
      (decide (s (.base .countdown) = 0#8)) (decide (IsStream s))
      (decide (IsStream s ∧ 1 < (s (.base .remaining)).toNat)) := by
  by_cases expired : s (.base .countdown) = 0#8 <;>
    by_cases stream : IsStream s <;>
    by_cases repeats : 1 < (s (.base .remaining)).toNat <;>
    simp only [IsStream] at stream <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [step_base, nextBase, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput, decodedRegister,
      withFetch, Expr.eval, lift, SegmentCore.discard, SegmentCore.control, setCount, branch, fetching,
      both, either, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting, Core.cmd, Core.both,
      Core.either, Core.free, Core.starting, Core.releasing, Core.hostOwner, Core.owned, Core.retained,
      Core.busy, Core.identity, Core.isPhase, Core.clearedRuntime, Core.fetching, Core.enteringCell,
      Core.advancing, Core.capturingRX, Core.capture, Core.reserving, Core.takingTX, Core.lowEnd,
      Core.guardedLowEnd, Core.waitSuccess, Core.standaloneSuccess, Core.waitFault, Core.waitDecrement,
      Core.highEnd, Core.stream, Core.repeating, Core.field, Core.inc, ordinary.1, ordinary.2, inv_one_inv,
      high, expired, stream, repeats, IsStream, BitVec.sub_eq_add_neg, one_and_one] <;> done

/-- A pulse or final stream slot reaches the next encoded row with its
    qualified receive capture intact. -/
theorem high_to_boundary_step (registered : Bool) (i : Values Core.Input)
    (s : Values (Register a)) (ordinary : NoReset i) (high : s (.base .phase) = 4#3)
    (expired : s (.base .countdown) = 0#8)
    (finalCell : ¬(IsStream s ∧ 1 < (s (.base .remaining)).toNat))
    (installed : Installed rows s) (position : (s (.base .pc)).toNat = pc)
    (inBounds : pc < rows.length) (latched : HasCapture s capture) :
    AtBoundary registered rows (pc + 1) capture ((circuit a registered).step i s) := by
  have frame := image_frame registered i s ordinary (.inl (by simp [high]))
  have crossed := high_step registered i s ordinary high
  have phase : ((circuit a registered).step i s) (.base .phase) = 1#3 := by
    simpa only [expired, finalCell, decide_true, decide_false, Bool.false_eq_true, if_false, if_true] using crossed.phase
  have nextPC : ((circuit a registered).step i s) (.base .pc) = s (.base .pc) + 1 := by
    simpa only [expired, finalCell, decide_true, decide_false, Bool.not_false, Bool.true_and, if_true] using crossed.pc
  exact ⟨frame.installed installed, phase,
    (congrArg BitVec.toNat nextPC).trans (advance_pc s position (Nat.lt_of_lt_of_le inBounds installed.size)),
    high_capture_frame registered i s ordinary high latched, reader_coherent registered i s⟩

structure HighPrefix (s after : Values (Register a)) (elapsed : Nat) (capture : Option Bool) : Prop where
  phase : after (.base .phase) = 4#3
  countdown : (after (.base .countdown)).toNat = (s (.base .countdown)).toNat - elapsed
  pc : after (.base .pc) = s (.base .pc)
  remaining : after (.base .remaining) = s (.base .remaining)
  current : after (.base .currentWord) = s (.base .currentWord)
  reserved : after (.base .txConsumed) = s (.base .txConsumed)
  produced : after (.base .rxProduced) = s (.base .rxProduced)
  image : ImageFrame s after
  owner : OwnerFrame s after
  latched : HasCapture after capture

private theorem ImageFrame.trans (left : ImageFrame s middle) (right : ImageFrame middle after) :
    ImageFrame s after :=
  ⟨right.count.trans left.count, right.valid.trans left.valid,
    fun address => (right.word address).trans (left.word address), right.generation.trans left.generation⟩

private theorem OwnerFrame.trans (left : OwnerFrame s middle) (right : OwnerFrame middle after) :
    OwnerFrame s after :=
  ⟨right.generation.trans left.generation, right.transfer.trans left.transfer, right.total.trans left.total⟩

/-- Continuing through the exact high-duration prefix preserves the latched
    bit and leaves the next edge as the cell boundary. -/
theorem high_prefix (registered : Bool) (s : Values (Register a)) (inputs : List (Values Core.Input))
    (ordinary : ∀ i ∈ inputs, NoReset i) (high : s (.base .phase) = 4#3)
    (within : inputs.length ≤ (s (.base .countdown)).toNat) (latched : HasCapture s capture) :
    HighPrefix s (SegmentTiming.run registered s inputs) inputs.length capture := by
  induction inputs generalizing s with
  | nil =>
    exact ⟨high, by simp [SegmentTiming.run], rfl, rfl, rfl, rfl, rfl,
      ⟨rfl, rfl, fun _ => rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, latched⟩
  | cons i rest ih =>
    let mid : Values (Register a) := (circuit a registered).step i s
    have safe := ordinary i (List.mem_cons_self ..)
    have edge := high_step registered i s safe high
    have positive : 0 < (s (.base .countdown)).toNat := by
      simp only [List.length_cons] at within
      omega
    have notExpired : s (.base .countdown) ≠ 0#8 := by
      intro expired
      simp [expired] at positive
    have phase : mid (.base .phase) = 4#3 := by
      simpa only [notExpired, decide_false, Bool.false_eq_true, if_false] using edge.phase
    have tick : (mid (.base .countdown)).toNat = (s (.base .countdown)).toNat - 1 := by
      have decrement : mid (.base .countdown) = s (.base .countdown) - 1 := by
        simpa only [notExpired, decide_false, Bool.false_eq_true, if_false] using edge.countdown
      rw [decrement]
      apply BitVec.toNat_sub_of_le
      change 1 ≤ (s (.base .countdown)).toNat
      omega
    have continued := ih mid (fun j hj => ordinary j (List.mem_cons_of_mem (α := Values Core.Input) i hj)) phase
      (by rw [tick]; simp only [List.length_cons] at within; omega) (high_capture_frame registered i s safe high latched)
    have keepsPC : mid (.base .pc) = s (.base .pc) := by
      simpa only [notExpired, decide_false, Bool.false_and, Bool.false_eq_true, if_false] using edge.pc
    have keepsRemaining : mid (.base .remaining) = s (.base .remaining) := by
      simpa only [notExpired, decide_false, Bool.false_and, Bool.false_eq_true, if_false] using edge.remaining
    have frame := image_frame registered i s safe (.inl (by simp [high]))
    have owner := active_owner_frame registered i s safe (by simp [high]) (by simp [high]) (by simp [high])
    refine ⟨continued.phase, ?_, continued.pc.trans keepsPC, continued.remaining.trans keepsRemaining,
      continued.current.trans edge.current, continued.reserved.trans edge.reserved,
      continued.produced.trans edge.produced, frame.trans continued.image,
      owner.trans continued.owner, continued.latched⟩
    calc
      _ = (mid (.base .countdown)).toNat - rest.length := continued.countdown
      _ = (s (.base .countdown)).toNat - (rest.length + 1) := by rw [tick]; omega

theorem high_to_boundary (registered : Bool) (s : Values (Register a))
    (holds : List (Values Core.Input)) (last : Values Core.Input)
    (ordinary : ∀ i ∈ holds, NoReset i) (lastOrdinary : NoReset last)
    (high : s (.base .phase) = 4#3) (elapsed : holds.length = (s (.base .countdown)).toNat)
    (finalCell : ¬(IsStream s ∧ 1 < (s (.base .remaining)).toNat))
    (installed : Installed rows s) (position : (s (.base .pc)).toNat = pc)
    (inBounds : pc < rows.length) (latched : HasCapture s capture) :
    AtBoundary registered rows (pc + 1) capture (SegmentTiming.run registered s (holds ++ [@last])) := by
  let endHigh : Values (Register a) := SegmentTiming.run registered s holds
  have waiting := high_prefix registered s holds ordinary high (Nat.le_of_eq elapsed) latched
  have expired : endHigh (.base .countdown) = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    exact waiting.countdown.trans (by simp [elapsed])
  have final : ¬(IsStream endHigh ∧ 1 < (endHigh (.base .remaining)).toNat) := by
    change ¬((endHigh (.base .currentWord)).extractLsb' 0 3 = 1#3 ∧ 1 < (endHigh (.base .remaining)).toNat)
    have current : endHigh (.base .currentWord) = s (.base .currentWord) := waiting.current
    have remaining : endHigh (.base .remaining) = s (.base .remaining) := waiting.remaining
    rw [current, remaining]
    exact finalCell
  rw [SegmentTiming.run_append]
  exact high_to_boundary_step registered last endHigh lastOrdinary waiting.phase expired final
    (waiting.image.installed installed) ((congrArg BitVec.toNat waiting.pc).trans position) inBounds waiting.latched

/-- A certified discard row selects the real discard circuit and preserves
    the accepted, consumed and received accounting for the retained owner. -/
theorem discard_step {s : Values (Register a)} (h : AtBoundary registered rows pc capture s)
    (i : Values Core.Input) (runtime : NoReset i) (row : rows[pc]? = some .discard) :
    SegmentCustody.Discarded s ((circuit a registered).step i s) := by
  have fetch := boundary_fetch h i runtime row
  exact SegmentCustody.discard_preserves_custody registered i s
    ⟨fetch.initialized, fetch.ordinary, fetch.phase, fetch.inBounds, selected_row h i row⟩

private theorem step_closed (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .txClosed =
      (next .txClosed).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

set_option linter.unusedSimpArgs false in
/-- HALT or FAULT at a checked fetch cut enters retained custody with the
    installed idle drive. The last instruction does not reserve or capture
    another bit. A closing edge without a TX offer preserves acceptance. -/
theorem terminal_step {s : Values (Register a)} (h : AtBoundary registered rows pc capture s)
    (i : Values Core.Input) (drain : ProtocolOwnership.DrainInput i) (fault : Bool)
    (row : rows[pc]? = some (.cell (if fault then .fault else .halt))) :
    let after : Values (Register a) := (circuit a registered).step i s
    ProtocolOwnership.TerminalCut.of after =
      { ProtocolOwnership.TerminalCut.of s with phase := if fault then 6#3 else 5#3 } ∧
      after (.base .levels) = s (.base .idleLevels) ∧
      after (.base .enabled) = s (.base .idleEnabled) := by
  obtain ⟨init, command, noOffer⟩ := drain
  have ordinary : NoReset i := ⟨init, by simp [command]⟩
  have fetch := boundary_fetch h i ordinary row
  have selected := selected_row h i row
  cases fault <;>
    simp [Row.encode, Pinwheel.Program.StreamingReady.encode] at selected <;>
    simp [ProtocolOwnership.TerminalCut.of, step_base, step_closed, next, nextBase, originalNext, Expr.eval_bind,
      usesEntryWord, runtimeInput, decodedRegister, withFetch, Expr.eval, lift,
      SegmentCore.discard, SegmentCore.control, setCount, branch, fetching, both, either, kind, field,
      Core.next, Core.nextRaw, Core.nextPins, Core.cold, Core.warm, Core.resetting, Core.cmd, Core.both,
      Core.either, Core.free, Core.starting, Core.committing, Core.releasing, Core.hostOwner, Core.owned,
      Core.retained, Core.busy, Core.identity, Core.isPhase, Core.clearedRuntime, Core.fetching,
      Core.entryBad, Core.entryBounds, Core.entryCanonical, Core.entryTerminal, Core.entryPulse,
      Core.entryStream, Core.entryHalt, Core.entryFault, Core.entryWait, Core.entryKind, Core.entryField, Core.entryWord,
      Execution.readTree_correct, Core.pushing, Core.capturingRX, Core.capture, Core.takingTX, Core.reserving,
      Core.lowEnd, Core.highEnd, Core.waitSuccess, Core.waitFault,
      init, command, noOffer, h.phase, fetch.inBounds, selected, inv_one_inv, one_and_one] <;> done

end Pinwheel.Hardware.StreamingReady.SegmentPathControl
