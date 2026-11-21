import Pinwheel.Hardware.StreamingReady.TxShiftCore
import Pinwheel.Hardware.StreamingReady.TxShiftCoreRing

namespace Pinwheel.Hardware.StreamingReady.TxShiftCore
open Pinwheel.Hardware

private def decode (s : Values Register) : Values (Core.Register 1) :=
  fun r => if h : retained r then s ⟨r, h⟩ else 0

private theorem lift_eval (e : Core.E 1 w) (i : Values Core.Input) (s : Values Register) :
    (lift e).eval i s = e.eval i (decode s) := by
  rw [lift, Expr.eval_bind]
  congr 1
  funext w r
  cases r <;> rfl

set_option maxHeartbeats 2000000 in
theorem observe_encode (i : Values Core.Input) (s : Values (Core.Register 1)) :
    @Circuit.observe _ _ _ circuit i (encode s) = @Circuit.observe _ _ _ (Core.circuit 1) i s := by
  funext w o
  change (lift (Core.output o)).eval i (encode s) = (Core.output o).eval i s
  rw [lift_eval]
  cases o <;> rfl

private def normalized (s : Values (Core.Register 1)) : Values (Core.Register 1) := decode (encode s)

private theorem headWord_normalized (i : Values Core.Input) (s : Values (Core.Register 1)) :
    Core.txHeadWord.eval i (normalized s) = Core.txHeadWord.eval i s := by
  simp [Core.txHeadWord, Execution.readTree_correct, Expr.eval, normalized, decode, encode, retained]

private theorem headBits_normalized (i : Values Core.Input) (s : Values (Core.Register 1)) :
    Core.txHeadBits.eval i (normalized s) = Core.txHeadBits.eval i s := by
  simp [Core.txHeadBits, Execution.readTree_correct, Expr.eval, normalized, decode, encode, retained]

private theorem source_normalized (i : Values Core.Input) (s : Values (Core.Register 1)) :
    Core.txSource.eval i (normalized s) = Core.txSource.eval i s := by
  simp only [Core.txSource, Expr.eval, headWord_normalized]
  rfl

private theorem sourceBits_normalized (i : Values Core.Input) (s : Values (Core.Register 1)) :
    Core.txSourceBits.eval i (normalized s) = Core.txSourceBits.eval i s := by
  simp only [Core.txSourceBits, Expr.eval, headBits_normalized]
  rfl

private theorem entryWord_normalized (i : Values Core.Input) (s : Values (Core.Register 1)) :
    Core.entryWord.eval i (normalized s) = Core.entryWord.eval i s := by
  simp only [Core.entryWord, Execution.readTree_correct, Expr.eval]
  rfl

-- Expand decode decisions while treating the program-bank read as one tap.
local macro "entry_eval" : tactic => `(tactic|
  simp only [Core.enteringCell, Core.entryBad, Core.entryTerminal, Core.entrySkip, Core.entryBounds,
    Core.entryCanonical, Core.entryLast, Core.entryLow, Core.entryPulse, Core.entryStream, Core.entryHalt,
    Core.entryFault, Core.entryWait, Core.entryGuardCanonical, Core.entryGuardCountdown,
    Core.entryGuardBudget, Core.entryGuardExpected, Core.entryGuardMask, Core.entryKind, Core.entryField,
    Core.either, Core.both, Expr.eval, entryWord_normalized])

private theorem driven_normalized (i : Values Core.Input) (s : Values (Core.Register 1)) (enabled : Bool) :
    (Core.driven false enabled Core.nextBit).eval i (normalized s) =
      (Core.driven false enabled Core.nextBit).eval i s := by
  cases enabled <;> simp only [Core.driven, Core.pack, Core.nextBit, Bool.false_eq_true, if_false, if_true,
    Expr.eval, source_normalized] <;> rfl

set_option linter.unusedSimpArgs false in
private theorem pins_normalized (i : Values Core.Input) (s : Values (Core.Register 1)) (enabled : Bool) :
    (Core.nextPins enabled).eval i (normalized s) = (Core.nextPins enabled).eval i s := by
  cases enabled <;> simp only [Core.nextPins, Expr.eval, driven_normalized]
  all_goals entry_eval <;> rfl

private def dataSlot : Core.Register 1 w → Prop
  | .txWord _ | .txBits _ => True
  | _ => False

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
private theorem next_normalized (i : Values Core.Input) (s : Values (Core.Register 1))
    (r : Core.Register 1 w) (keep : retained r) (other : ¬ dataSlot r) :
    (Core.next r).eval i (normalized s) = (Core.next r).eval i s := by
  cases r <;> try contradiction
  case levels | enabled =>
    simp only [Core.next, Core.nextRaw, Expr.eval, pins_normalized]
    rfl
  case cellBit =>
    simp only [Core.next, Core.nextRaw, Core.nextBit, Expr.eval, source_normalized]
    rfl
  case txShift =>
    simp only [Core.next, Core.nextRaw, Expr.eval, source_normalized]
    rfl
  case txValid =>
    simp only [Core.next, Core.nextRaw, Expr.eval, sourceBits_normalized]
    rfl
  case phase | pc | currentWord | countdown =>
    simp only [Core.next, Core.nextRaw, Expr.eval]
    entry_eval
    rfl
  all_goals rfl

private theorem other_next (r : Register w) (other : ¬ dataSlot r.val) :
    circuit.next r = lift (Core.next r.val) := by
  obtain ⟨r, keep⟩ := r
  cases r <;> (first | contradiction | rfl)

private theorem other_encode (s : Values (Core.Register 1)) (r : Register w) (other : ¬ dataSlot r.val) :
    encode s r = s r.val := by
  obtain ⟨r, keep⟩ := r
  cases r <;> (first | contradiction | rfl)

private theorem one_and : ∀ a b : BitVec 1, a &&& b = 1 ↔ a = 1 ∧ b = 1 := by decide +kernel
private theorem decide_one (p : Prop) [Decidable p] : BitVec.ofBool (decide p) = 1 ↔ p := by
  by_cases h : p <;> simp [h]

private theorem slotEq_one (i : Values Core.Input) (s : Values Register) (k : BitVec 1) :
    (Expr.equal (.slice 0 1 (by decide) (.reg ⟨.txCount, trivial⟩)) (.lit k) : E 1).eval i s = 1 ↔
      k = (s ⟨.txCount, trivial⟩).extractLsb' 0 1 :=
  (decide_one _).trans eq_comm

private theorem slotUpdate_eval (i : Values Core.Input) (s : Values Register)
    (slot : BitVec 1 → Core.Register 1 w) (input : Core.Input w)
    (resetValue : BitVec w) (index : BitVec 1) (valid : ∀ k, retained (slot k)) :
    (slotUpdate slot input resetValue index valid).eval i s =
      if Core.clearedRuntime.eval i (decode s) = 1 then resetValue
      else
        let oldIndex := if Core.loadingTX.eval i (decode s) = 1 then index + 1 else index
        if Core.pushing.eval i (decode s) = 1 ∧ oldIndex = (s ⟨.txCount, trivial⟩).extractLsb' 0 1
          then i input else s ⟨slot oldIndex, valid oldIndex⟩ := by
  simp only [slotUpdate, clear, put, take, Expr.eval.eq_12, Expr.eval.eq_6, Expr.eval.eq_1,
    Expr.eval.eq_2, Expr.eval.eq_3, lift_eval, one_and, slotEq_one]
  all_goals split <;> try rfl
  all_goals split <;> rfl

private def asShift (s : Values Register) : TxQueue.Shift Chunk :=
  ⟨s ⟨.txCount, trivial⟩, fun k => (s ⟨.txWord k, trivial⟩, s ⟨.txBits k, trivial⟩)⟩

private theorem shift_encode (s : Values (Core.Register 1)) : asShift (encode s) = (asRing s).encode := rfl

private theorem ite_pair (p : Prop) [Decidable p] (x x' : α) (y y' : β) :
    ((if p then x else x'), (if p then y else y')) = if p then (x, y) else (x', y') := by
  by_cases h : p <;> simp [h]

private theorem shift_slots_step (i : Values Core.Input) (s : Values Register) (k : BitVec 1) :
    (asShift (circuit.step i s)).slot k =
      ((asShift s).step (clears i (decode s)) (pushes i (decode s)) (pops i (decode s))
        (incoming i) (0#32, 32#6)).slot k := by
  simp only [asShift, Circuit.step, circuit, next, slotUpdate_eval, TxQueue.Shift.step, clears,
    pushes, pops, incoming, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, ite_pair]
  all_goals split <;> rfl

private theorem slots_encode (i : Values Core.Input) (s : Values (Core.Register 1))
    (well : RingInvariant s) (k : BitVec 1) :
    (asShift (circuit.step i (encode s))).slot k =
      (asShift (encode ((Core.circuit 1).step i s))).slot k := by
  have eq := shift_slots_step i (encode s) k
  change (asShift (circuit.step i (encode s))).slot k =
      ((asShift (encode s)).step (clears i s) (pushes i s) (pops i s) (incoming i) (0#32, 32#6)).slot k at eq
  rw [shift_encode, ← (asRing s).encode_step _ _ _ _ _ well, ← ring_step] at eq
  rw [shift_encode]
  exact eq

theorem step_encode (i : Values Core.Input) (s : Values (Core.Register 1)) (well : RingInvariant s) :
    @Circuit.step _ _ _ circuit i (encode s) = @encode ((Core.circuit 1).step i s) := by
  funext w r
  by_cases slot : dataSlot r.val
  · obtain ⟨r, keep⟩ := r
    cases r <;> try contradiction
    case txWord k => exact congrArg Prod.fst (slots_encode i s well k)
    case txBits k => exact congrArg Prod.snd (slots_encode i s well k)
  · simp only [Circuit.step, other_next _ slot, other_encode _ _ slot, lift_eval]
    exact next_normalized i s r.val r.property slot

private theorem cold_slots (i j : Values Core.Input) (s : Values (Core.Register 1)) (t : Values Register)
    (hi : i .initialize = 1) (hj : j .initialize = 1) (k : BitVec 1) :
    (asShift (circuit.step i t)).slot k = (asShift (encode ((Core.circuit 1).step j s))).slot k := by
  rw [shift_slots_step, cold_clears i _ hi, shift_encode, ring_step, cold_clears j s hj]
  rfl

private theorem one_or (i : Values Core.Input) (s : Values (Core.Register 1)) (x y : Core.E 1 1) :
    (Core.either x y).eval i s = 1 ↔ x.eval i s = 1 ∨ y.eval i s = 1 :=
  (by decide +kernel : ∀ a b : BitVec 1, ~~~(~~~a &&& ~~~b) = 1 ↔ a = 1 ∨ b = 1) _ _

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
private theorem cold_other (i j : Values Core.Input) (s t : Values (Core.Register 1))
    (hi : i .initialize = 1) (hj : j .initialize = 1) (r : Core.Register 1 w) :
    (Core.next r).eval i t = (Core.next r).eval j s := by
  have resetI := cold_resets i t hi
  have resetJ := cold_resets j s hj
  have clearI : Core.clearedRuntime.eval i t = 1 := of_decide_eq_true (cold_clears i t hi)
  have clearJ : Core.clearedRuntime.eval j s = 1 := of_decide_eq_true (cold_clears j s hj)
  cases r <;> simp only [Core.next, Expr.eval, resetI, resetJ, clearI, clearJ,
    one_or, Core.cold, hi, hj, true_or, if_true]

theorem cold_encode (i j : Values Core.Input) (s : Values (Core.Register 1)) (t : Values Register)
    (hi : i .initialize = 1) (hj : j .initialize = 1) :
    @Circuit.step _ _ _ circuit i t = @encode ((Core.circuit 1).step j s) := by
  funext w r
  by_cases slot : dataSlot r.val
  · obtain ⟨r, keep⟩ := r
    cases r <;> try contradiction
    case txWord k => exact congrArg Prod.fst (cold_slots i j s t hi hj k)
    case txBits k => exact congrArg Prod.snd (cold_slots i j s t hi hj k)
  · simp only [Circuit.step, other_next _ slot, other_encode _ _ slot, lift_eval]
    exact cold_other i j s (decode t) hi hj r.val

end Pinwheel.Hardware.StreamingReady.TxShiftCore
