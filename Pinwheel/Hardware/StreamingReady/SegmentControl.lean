import Pinwheel.Hardware.StreamingReady.SegmentCore
import Pinwheel.Program.StreamingReadySegments

/-! Instruction boundaries for the two selected-word circuits. Decode the
    compiler's own words and bound the effect of each control instruction. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentControl

open Pinwheel.Hardware SegmentCore
open Pinwheel.Program.StreamingReadySegments (Row)

structure AtFetch (i : Values Core.Input) (s : Values (Register a)) : Prop where
  initialized : i .initialize = 0#1
  ordinary : i .command ≠ 15#4
  phase : s (.base .phase) = 1#3
  inBounds : (s (.base .pc)).toNat < (s (.base .count)).toNat

private def selected (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    Values (Register a) := withFetch s ((word registered).eval i s)

private theorem lift_eval (expr : Core.E a w) (i : Values Core.Input) (s : Values (Register a)) :
    (lift expr).eval i s = expr.eval i (project s) := Expr.eval_bind .input _ expr i s

private theorem fetching_eval (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (fetch : AtFetch i s) : fetching.eval i (selected registered i s) = 1#1 := by
  simp [fetching, both, lift_eval, Core.fetching, Core.entryBounds, Core.resetting,
    Core.either, Core.both, Core.cold, Core.warm, Core.cmd, Core.isPhase, Expr.eval,
    project, selected, withFetch, fetch.initialized, fetch.ordinary, fetch.phase, fetch.inBounds]

private theorem step_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (reg : Core.Register a w) :
    (circuit a registered).step i s (.base reg) = (nextBase reg).eval i (selected registered i s) :=
  bindWord_eval _ _ _ _

private theorem step_valid (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .captureValid = (next .captureValid).eval i (selected registered i s) :=
  bindWord_eval _ _ _ _

private theorem pc_inc (x : BitVec 7) : x - 127#7 = x + 1#7 := by decide +revert +kernel

/-- An encoded count loads the segment's counter and invalidates any
    earlier capture before continuing at the next instruction. -/
theorem set_count (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (fetch : AtFetch i s) (slots : BitVec 16) (nonzero : slots ≠ 0#16)
    (loaded : (word registered).eval i s = (Row.count slots).encode) :
    let after : Values (Register a) := (circuit a registered).step i s
    after (.base .pc) = s (.base .pc) + 1 ∧ after (.base .remaining) = slots ∧
      after (.base .phase) = 1#3 ∧ after .captureValid = 0#1 := by
  dsimp only
  let state : Values (Register a) := selected registered i s
  have active : fetching.eval i state = 1#1 := fetching_eval registered i s fetch
  obtain ⟨opcode, bits, reserved⟩ := Row.count_fields slots
  have installed : state .fetched = (Row.count slots).encode := loaded
  have countNow : setCount.eval i state = 1#1 := by
    simp [setCount, both, kind, count, field, Expr.eval, installed, active, opcode, bits, reserved, nonzero]
  have branchOff : branch.eval i state = 0#1 := by
    simp [branch, both, kind, field, Expr.eval, installed, opcode]
  have discardOff : discard.eval i state = 0#1 := by
    have different : (Row.count slots).encode ≠ 7#64 := by
      intro same
      rw [same] at opcode
      contradiction
    simp [SegmentCore.discard, both, Expr.eval, installed, different]
  have controlNow : control.eval i state = 1#1 := by
    simp [SegmentCore.control, either, Expr.eval, countNow, branchOff]
  have size : count.eval i state = slots := by simp [count, field, Expr.eval, installed, bits]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [step_base]
    change (nextBase .pc).eval i state = _
    simp only [nextBase, Expr.eval, branchOff, countNow, lift_eval, Core.inc, project]
    simp [state, selected, withFetch, pc_inc]
  · rw [step_base]
    change (nextBase .remaining).eval i state = _
    simp [nextBase, Expr.eval, countNow, size]
  · rw [step_base]
    change (nextBase .phase).eval i state = _
    simp [nextBase, Expr.eval, discardOff, controlNow]
  · rw [step_valid]
    change (next .captureValid).eval i state = _
    simp [next, either, Expr.eval, controlNow]

/-- The branch consumes the latched receive bit, even if raw input has
    subsequently changed. Both outcomes stay on the instruction-fetch path. -/
theorem take_branch (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (fetch : AtFetch i s) (destination : BitVec 6) (onBit : Bool)
    (forward : (s (.base .pc)).toNat < destination.toNat)
    (inBounds : destination.toNat < (s (.base .count)).toNat)
    (valid : s .captureValid = 1#1)
    (loaded : (word registered).eval i s = (Row.branch destination onBit).encode) :
    let after : Values (Register a) := (circuit a registered).step i s
    after (.base .pc) = (if s .lastCapture = BitVec.ofBool onBit then 0#1 ++ destination else s (.base .pc) + 1) ∧
      after (.base .phase) = 1#3 ∧ after .captureValid = 0#1 := by
  dsimp only
  let state : Values (Register a) := selected registered i s
  have active : fetching.eval i state = 1#1 := fetching_eval registered i s fetch
  obtain ⟨opcode, bits, condition, reserved⟩ := Row.branch_fields destination onBit
  have installed : state .fetched = (Row.branch destination onBit).encode := loaded
  have extended : (0#1 ++ destination).toNat = destination.toNat := by rw [BitVec.toNat_append]; simp
  have branchNow : branch.eval i state = 1#1 := by
    simp only [branch, both, kind, target, field, Expr.eval, active, installed, opcode, bits, reserved]
    change 1#1 &&& (1#1 &&& (1#1 &&& (s .captureValid &&&
      (BitVec.ofBool (decide ((s (.base .pc)).toNat < (0#1 ++ destination).toNat)) &&&
       BitVec.ofBool (decide ((0#1 ++ destination).toNat < (s (.base .count)).toNat)))))) = 1#1
    rw [extended, valid]
    simp [forward, inBounds]
  have controlNow : control.eval i state = 1#1 := by
    simp [SegmentCore.control, either, Expr.eval, branchNow]
  have discardOff : discard.eval i state = 0#1 := by
    have different : (Row.branch destination onBit).encode ≠ 7#64 := by
      intro same
      rw [same] at opcode
      contradiction
    simp [SegmentCore.discard, both, Expr.eval, installed, different]
  refine ⟨?_, ?_, ?_⟩
  · rw [step_base]
    change (nextBase .pc).eval i state = _
    simp only [nextBase, Expr.eval, branchNow, branchOn, target, field, installed, condition, bits,
      lift_eval, Core.inc, project]
    simp [state, selected, withFetch, pc_inc]
  · rw [step_base]
    change (nextBase .phase).eval i state = _
    simp [nextBase, Expr.eval, discardOff, controlNow]
  · rw [step_valid]
    change (next .captureValid).eval i state = _
    simp [next, either, Expr.eval, controlNow]

/-- Only the existing qualified RX event latches a branch input. On a
    guarded wait, that value is read from the second sampler. -/
theorem guarded_capture (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (initialized : i .initialize = 0#1) (ordinary : i .command ≠ 15#4)
    (waiting : s (.base .phase) = 7#3) (captures : (lift Core.capturingRX).eval i s = 1#1) :
    let after : Values (Register a) := (circuit a registered).step i s
    after .captureValid = 1#1 ∧
      after .lastCapture = (if (s (.base .currentWord)).extractLsb' 33 1 = 1#1 then
        (s (.base .stage2)).extractLsb' 1 1 else (s (.base .stage2)).extractLsb' 0 1) := by
  dsimp only
  let state : Values (Register a) := selected registered i s
  have base : @project a state = @project a s := rfl
  have clear : (lift Core.clearedRuntime).eval i state = 0#1 := by
    simp [lift_eval, Core.clearedRuntime, Core.starting, Core.releasing, Core.free, Core.retained,
      Core.resetting, Core.either, Core.both, Core.cold, Core.warm, Core.cmd, Core.isPhase, Expr.eval,
      project, state, selected, withFetch, initialized, ordinary, waiting]
  have idleControl : SegmentCore.control.eval i state = 0#1 := by
    have idleFetch : fetching.eval i state = 0#1 := by
      simp [fetching, both, lift_eval, Core.fetching, Core.isPhase, Core.both, Expr.eval, project,
        state, selected, withFetch, waiting]
    simp [SegmentCore.control, either, setCount, branch, both, Expr.eval, idleFetch]
  have fired : (lift Core.capturingRX).eval i state = 1#1 := by
    rw [lift_eval, base, ← lift_eval]
    exact captures
  constructor
  · rw [step_valid]
    change (next .captureValid).eval i state = _
    simp [next, either, Expr.eval, clear, idleControl, fired]
  · have latch : (circuit a registered).step i s .lastCapture = (next .lastCapture).eval i state :=
      bindWord_eval _ _ _ _
    rw [latch]
    simp only [next, Expr.eval, clear, fired]
    rw [lift_eval, base]
    rfl

end Pinwheel.Hardware.StreamingReady.SegmentControl
