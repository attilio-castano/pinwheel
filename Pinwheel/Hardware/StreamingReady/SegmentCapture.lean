import Pinwheel.Hardware.StreamingReady.SegmentStreamStep

/-! Completion of an unguarded stream LOW cut. The sample comes from the
old second sampler even when the external pin moves on the capture edge. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentCapture

open Pinwheel.Hardware SegmentCore SegmentPathControl
open Pinwheel.Program.StreamingReady

private theorem step_base (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (r : Core.Register a w) :
    (circuit a registered).step i s (.base r) =
      (nextBase r).eval i (withFetch s ((word registered).eval i s)) :=
  bindWord_eval _ _ _ _

private theorem step_extra (registered : Bool) (i : Values Core.Input) (s : Values (Register a)) :
    (circuit a registered).step i s .lastCapture =
        (next .lastCapture).eval i (withFetch s ((word registered).eval i s)) ∧
      (circuit a registered).step i s .captureValid =
        (next .captureValid).eval i (withFetch s ((word registered).eval i s)) :=
  ⟨bindWord_eval _ _ _ _, bindWord_eval _ _ _ _⟩

private theorem inv_one_inv (x : BitVec 1) : ~~~(1#1 &&& ~~~x) = x := by decide +revert +kernel

private theorem extractBit (bits : BitVec 2) (index : Fin 2) :
    (if BitVec.ofNat 1 index.val = 1#1 then bits.extractLsb' 1 1 else bits.extractLsb' 0 1) =
      BitVec.ofBool bits[index.val] := by
  have one (idx : Nat) : bits.extractLsb' idx 1 = BitVec.ofBool (bits.getLsbD idx) := by
    rw [BitVec.getLsbD_eq_extractLsb']
    rcases BitVec.eq_zero_or_eq_one (bits.extractLsb' idx 1) with h | h <;> simp [h]
  have range : index.val = 0 ∨ index.val = 1 := by omega
  rcases range with h | h <;> simp [h, one, BitVec.getLsbD_eq_getElem]

structure Captured (cell : Cell) (s after : Values (Register a)) (previous : Option Bool) : Prop where
  high : after (.base .phase) = 4#3
  countdown : after (.base .countdown) = BitVec.ofNat 8 cell.highDuration.val
  current : after (.base .currentWord) = s (.base .currentWord)
  pc : after (.base .pc) = s (.base .pc)
  remaining : after (.base .remaining) = s (.base .remaining)
  reserved : after (.base .txConsumed) = s (.base .txConsumed)
  produced : after (.base .rxProduced) = s (.base .rxProduced) + (if cell.receive then 1#16 else 0)
  latched : HasCapture after (if cell.receive then some ((s (.base .stage2))[cell.rxInput.val]) else previous)

set_option linter.unusedSimpArgs false in
theorem capture (registered : Bool) (i : Values Core.Input) (s : Values (Register a))
    (cell : Cell) (ordinary : NoReset i) (low : s (.base .phase) = 3#3)
    (elapsed : s (.base .countdown) = 0#8)
    (loaded : s (.base .currentWord) = encode (.stream cell none))
    (old : HasCapture s previous) :
    Captured cell s ((circuit a registered).step i s) previous := by
  have fields := encode_fields (.stream cell none)
  have stream : (s (.base .currentWord)).extractLsb' 0 3 = 1#3 := loaded ▸ fields.operation
  have guard : (s (.base .currentWord)).extractLsb' 62 1 = 0#1 := loaded ▸ fields.highGuard
  have receive : (s (.base .currentWord)).extractLsb' 35 1 = BitVec.ofBool cell.receive := loaded ▸ fields.receive
  have source : (s (.base .currentWord)).extractLsb' 33 1 = BitVec.ofNat 1 cell.rxInput.val :=
    loaded ▸ fields.rxInput
  have period : (s (.base .currentWord)).extractLsb' 11 8 = BitVec.ofNat 8 cell.highDuration.val :=
    loaded ▸ fields.highDuration
  have increment (x : BitVec 16) : x - 65535#16 = x + 1 := by decide +revert +kernel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?latch⟩
  case latch =>
    have latched := step_extra registered i s
    simp [next, lift, Expr.eval_bind, Expr.eval, withFetch, Core.clearedRuntime, Core.cold, Core.warm,
      Core.resetting, Core.cmd, Core.either, Core.both, Core.free, Core.starting, Core.releasing,
      Core.hostOwner, Core.owned, Core.retained, Core.isPhase, Core.capture, Core.waitSuccess,
      Core.standaloneSuccess, Core.guardedLowEnd, Core.lowEnd, Core.capturingRX, Core.receive,
      Core.stream, Core.highGuard, Core.field, Core.inputBit, Core.fetching, SegmentCore.control, either, both,
      fetching, branch, setCount, ordinary.1, ordinary.2, low, elapsed, stream, guard, receive,
      source, inv_one_inv] at latched
    by_cases rx : cell.receive
    · simp [rx, HasCapture, latched.1, latched.2]
      simpa using extractBit (s (.base .stage2)) cell.rxInput
    · cases previous <;> simpa [rx, HasCapture, latched.1, latched.2] using old
  all_goals
    simp [step_base,
      nextBase, next, originalNext, Expr.eval_bind, usesEntryWord, runtimeInput, decodedRegister,
      withFetch, lift, Expr.eval, Core.next, Core.nextRaw, Core.cold, Core.warm, Core.resetting,
      Core.cmd, Core.both, Core.either, Core.free, Core.starting, Core.releasing, Core.hostOwner,
      Core.owned, Core.retained, Core.isPhase, Core.fetching, Core.enteringCell, Core.reserving,
      Core.takingTX, Core.lowEnd, Core.advancing, Core.highEnd, Core.guardedLowEnd, Core.capture,
      Core.standaloneSuccess, Core.waitSuccess, Core.waitFault, Core.waitDecrement,
      Core.capturingRX, Core.receive, Core.highGuard, Core.stream, Core.field, Core.inputBit,
      Core.clearedRuntime, Core.inc, SegmentCore.control, SegmentCore.discard, branch, setCount, fetching, both, either,
      ordinary.1, ordinary.2, low, elapsed, stream, guard, receive, period, source, inv_one_inv, increment]
  all_goals by_cases rx : cell.receive <;> simp (config := {failIfUnchanged := false}) [rx]
  all_goals done

end Pinwheel.Hardware.StreamingReady.SegmentCapture
