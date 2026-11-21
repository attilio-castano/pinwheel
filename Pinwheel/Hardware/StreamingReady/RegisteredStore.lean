import Pinwheel.Hardware.StreamingReady.Core

/-! A clocked look-ahead read for the existing StreamingReady fetch phase.
The address is the next program counter, including START, sequential entry,
and a skipped zero-length stream. An admitted write to that address bypasses
the read to keep the latch coherent with the post-edge bank. -/
namespace Pinwheel.Hardware.StreamingReady.RegisteredStore
open Pinwheel.Hardware

inductive Register (a : Nat) : Nat → Type where
  | base : Core.Register a w → Register a w
  | fetched : Register a 64

abbrev E (a : Nat) := Expr Core.Input (Register a)

def project (s : Values (Register a)) : Values (Core.Register a) := fun r => s (.base r)

private def lift (e : Core.E a w) : E a w :=
  e.bind .input (fun r => .reg (.base r))

/-- The instruction decoder sees the selected word on the read port.
    Other state, and writes to the full bank, still use the base registers. -/
private def decodeRegister : {w : Nat} → Core.Register a w → E a w
  | _, .word _ => .reg .fetched
  | _, r => .reg (.base r)

private def decode (e : Core.E a w) : E a w :=
  e.bind .input decodeRegister

private def nextBase : {w : Nat} → Core.Register a w → E a w
  | _, .phase => decode (Core.next .phase)
  | _, .pc => decode (Core.next .pc)
  | _, .currentWord => decode (Core.next .currentWord)
  | _, .countdown => decode (Core.next .countdown)
  | _, .levels => decode (Core.next .levels)
  | _, .enabled => decode (Core.next .enabled)
  | _, r => lift (Core.next r)

private def address : E a 6 := .slice 0 6 (by decide) (nextBase .pc)

private def load : E a 64 :=
  .mux (lift Core.cold) (.lit 0)
    (.mux (.band (lift Core.writing) (.equal (.input .address) address)) (.input .word)
      (Execution.readTree 6 (fun k => .reg (.base (.word k))) address))

def circuit (a : Nat) : Circuit Core.Input (Register a) Core.Output where
  next := fun r => match r with
    | .base r => nextBase r
    | .fetched => load
  output := fun o => lift (Core.output o)

/-- At every reached edge, the registered response is the word selected by
    the current PC. The complete base register bank projects verbatim. -/
def Related (s : Values (Register a)) : Prop :=
  s .fetched = (Core.entryWord (a := a)).eval (fun _ => 0) (project s)

private theorem lift_eval (e : Core.E a w) (i : Values Core.Input) (s : Values (Register a)) :
    (lift e).eval i s = e.eval i (project s) :=
  Expr.eval_bind .input _ e i s

private def decodeState (s : Values (Register a)) : Values (Core.Register a) :=
  fun r => (decodeRegister r).eval (fun _ => 0) s

private theorem decode_eval (e : Core.E a w) (i : Values Core.Input) (s : Values (Register a)) :
    (decode e).eval i s = e.eval i (decodeState s) := by
  rw [decode, Expr.eval_bind]
  congr 1
  funext w r
  cases r <;> rfl
  done

private theorem read_eval (i : Values Core.Input) (s : Values (Core.Register a)) :
    Core.entryWord.eval i s = s (.word ((s .pc).extractLsb' 0 6)) := by
  simp only [Core.entryWord, Execution.readTree_correct, Expr.eval]
  done

private theorem read_decode (i : Values Core.Input) (s : Values (Register a)) :
    Core.entryWord.eval i (decodeState s) = s .fetched := by
  rw [read_eval]
  rfl
  done

private theorem read_project (i : Values Core.Input) (s : Values (Register a)) (h : Related s) :
    Core.entryWord.eval i (project s) = s .fetched := by
  change s .fetched = Core.entryWord.eval (fun _ => 0) (project s) at h
  rw [h, read_eval, read_eval]
  done

set_option maxHeartbeats 500000 in
private theorem nextBase_eval (i : Values Core.Input) (s : Values (Register a)) (h : Related s)
    (r : Core.Register a w) : (nextBase r).eval i s = (Core.next r).eval i (project s) := by
  cases r <;> first | exact lift_eval _ _ _ | skip
  all_goals simp only [nextBase, decode_eval, Core.next, Core.nextRaw, Core.nextPins,
      Core.enteringCell, Core.entryBad, Core.entryTerminal, Core.entrySkip, Core.entryBounds,
      Core.entryCanonical, Core.entryLast, Core.entryLow, Core.entryPulse, Core.entryStream,
      Core.entryHalt, Core.entryFault, Core.entryWait, Core.entryGuardCanonical,
      Core.entryGuardCountdown, Core.entryGuardBudget, Core.entryGuardExpected, Core.entryGuardMask,
      Core.entryKind, Core.entryField, Core.clearedRuntime, Core.both, Core.either,
      Core.resetting, Core.cold, Core.warm, Core.cmd, Core.releasing, Core.starting, Core.hostOwner,
      Core.owned, Core.identity, Core.drained, Core.free, Core.busy, Core.retained, Core.isPhase, Core.space,
      Core.advancing, Core.repeating, Core.highEnd, Core.guardedLowEnd, Core.standaloneSuccess,
      Core.fetching, Core.reserving, Core.credit, Core.txAvailable, Core.rxRoom, Core.depth,
      Core.capture, Core.waitSuccess, Core.waitFault, Core.waitReady, Core.waitDecrement,
      Core.lowEnd, Core.highGuard, Core.guardBudget, Core.guardMask, Core.guardExpected,
      Core.inc, Core.guardCountdown, Core.driven, Core.nextBit, Core.txSource, Core.txHeadWord,
      Core.basePins, Core.lastCell, Core.pack, Core.transmit, Core.receive, Core.stream, Core.field,
      Execution.readTree_correct, Expr.eval, read_decode, read_project i s h, decodeState, decodeRegister, project,
      Bool.false_eq_true, ite_false, if_pos]
  all_goals rfl
  done

theorem project_step {a : Nat} (i : Values Core.Input) (s : Values (Register a)) (h : Related s) :
    @project a ((circuit a).step i s) = @Circuit.step _ _ _ (Core.circuit a) i (project s) := by
  funext w r
  exact nextBase_eval i s h r
  done

theorem observe_eq {a : Nat} (i : Values Core.Input) (s : Values (Register a)) :
    @Circuit.observe _ _ _ (circuit a) i s = @Circuit.observe _ _ _ (Core.circuit a) i (project s) := by
  funext w o
  exact lift_eval _ i s
  done

/-- The read result matches the actual post-edge bank and PC on every edge. -/
theorem coherent_after_edge {a : Nat} (i : Values Core.Input) (s : Values (Register a)) :
    Related ((circuit a).step i s) := by
  unfold Related
  rw [read_eval]
  change load.eval i s = (nextBase (.word (address.eval i s))).eval i s
  simp only [load, Expr.eval, lift_eval, Execution.readTree_correct, nextBase, Core.next,
    Core.nextRaw, Core.both, project]
  rfl
  done

private theorem resetting_cold (i : Values Core.Input) (s : Values (Core.Register a))
    (cold : i .initialize = 1) : Core.resetting.eval i s = 1 := by
  simp [Core.resetting, Core.either, Core.warm, Core.cold, Core.both, Expr.eval, cold]
  done

private theorem inv_one : ~~~(1#1) = 0 := rfl

/-- Cold reset projects correctly even when the old cache has arbitrary contents. -/
theorem project_cold {a : Nat} (i : Values Core.Input) (s : Values (Register a)) (cold : i .initialize = 1) :
    @project a ((circuit a).step i s) = @Circuit.step _ _ _ (Core.circuit a) i (project s) := by
  funext w r
  change (nextBase r).eval i s = (Core.next r).eval i (project s)
  cases r <;> first | exact lift_eval _ _ _ | skip
  all_goals simp only [nextBase, decode_eval, Core.next, Core.clearedRuntime, Core.either,
    Expr.eval, resetting_cold _ _ cold, if_pos]
  all_goals simp [inv_one, Core.cold, Expr.eval, cold]
  done

end Pinwheel.Hardware.StreamingReady.RegisteredStore
