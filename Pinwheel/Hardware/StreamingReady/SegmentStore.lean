import Pinwheel.Hardware.StreamingReady.SegmentCore

/-! Store substitution for the segmented sequencer. Branches change the
    read address, so the register is fed from the actual next PC. -/
namespace Pinwheel.Hardware.StreamingReady.SegmentStore

open Pinwheel.Hardware SegmentCore

private def currentWord (s : Values (Register a)) : BitVec 64 :=
  s (.base (.word ((s (.base .pc)).extractLsb' 0 6)))

def Coherent (s : Values (Register a)) : Prop := s .fetched = currentWord s

def Related (direct cached : Values (Register a)) : Prop :=
  @withFetch a direct 0 = @withFetch a cached 0 ∧ Coherent cached

private theorem directWord_eval (i : Values Core.Input) (s : Values (Register a)) :
    (word false).eval i s = currentWord s := by
  simp only [word, Bool.false_eq_true, if_false, lift, Expr.eval_bind, Core.entryWord,
    Execution.readTree_correct, Expr.eval, currentWord]

private theorem bound_state_eq (i : Values Core.Input) (l r : Values (Register a)) (same : Related l r) :
    @withFetch a l ((word false).eval i l) = @withFetch a r ((word true).eval i r) := by
  have wordEq := congrArg (fun state : Values (Register a) => currentWord state) same.1
  have selected : (word false).eval i l = (word true).eval i r :=
    (directWord_eval i l).trans (wordEq.trans same.2.symm)
  funext w reg
  cases reg with
  | fetched => exact selected
  | base reg =>
    have equal := congrArg (fun state : Values (Register a) => state (.base reg)) same.1
    exact equal
  | lastCapture =>
    have equal := congrArg (fun state : Values (Register a) => state .lastCapture) same.1
    exact equal
  | captureValid =>
    have equal := congrArg (fun state : Values (Register a) => state .captureValid) same.1
    exact equal
  | txClosed =>
    have equal := congrArg (fun state : Values (Register a) => state .txClosed) same.1
    exact equal

private theorem same_logic (i : Values Core.Input) (l r : Values (Register a)) (same : Related l r)
    (expr : E a w) : (bindWord (word false) expr).eval i l = (bindWord (word true) expr).eval i r := by
  rw [bindWord_eval, bindWord_eval, bound_state_eq i l r same]

theorem coherent_after_edge (i : Values Core.Input) (s : Values (Register a)) :
    Coherent ((circuit a true).step i s) := by
  change (load (address true)).eval i s =
    (bindWord (word true) (nextBase (.word ((address true).eval i s)))).eval i s
  have nextWord (k : BitVec 6) : nextBase (a := a) (.word k) = .mux (lift Core.cold) (.lit 0)
      (.mux (both (lift Core.writing) (.equal (.input .address) (.lit k))) (.input .word)
        (.reg (.base (.word k)))) := rfl
  rw [nextWord, bindWord_eval]
  simp only [load, Expr.eval, Execution.readTree_correct, lift, Expr.eval_bind, withFetch]
  rfl

theorem step (i : Values Core.Input) (l r : Values (Register a)) (same : Related l r) :
    Related ((circuit a false).step i l) ((circuit a true).step i r) := by
  refine ⟨?_, coherent_after_edge i r⟩
  funext w reg
  cases reg with
  | fetched => rfl
  | base reg => exact same_logic i l r same (next (.base reg))
  | lastCapture => exact same_logic i l r same (next .lastCapture)
  | captureValid => exact same_logic i l r same (next .captureValid)
  | txClosed => exact same_logic i l r same (next .txClosed)

theorem observe (i : Values Core.Input) (l r : Values (Register a)) (same : Related l r) :
    @Circuit.observe _ _ _ (circuit a false) i l = @Circuit.observe _ _ _ (circuit a true) i r := by
  funext w port
  exact same_logic i l r same (output port)

end Pinwheel.Hardware.StreamingReady.SegmentStore
