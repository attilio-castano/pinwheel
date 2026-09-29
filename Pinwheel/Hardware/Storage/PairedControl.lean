import Pinwheel.Hardware.Storage.PairedE64

/-! Source-independent equations for execution control in the actual graph. -/
namespace Pinwheel.Hardware.Storage.PairedControl
open Pinwheel.Hardware PairedController PairedRunning PairedBits
set_option backward.isDefEq.respectTransparency false

theorem checkBits_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : checkBits.eval g s = checkBitsExpr.eval g s := by
  simpa only [checkBits, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 4)
      (h .checkBits (.concat (.lit (0 : BitVec 60)) checkBitsExpr) (by simp [bindings]))

theorem guarded_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : guarded.eval g s = guardedExpr.eval g s := by
  simpa only [guarded, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .guarded (.concat (.lit (0 : BitVec 63)) guardedExpr) (by simp [bindings]))

theorem ready_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : ready.eval g s = readyExpr.eval g s := by
  simpa only [ready, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .ready (.concat (.lit (0 : BitVec 63)) readyExpr) (by simp [bindings]))

theorem timeout_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : timeout.eval g s = timeoutExpr.eval g s := by
  simpa only [timeout, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .timeout (.concat (.lit (0 : BitVec 63)) timeoutExpr) (by simp [bindings]))

theorem fault_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : fault.eval g s = faultExpr.eval g s := by
  simpa only [fault, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .fault (.concat (.lit (0 : BitVec 63)) faultExpr) (by simp [bindings]))

theorem ending_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : ending.eval g s = endingExpr.eval g s := by
  simpa only [ending, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .ending (.concat (.lit (0 : BitVec 63)) endingExpr) (by simp [bindings]))

theorem stopping_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : stopping.eval g s = stoppingExpr.eval g s := by
  simpa only [stopping, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 1)
      (h .stopping (.concat (.lit (0 : BitVec 63)) stoppingExpr) (by simp [bindings]))

theorem entrySamples_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : entrySamples.eval g s = entrySamplesExpr.eval g s := by
  simpa only [entrySamples, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 16)
      (h .entrySamples (.concat (.lit (0 : BitVec 48)) entrySamplesExpr) (by simp [bindings]))

theorem captured_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : captured.eval g s = capturedExpr.eval g s := by
  simpa only [captured, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 16)
      (h .captured (.concat (.lit (0 : BitVec 48)) capturedExpr) (by simp [bindings]))

theorem entryLevels_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : entryLevels.eval g s = entryLevelsExpr.eval g s := by
  simpa only [entryLevels, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 3)
      (h .entryLevels (.concat (.lit (0 : BitVec 61)) entryLevelsExpr) (by simp [bindings]))

theorem idleWord_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : idleWord.eval g s = idleWordExpr.eval g s := by
  simpa only [idleWord, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 6)
      (h .idleWord (.concat (.lit (0 : BitVec 58)) idleWordExpr) (by simp [bindings]))

theorem bool_value (x : BitVec 1) (b : Bool) (h : x = 1 ↔ b = true) : x = BitVec.ofBool b := by
  rcases PairedUpload.bit_cases x with hx | hx <;> cases b <;> simp_all

theorem busy_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    busy.eval g s = BitVec.ofBool (s .mode != 0 && (s .mode).toNat < 5) := by
  exact bool_value _ _ ((busy_iff g s h).trans (by simp [Running]))

theorem guarded_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    guarded.eval g s = BitVec.ofBool
      ((Execution.getCheck ((s .cached).extractLsb' 12 4)).ready (g (.base .incoming))) := by
  simp [guarded_wire g s h, guardedExpr, checkBits_wire g s h, checkBitsExpr,
    Expr.eval, incoming_value g s h, Execution.getCheck, Engine.Reactive.Check.ready,
    Bool.beq_eq_decide_eq]

private theorem input_mux : ∀ (selector : BitVec 1) (value : BitVec 2),
    (if selector = 1 then value.extractLsb' 1 1 else value.extractLsb' 0 1) =
      BitVec.ofBool (value.getLsbD selector.toNat) := by decide +kernel

theorem ready_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    ready.eval g s = BitVec.ofBool
      ((g (.base .incoming)).getLsbD (((s .cached).extractLsb' 12 4).extractLsb' 0 1).toNat ==
        ((s .cached).extractLsb' 12 4)[1]) := by
  simp only [ready_wire g s h, readyExpr, bit, Expr.eval, checkBits_wire g s h,
    checkBitsExpr, incoming_value g s h, input_mux]
  simp [slice_one, ← BitVec.getLsbD_eq_getElem, Bool.beq_eq_decide_eq]
  simp only [BitVec.ofBool_eq_iff_eq]
  done

theorem checked_guard (a : Engine.Reactive.Checked 255 15) (g : Values GraphInput)
    (s : Values Register) (h : PairedSemantics.Equations bindings g s)
    (hp : s .cached = PairedImage.parameter (Execution.fields (.checked a))) :
    guarded.eval g s = BitVec.ofBool (a.guard.ready (g (.base .incoming))) := by
  simp only [guarded_value g s h, hp, (PairedE64.parameter_checked a).2.2,
    Execution.check_roundtrip]

theorem checked_decisions (a : Engine.Reactive.Checked 255 15) (g : Values GraphInput)
    (s : Values Register) (h : PairedSemantics.Equations bindings g s) (hm : s .mode = 3)
    (hp : s .cached = PairedImage.parameter (Execution.fields (.checked a))) :
    fault.eval g s = BitVec.ofBool (!a.guard.ready (g (.base .incoming))) ∧
    timeout.eval g s = 0 ∧
    dispatch.eval g s = BitVec.ofBool (a.guard.ready (g (.base .incoming)) && s .remaining == 0) := by
  cases hg : a.guard.ready (g (.base .incoming)) <;> by_cases hr : s .remaining = 0 <;>
    simp [fault_wire g s h, timeout_wire g s h, dispatch_wire g s h, busy_wire g s h,
      faultExpr, timeoutExpr, dispatchExpr, busyExpr, both, either, isMode, Expr.eval,
      checked_guard a g s h hp, hm, hg, hr]
  all_goals bv_normalize
  done

theorem active_decisions (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hm : s .mode = 1) :
    fault.eval g s = 0 ∧ timeout.eval g s = 0 ∧
    dispatch.eval g s = BitVec.ofBool (s .remaining == 0) := by
  simp [fault_wire g s h, timeout_wire g s h, dispatch_wire g s h, busy_wire g s h,
    faultExpr, timeoutExpr, dispatchExpr, busyExpr, both, either, isMode, Expr.eval, hm]
  bv_normalize
  done

private theorem condition_parts : ∀ (input : Fin 2) (level : Bool),
    ((0#2 ++ BitVec.ofBool level ++ (BitVec.ofFin input : BitVec 1)).toNat % 2 = input.val) ∧
    ((0#2 ++ BitVec.ofBool level ++ (BitVec.ofFin input : BitVec 1)).getLsbD 1 = level) := by
  decide +kernel

theorem wait_ready (w : Engine.Reactive.Wait) (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hp : s .cached = PairedImage.parameter (Execution.fields (.wait w))) :
    ready.eval g s = BitVec.ofBool (w.condition.ready (g (.base .incoming))) := by
  simp [ready_value g s h, hp, PairedE64.parameter_check, Execution.fields,
    Engine.Reactive.Condition.ready, ← BitVec.getLsbD_eq_getElem]
  simp only [(condition_parts w.condition.input w.condition.level).1,
    (condition_parts w.condition.input w.condition.level).2]
  done

theorem wait_decisions (w : Engine.Reactive.Wait) (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hm : s .mode = 2)
    (hp : s .cached = PairedImage.parameter (Execution.fields (.wait w))) :
    fault.eval g s = 0 ∧
    timeout.eval g s = BitVec.ofBool (!w.condition.ready (g (.base .incoming)) && s .remaining == 0) ∧
    dispatch.eval g s = BitVec.ofBool (w.condition.ready (g (.base .incoming))) := by
  cases hg : w.condition.ready (g (.base .incoming)) <;> by_cases hr : s .remaining = 0 <;>
    simp [fault_wire g s h, timeout_wire g s h, dispatch_wire g s h, busy_wire g s h,
      faultExpr, timeoutExpr, dispatchExpr, busyExpr, both, either, isMode, Expr.eval,
      wait_ready w g s h hp, hm, hg, hr]
  all_goals bv_normalize

theorem qualify_guard (q : Engine.Reactive.Qualify) (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hp : s .cached = PairedImage.parameter (Execution.fields (.qualify q))) :
    guarded.eval g s = BitVec.ofBool (q.condition.ready (g (.base .incoming))) := by
  simp only [guarded_value g s h, hp, PairedE64.parameter_check, Execution.fields,
    Execution.check_roundtrip]

theorem qualify_decisions (q : Engine.Reactive.Qualify) (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hm : s .mode = 4)
    (hp : s .cached = PairedImage.parameter (Execution.fields (.qualify q))) :
    fault.eval g s = 0 ∧
    timeout.eval g s = BitVec.ofBool (!q.condition.ready (g (.base .incoming)) && s .waitLeft == 0) ∧
    dispatch.eval g s = BitVec.ofBool (q.condition.ready (g (.base .incoming)) && s .remaining == 0) := by
  cases hg : q.condition.ready (g (.base .incoming)) <;>
    by_cases hr : s .remaining = 0 <;> by_cases hw : s .waitLeft = 0 <;>
    simp [fault_wire g s h, timeout_wire g s h, dispatch_wire g s h, busy_wire g s h,
      faultExpr, timeoutExpr, dispatchExpr, busyExpr, both, either, isMode, Expr.eval,
      qualify_guard q g s h hp, hm, hg, hr, hw]
  all_goals bv_normalize

end Pinwheel.Hardware.Storage.PairedControl
