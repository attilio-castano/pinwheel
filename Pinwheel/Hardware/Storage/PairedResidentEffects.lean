import Pinwheel.Hardware.Storage.PairedControl

/-! Local operation semantics of the retained resident datapath. These results
interpret actual graph equations and pre-edge registers. They require no image
certificate or memory law, and do not assert a complete resident-program or
package lifecycle refinement. -/
namespace Pinwheel.Hardware.Storage.PairedResidentEffects
open Pinwheel.Hardware PairedController PairedRunning PairedBits PairedControl
set_option backward.isDefEq.respectTransparency false

def operand (acceptedStart : Bool) (data : BitVec 64) (old : BitVec 8) : BitVec 8 :=
  if acceptedStart then data.extractLsb' 0 8 else old

def shiftOperand (msbFirst : Bool) (old : BitVec 8) : BitVec 8 :=
  if msbFirst then old <<< 1 else old >>> 1

def outputBit (msbFirst : Bool) (old : BitVec 8) : Bool :=
  old.getLsbD (if msbFirst then 7 else 0)

theorem entryPayload_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    entryPayload.eval g s = entryPayloadExpr.eval g s := by
  simpa only [entryPayload, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 8)
      (h .entryPayload (.concat (.lit (0 : BitVec 56)) entryPayloadExpr) (by simp [bindings]))

theorem operand_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    entryPayload.eval g s = operand (start.eval g s == 1) (g (.base .data)) (s .payload) := by
  simp [entryPayload_wire g s h, entryPayloadExpr, Expr.eval, operand, PairedUpload.data_value g s h]

theorem accepted_start_snapshot (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hs : start.eval g s = 1) :
    entryPayload.eval g s = (g (.base .data)).extractLsb' 0 8 := by
  simp [operand_value g s h, operand, hs]

theorem shifted_wire (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) : shifted.eval g s = shiftedExpr.eval g s := by
  simpa only [shifted, Expr.eval, BitVec.extractLsb'_append_eq_right] using
    congrArg (fun v : BitVec 64 => v.extractLsb' 0 8)
      (h .shifted (.concat (.lit (0 : BitVec 56)) shiftedExpr) (by simp [bindings]))

theorem shift_layout (msbFirst : Bool) (value : BitVec 8) :
    (if msbFirst then value.extractLsb' 0 7 ++ (0#1)
      else (0#1) ++ value.extractLsb' 1 7) = shiftOperand msbFirst value := by
  cases msbFirst <;> simp [shiftOperand] <;> bv_decide

theorem shifted_value (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) :
    shifted.eval g s = shiftOperand (parameter0.eval g s)[2] (entryPayload.eval g s) := by
  simp [shifted_wire g s h, shiftedExpr, Expr.eval, slice_one, shift_layout,
    ← BitVec.getLsbD_eq_getElem]
  done

theorem shift_levels_bit (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hk : (entered.eval g s).extractLsb' 0 3 = 5) (pin : Fin 3) :
    (entryLevels.eval g s)[pin.val] =
      if (parameter0.eval g s).extractLsb' 0 2 = BitVec.ofNat 2 pin.val then
        outputBit (parameter0.eval g s)[2] (entryPayload.eval g s)
      else (entered.eval g s).getLsbD (pin.val + 3) := by
  simp [entryLevels_wire g s h, entryLevelsExpr, isKind, kind, Expr.eval, hk]
  rw [pack_bit]
  simp [Expr.eval, slice_one, outputBit, ← BitVec.getLsbD_eq_getElem]
  by_cases hs : (parameter0.eval g s).extractLsb' 0 2 = BitVec.ofNat 2 pin.val <;>
    cases hb : (parameter0.eval g s)[2] <;> simp_all [Nat.add_comm, ← BitVec.getLsbD_eq_getElem]
  done

theorem payload_enter_shift (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hr : resetting.eval g s = 0) (he : enteringRun.eval g s = 1)
    (hk : (entered.eval g s).extractLsb' 0 3 = 5) :
    (body.step g s) .payload = shiftOperand (parameter0.eval g s)[2]
      (operand (start.eval g s == 1) (g (.base .data)) (s .payload)) := by
  simp [Circuit.step, body, PairedController.next, Expr.eval, isKind, kind,
    hr, he, hk, shifted_value g s h, operand_value g s h]

theorem payload_held (g : Values GraphInput) (s : Values Register)
    (hr : resetting.eval g s = 0) (he : enteringRun.eval g s = 0)
    (hs : start.eval g s = 0) : (body.step g s) .payload = s .payload := by
  simp [Circuit.step, body, PairedController.next, Expr.eval, hr, he, hs]

theorem payload_reset (g : Values GraphInput) (s : Values Register)
    (hr : resetting.eval g s = 1) : (body.step g s) .payload = 0 := by
  simp [Circuit.step, body, PairedController.next, Expr.eval, hr]

theorem payload_accepted_start_not_shift (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hr : resetting.eval g s = 0) (hs : start.eval g s = 1)
    (hk : (entered.eval g s).extractLsb' 0 3 ≠ 5) :
    (body.step g s) .payload = (g (.base .data)).extractLsb' 0 8 := by
  simp [Circuit.step, body, PairedController.next, Expr.eval, isKind, kind,
    hr, hs, accepted_start_snapshot g s h hs]
  exact fun _ hshift => False.elim (hk hshift)

theorem levels_enter (g : Values GraphInput) (s : Values Register)
    (ht : stopping.eval g s = 0) (he : enteringRun.eval g s = 1) :
    (body.step g s) .levels = entryLevels.eval g s := by
  simp [Circuit.step, body, PairedController.next, Expr.eval, ht, he]

theorem shift_pin_after_edge (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (ht : stopping.eval g s = 0) (he : enteringRun.eval g s = 1)
    (hk : (entered.eval g s).extractLsb' 0 3 = 5) (pin : Fin 3) :
    ((body.step g s) .levels)[pin.val] =
      if (parameter0.eval g s).extractLsb' 0 2 = BitVec.ofNat 2 pin.val then
        outputBit (parameter0.eval g s)[2]
          (operand (start.eval g s == 1) (g (.base .data)) (s .payload))
      else (entered.eval g s).getLsbD (pin.val + 3) := by
  simpa only [levels_enter g s ht he, operand_value g s h] using shift_levels_bit g s h hk pin

theorem keep_levels_bit (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hk : (entered.eval g s).extractLsb' 0 3 = 6) (pin : Fin 3) :
    (entryLevels.eval g s)[pin.val] =
      if (parameter0.eval g s).getLsbD (pin.val + 6) then (s .levels)[pin.val]
      else (entered.eval g s).getLsbD (pin.val + 3) := by
  simp [entryLevels_wire g s h, entryLevelsExpr, either, isKind, kind, Expr.eval, hk,
    ← BitVec.getLsbD_eq_getElem, Nat.add_comm]
  cases (parameter0.eval g s).getLsbD (pin.val + 6) <;> simp
  done

theorem keep_capture (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hk : (entered.eval g s).extractLsb' 0 3 = 6) :
    samples (captured.eval g s) = Engine.Reactive.capture (samples (entrySamples.eval g s))
      (Execution.getCapture ((parameter0.eval g s).extractLsb' 0 6)) (g (.base .incoming)) := by
  simp [captured_wire g s h, capturedExpr, either, isKind, kind, Expr.eval, hk,
    capture_samples, incoming_value g s h]

theorem keep_pin_after_edge (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (ht : stopping.eval g s = 0) (he : enteringRun.eval g s = 1)
    (hk : (entered.eval g s).extractLsb' 0 3 = 6) (pin : Fin 3) :
    ((body.step g s) .levels)[pin.val] =
      if (parameter0.eval g s).getLsbD (pin.val + 6) then (s .levels)[pin.val]
      else (entered.eval g s).getLsbD (pin.val + 3) := by
  simpa only [levels_enter g s ht he] using keep_levels_bit g s h hk pin

theorem enteringRun_implies_entering (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (he : enteringRun.eval g s = 1) :
    entering.eval g s = 1 := by
  exact ((PairedUpload.bit_and_one _ _).mp ((enteringRun_wire g s h).symm.trans he)).1

theorem keep_capture_after_edge (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hr : resetting.eval g s = 0) (hc : commit.eval g s = 0)
    (he : enteringRun.eval g s = 1) (hk : (entered.eval g s).extractLsb' 0 3 = 6) :
    samples ((body.step g s) .samples) =
      Engine.Reactive.capture (samples (entrySamples.eval g s))
        (Execution.getCapture ((parameter0.eval g s).extractLsb' 0 6)) (g (.base .incoming)) := by
  simp [Circuit.step, body, PairedController.next, either, Expr.eval, hr, hc, he,
    enteringRun_implies_entering g s h he, keep_capture g s h hk]

theorem busy_start_zero (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s) (hb : busy.eval g s = 1) :
    start.eval g s = 0 := by
  simp [start_wire g s h, startExpr, PairedUpload.accepting_value g s h,
    PairedUpload.inputs, Loader.enabled, Expr.eval, both, cmd, hb]

theorem payload_busy_hold (g : Values GraphInput) (s : Values Register)
    (h : PairedSemantics.Equations bindings g s)
    (hr : resetting.eval g s = 0) (he : enteringRun.eval g s = 0)
    (hb : busy.eval g s = 1) : (body.step g s) .payload = s .payload := by
  exact payload_held g s hr he (busy_start_zero g s h hb)

theorem retained_shift_payload (n : Netlist Register (SramController.Out Loader.Machine.Output) Input)
    (hn : PairedController.core = .ok n) (i : Values Input) (s : Values Register)
    (hr : resetting.eval (PairedSemantics.inputs bindings i s) s = 0)
    (he : enteringRun.eval (PairedSemantics.inputs bindings i s) s = 1)
    (hk : (entered.eval (PairedSemantics.inputs bindings i s) s).extractLsb' 0 3 = 5) :
    (n.step i s) .payload =
      shiftOperand (parameter0.eval (PairedSemantics.inputs bindings i s) s)[2]
        (operand (start.eval (PairedSemantics.inputs bindings i s) s == 1) (i (.base .data)) (s .payload)) := by
  exact (congrArg (fun state : Values Register => state .payload)
    (PairedSemantics.core_correct n hn i s).1).trans
      (payload_enter_shift _ s (PairedSemantics.inputs_equations bindings
        PairedSemantics.bindings_ordered i s) hr he hk)

end Pinwheel.Hardware.Storage.PairedResidentEffects
