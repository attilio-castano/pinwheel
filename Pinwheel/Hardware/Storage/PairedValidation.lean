import Pinwheel.Hardware.Storage.PairedController

/-! An opt-in paired controller with upload-only validation reads. The retained
controller remains the comparison implementation. Only the push computation
changes; state, execution lookup, wrappers and image format remain identical. -/
namespace Pinwheel.Hardware.Storage.PairedValidation
open Pinwheel.Hardware Pinwheel.Hardware.Storage
open PairedController

/-- Admission reads the inactive bank using the uploaded token, never SRAM Q. -/
def validationLookup (address : E 5) : E 20 := .mux inactive
  (Execution.readTree 5 (fun k => .reg (.parameter true k)) address)
  (Execution.readTree 5 (fun k => .reg (.parameter false k)) address)

def validationInput : {w : Nat} → GraphInput w → E w
  | _, .node .parameter0 => .concat (.lit (0 : BitVec 44))
      (validationLookup (.slice 17 5 (by decide) data))
  | _, .node .parameter1 => .concat (.lit (0 : BitVec 44))
      (validationLookup (.slice 49 5 (by decide) data))
  | _, p => .input p

def validationGood : E 1 := PairedController.goodExpr.bind validationInput (.reg)

def pushInput : {w : Nat} → GraphInput w → E w
  | _, .node .good => .concat (.lit (0 : BitVec 63)) validationGood
  | _, p => .input p

def isolatedPush : E 1 := PairedController.pushExpr.bind pushInput (.reg)

private theorem one_bit (b : BitVec 1) : b = 0 ∨ b = 1 := by bv_omega

private theorem gated_congr (a b c d x y : BitVec 1)
    (h : a = 1 → b = 1 → c = 1 → x = y) :
    a &&& (b &&& (c &&& (d &&& x))) = a &&& (b &&& (c &&& (d &&& y))) := by
  rcases one_bit a with ha | ha
  all_goals rcases one_bit b with hb | hb
  all_goals rcases one_bit c with hc | hc
  all_goals simp_all

private theorem isolatedPush_eval (i : Values GraphInput) (s : Values Register) :
    isolatedPush.eval i s = accepting.eval i s &&&
      ((cmd 2).eval i s &&& (s .pending &&& ((below 290).eval i s &&& validationGood.eval i s))) := by
  simp only [isolatedPush, pushExpr, Expr.eval_bind, both, accepting, cmd, below, good,
    Expr.eval, pushInput, BitVec.extractLsb'_append_eq_right]
  rfl

private theorem validationGood_matches (i : Values GraphInput) (s : Values Register)
    (h0 : parameter0.eval i s = (validationLookup (.slice 17 5 (by decide) data)).eval i s)
    (h1 : parameter1.eval i s = (validationLookup (.slice 49 5 (by decide) data)).eval i s) :
    validationGood.eval i s = goodExpr.eval i s := by
  simp only [validationGood, Expr.eval_bind, goodExpr, tokenValid, terminal, isKind, kind,
    allowed, captureValid, both, either, below, atCursor, parameter0, parameter1, data,
    Expr.eval, validationInput, BitVec.extractLsb'_append_eq_right] at h0 h1 ⊢
  simp only [h0, h1]
  rfl

/-- Local contract for the sole changed graph node. The premises are the
upstream graph equations; saved-RTL checks cover their actual emitted wiring. -/
theorem isolatedPush_matches (i : Values GraphInput) (s : Values Register)
    (hgood : good.eval i s = goodExpr.eval i s)
    (hread : validatingExpr.eval i s = 1 →
      parameter0.eval i s = (validationLookup (.slice 17 5 (by decide) data)).eval i s ∧
      parameter1.eval i s = (validationLookup (.slice 49 5 (by decide) data)).eval i s) :
    isolatedPush.eval i s = pushExpr.eval i s := by
  rw [isolatedPush_eval]
  simp only [pushExpr, both, Expr.eval, hgood]
  apply gated_congr
  intro ha hc hp
  by_cases hlo : (s .cursor).toNat < 32
  · simp [validationGood, Expr.eval_bind, goodExpr, below, Expr.eval, validationInput, hlo, data]
  · by_cases hhi : (s .cursor).toNat < 289
    · have hv : validatingExpr.eval i s = 1 := by
        simp [validatingExpr, both, Expr.eval, ha, hp, below, hlo, hhi, cmd] at hc ⊢
        simp [hc]
      exact validationGood_matches i s (hread hv).1 (hread hv).2
    · have hmiddle : ¬ (s .cursor).toNat < 288 := by omega
      have hboot : s .cursor ≠ 288#9 := by bv_omega
      simp [validationGood, Expr.eval_bind, goodExpr, below, atCursor, both, Expr.eval,
        validationInput, hlo, hmiddle, hboot, data]
      rfl

/-- These equations are exactly the named upstream bindings used by the
retained controller. They permit arbitrary inputs and arbitrary register values. -/
structure UpstreamEquations (i : Values GraphInput) (s : Values Register) : Prop where
  validating : PairedController.validating.eval i s = validatingExpr.eval i s
  bank : parameterBank.eval i s = parameterBankExpr.eval i s
  index0 : parameterIndex0.eval i s = parameterIndex0Expr.eval i s
  index1 : parameterIndex1.eval i s = parameterIndex1Expr.eval i s
  parameter0 : PairedController.parameter0.eval i s = parameter0Expr.eval i s
  parameter1 : PairedController.parameter1.eval i s = parameter1Expr.eval i s
  good : PairedController.good.eval i s = goodExpr.eval i s

theorem validation_reads_match (i : Values GraphInput) (s : Values Register)
    (h : UpstreamEquations i s) (hv : validatingExpr.eval i s = 1) :
    parameter0.eval i s = (validationLookup (.slice 17 5 (by decide) data)).eval i s ∧
    parameter1.eval i s = (validationLookup (.slice 49 5 (by decide) data)).eval i s := by
  simp only [h.parameter0, h.parameter1, parameter0Expr, parameter1Expr, lookup,
    validationLookup, Expr.eval, Execution.readTree_correct, h.bank, h.index0, h.index1,
    parameterBankExpr, parameterIndex0Expr, parameterIndex1Expr, index, h.validating, hv,
    ite_true]
  simp [BitVec.extractLsb'_extractLsb'_of_le]

/-- The replacement preserves the push decision under the original upstream
binding equations. This is a local expression theorem, not a compiler theorem. -/
theorem isolatedPush_correct (i : Values GraphInput) (s : Values Register)
    (h : UpstreamEquations i s) : isolatedPush.eval i s = pushExpr.eval i s := by
  exact isolatedPush_matches i s h.good (validation_reads_match i s h)

def bindings : List (Computation × E 64) := PairedController.bindings.map fun (name,e) =>
  (name, if name = .push then .concat (.lit (0 : BitVec 63)) isolatedPush else e)

def core : Except String (Netlist Register (SramController.Out Loader.Machine.Output) Input) :=
  construct (.input) (fun _ => .lit 0) [] bindings

def coreText : Except String String := match core with
  | .error e => .error e
  | .ok n => Netlist.moduleText "pinwheel_paired_core_controller" n
      (inputs Loader.Machine.inputs) registers (outputs Loader.Machine.outputs)
      (SramAssembly.inputLabel Loader.Machine.inputLabel) label (SramAssembly.outputLabel Loader.Machine.outputLabel)

def chipText : Except String String := match core with
  | .error e => .error e
  | .ok n =>
    let chip := SramAssembly.observer.wrap ((SramController.bypass Chip.pinMap).wrap
      ((SramController.bypass Feeder.sampler).wrap ((SramController.bypass Serial.receiver).wrap n)))
    Netlist.moduleText "pinwheel_paired_controller" chip
      (inputs Backend.Policy.chipInputs) fullRegisters (outputs Backend.Policy.chipOutputs)
      (SramAssembly.inputLabel Backend.Policy.chipInputLabel) fullLabel
      (SramAssembly.outputLabel Backend.Policy.chipOutputLabel)

end Pinwheel.Hardware.Storage.PairedValidation
