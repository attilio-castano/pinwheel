import Pinwheel.Hardware.Processor.CoreCircuit
import Pinwheel.Hardware.Processor.RV32I.ExecuteCircuitProofs

namespace Pinwheel.Hardware.Processor.CoreCircuit

def architecture (s : Values Register) : RV32I.Semantics.State :=
  ⟨s pc, Hardware.RegisterFile.view (fun r => s (.left r))⟩

theorem readOperand_eval (address : E 5) (i : Values CoreInterface.Input) (s : Values Register) :
    (readOperand address).eval i s = RV32I.Semantics.read (architecture s).registers (address.eval i s) := by
  simp only [readOperand, Execution.readTree_correct, registerWord, architecture, RV32I.Semantics.read]
  split <;> rfl

theorem execution_eval (i : Values CoreInterface.Input) (s : Values Register) (field : RV32I.ExecuteCircuit.Field b) :
    (execution field).eval i s =
      (RV32I.ExecuteCircuit.project (RV32I.Semantics.step (architecture s) (s instruction))).values field := by
  apply RV32I.ExecuteCircuit.bundle_semantics
  · rfl
  · constructor <;> simp only [readOperand_eval, decoded, RV32I.DecodeCircuit.bundle_eval, Expr.eval]

theorem extendByte_eval (value : E 32) (i : Values CoreInterface.Input) (s : Values Register) :
    (extendByte value).eval i s =
      if (execution .signedLoad).eval i s = 1 then ((value.eval i s).extractLsb' 0 8).signExtend 32
      else ((value.eval i s).extractLsb' 0 8).setWidth 32 := by
  simp only [extendByte, both, Expr.eval]
  rcases BitVec.eq_zero_or_eq_one ((execution .signedLoad).eval i s) with h | h
  all_goals simp [h]
  all_goals bv_normalize
  all_goals simp [BitVec.extractLsb'_extractLsb'_of_le (by decide : 7+1 ≤ 8)] at *

theorem extendHalf_eval (value : E 32) (i : Values CoreInterface.Input) (s : Values Register) :
    (extendHalf value).eval i s =
      if (execution .signedLoad).eval i s = 1 then ((value.eval i s).extractLsb' 0 16).signExtend 32
      else ((value.eval i s).extractLsb' 0 16).setWidth 32 := by
  simp only [extendHalf, both, Expr.eval]
  rcases BitVec.eq_zero_or_eq_one ((execution .signedLoad).eval i s) with h | h
  all_goals simp [h]
  all_goals bv_normalize
  all_goals simp [BitVec.extractLsb'_extractLsb'_of_le (by decide : 15+1 ≤ 16)] at *

theorem loadedValue_load (i : Values CoreInterface.Input) (s : Values Register)
    (context : RV32I.Semantics.Context) (op : RV32I.LoadOp) (dest : RV32I.Register) (address : BitVec 32)
    (h : RV32I.Semantics.step (architecture s) (s instruction) =
      .pending (.load context op dest address)) :
    loadedValue.eval i s = RV32I.Semantics.loadValue op (replyData.eval i s) := by
  cases op <;> simp [loadedValue, Expr.eval, extendByte_eval, extendHalf_eval, execution_eval, h,
    RV32I.ExecuteCircuit.project, RV32I.ExecuteCircuit.loading, RV32I.ExecuteCircuit.Result.values,
    RV32I.ExecuteCircuit.sizeCode, RV32I.Semantics.loadSize, RV32I.Semantics.loadSigned, RV32I.Semantics.loadValue]

end Pinwheel.Hardware.Processor.CoreCircuit
