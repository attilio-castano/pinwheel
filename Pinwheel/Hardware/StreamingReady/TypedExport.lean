import Pinwheel.Hardware.StreamingReady.CoreEmit
import Pinwheel.Hardware.Streaming.FrontendEmit
import Pinwheel.Hardware.TypedModule

/-! Typed interfaces for the two source circuits used by the sampled-ready
package, in the same order as the existing artifact ABI. -/
namespace Pinwheel.Hardware.StreamingReady.TypedExport

private def coreInputPosition : Core.Input w → Fin Core.inputs.size
  | .initialize => ⟨0, by decide⟩
  | .command => ⟨1, by decide⟩
  | .address => ⟨2, by decide⟩
  | .word => ⟨3, by decide⟩
  | .count => ⟨4, by decide⟩
  | .idleLevels => ⟨5, by decide⟩
  | .idleEnabled => ⟨6, by decide⟩
  | .startCount => ⟨7, by decide⟩
  | .expectedGeneration => ⟨8, by decide⟩
  | .expectedTransfer => ⟨9, by decide⟩
  | .txPush => ⟨10, by decide⟩
  | .txData => ⟨11, by decide⟩
  | .txBits => ⟨12, by decide⟩
  | .rxPop => ⟨13, by decide⟩
  | .rawInputs => ⟨14, by decide⟩

private def coreOutputPosition : Core.Output w → Fin Core.outputs.size
  | .valid => ⟨0, by decide⟩
  | .busy => ⟨1, by decide⟩
  | .retained => ⟨2, by decide⟩
  | .pending => ⟨3, by decide⟩
  | .rejected => ⟨4, by decide⟩
  | .stalled => ⟨5, by decide⟩
  | .fault => ⟨6, by decide⟩
  | .waitingTX => ⟨7, by decide⟩
  | .waitingRX => ⟨8, by decide⟩
  | .generation => ⟨9, by decide⟩
  | .transfer => ⟨10, by decide⟩
  | .phase => ⟨11, by decide⟩
  | .pc => ⟨12, by decide⟩
  | .remaining => ⟨13, by decide⟩
  | .total => ⟨14, by decide⟩
  | .levels => ⟨15, by decide⟩
  | .enabled => ⟨16, by decide⟩
  | .txFree => ⟨17, by decide⟩
  | .txQueued => ⟨18, by decide⟩
  | .rxQueued => ⟨19, by decide⟩
  | .rxData => ⟨20, by decide⟩
  | .rxBits => ⟨21, by decide⟩
  | .txAccepted => ⟨22, by decide⟩
  | .txConsumed => ⟨23, by decide⟩
  | .rxProduced => ⟨24, by decide⟩
  | .rxPopped => ⟨25, by decide⟩
  | .stage1 => ⟨26, by decide⟩
  | .stage2 => ⟨27, by decide⟩

private theorem coreRegistersSize1 : (Core.registers 1).size = 105 := by decide +kernel
private theorem coreRegistersSize2 : (Core.registers 2).size = 113 := by decide +kernel

private theorem coreRegisterIndexLt (supported : a = 1 ∨ a = 2) (r : Core.Register a w) :
    Core.registerIndex r < (Core.registers a).size := by
  rcases supported with rfl | rfl
  all_goals
    cases r <;> simp [Core.registerIndex, Streaming.Core.registerIndex,
      coreRegistersSize1, coreRegistersSize2]
  all_goals
    rename_i address
    have h := address.isLt
    simp at h
    omega
  done

private def coreRegisterPosition (supported : a = 1 ∨ a = 2) (r : Core.Register a w) :
    Fin (Core.registers a).size :=
  ⟨Core.registerIndex r, coreRegisterIndexLt supported r⟩

set_option maxHeartbeats 2000000 in
private theorem coreRegisterAtPosition (supported : a = 1 ∨ a = 2) (r : Core.Register a w) :
    (Core.registers a)[(coreRegisterPosition supported r).val] = ⟨w, r⟩ := by
  rcases supported with rfl | rfl
  all_goals
    cases r <;> simp [coreRegisterPosition, Core.registerIndex, Streaming.Core.registerIndex,
      Core.registers, Streaming.Core.registers]
  all_goals
    first
    | rename_i address
      have h : address.toNat < 64 := address.isLt
      simp [h]
    | rename_i address
      obtain ⟨⟨value, bound⟩⟩ := address
      simp at bound
      have h : value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;> first | omega | simp [List.finRange_succ]
    | simp [List.finRange_succ]
  done

private theorem frontendInputsSize : Streaming.Frontend.inputs.size = 33 := by
  simp [Streaming.Frontend.inputs, Streaming.Core.outputs]

private theorem frontendOutputsSize : Streaming.Frontend.outputs.size = 17 := by
  simp [Streaming.Frontend.outputs, Streaming.Core.inputs]

private def frontendInputPosition : Streaming.Frontend.Input w → Fin Streaming.Frontend.inputs.size
  | .initialize => ⟨0, by simp [frontendInputsSize]⟩
  | .sck => ⟨1, by simp [frontendInputsSize]⟩
  | .csn => ⟨2, by simp [frontendInputsSize]⟩
  | .mosi => ⟨3, by simp [frontendInputsSize]⟩
  | .rawInputs => ⟨4, by simp [frontendInputsSize]⟩
  | .status p => ⟨5 + (coreOutputPosition p).val, by
      have h := (coreOutputPosition p).isLt
      change _ < 28 at h
      rw [frontendInputsSize]
      omega⟩

private def frontendOutputPosition :
    Streaming.Frontend.Output w → Fin Streaming.Frontend.outputs.size
  | .core p => ⟨(coreInputPosition p).val, by
      have h := (coreInputPosition p).isLt
      change _ < 15 at h
      rw [frontendOutputsSize]
      omega⟩
  | .miso => ⟨15, by simp [frontendOutputsSize]⟩
  | .ready => ⟨16, by simp [frontendOutputsSize]⟩

private def frontendRegisterPosition (r : Streaming.Frontend.Register w) :
    Fin Streaming.Frontend.registers.size :=
  ⟨Streaming.Frontend.registerIndex r, by cases r <;> decide⟩

set_option maxRecDepth 4096 in
private theorem coreRegisterLabelsUnique (a : Nat) (supported : a = 1 ∨ a = 2)
    (i j : Fin (Core.registers a).size)
    (h : Core.registerLabel (Core.registers a)[i.val].2 =
      Core.registerLabel (Core.registers a)[j.val].2) :
    i = j := by
  let labels := (Core.registers a).toList.map (fun p => Core.registerLabel p.2)
  have nodup : labels.Nodup := by
    rcases supported with rfl | rfl <;> decide +kernel
  have hi : i.val < labels.length := by simp [labels]
  have hj : j.val < labels.length := by simp [labels]
  apply Fin.ext
  apply (List.getElem?_inj hi nodup).mp
  simpa [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, labels] using h
  done

def core (a : Nat) (supported : a = 1 ∨ a = 2) :
    TypedModule Core.Input (Core.Register a) Core.Output where
  name := s!"pinwheel_streaming_ready_core_d{2^a}"
  circuit := Core.circuit a
  inputs := {
    size := Core.inputs.size
    signal := fun k => Core.inputs[k.val]
    position := coreInputPosition
    signal_position := by intro w p; cases p <;> rfl
    label := Core.inputLabel
    unique := by decide +kernel }
  registers := {
    size := (Core.registers a).size
    signal := fun k => (Core.registers a)[k.val]
    position := coreRegisterPosition supported
    signal_position := coreRegisterAtPosition supported
    label := Core.registerLabel
    unique := coreRegisterLabelsUnique a supported }
  outputs := {
    size := Core.outputs.size
    signal := fun k => Core.outputs[k.val]
    position := coreOutputPosition
    signal_position := by intro w p; cases p <;> rfl
    label := Core.outputLabel
    unique := by decide +kernel }

def frontend : TypedModule Streaming.Frontend.Input Streaming.Frontend.Register
    Streaming.Frontend.Output where
  name := "pinwheel_streaming_quad_frontend"
  circuit := Streaming.Frontend.circuit
  inputs := {
    size := Streaming.Frontend.inputs.size
    signal := fun k => Streaming.Frontend.inputs[k.val]
    position := frontendInputPosition
    signal_position := by
      intro w p
      cases p <;> simp [Streaming.Frontend.inputs, frontendInputPosition]
      rename_i status
      cases status <;> simp [Streaming.Core.outputs, coreOutputPosition]
    label := Streaming.Frontend.inputLabel
    unique := by decide +kernel }
  registers := {
    size := Streaming.Frontend.registers.size
    signal := fun k => Streaming.Frontend.registers[k.val]
    position := frontendRegisterPosition
    signal_position := by intro w p; cases p <;> rfl
    label := Streaming.Frontend.registerLabel
    unique := by decide +kernel }
  outputs := {
    size := Streaming.Frontend.outputs.size
    signal := fun k => Streaming.Frontend.outputs[k.val]
    position := frontendOutputPosition
    signal_position := by
      intro w p
      cases p with
      | core input => cases input <;> simp [Streaming.Frontend.outputs, frontendOutputPosition,
          Streaming.Core.inputs, coreInputPosition]
      | miso | ready => simp [Streaming.Frontend.outputs, frontendOutputPosition,
          Streaming.Core.inputs]
    label := Streaming.Frontend.outputLabel
    unique := by decide +kernel }

end Pinwheel.Hardware.StreamingReady.TypedExport
