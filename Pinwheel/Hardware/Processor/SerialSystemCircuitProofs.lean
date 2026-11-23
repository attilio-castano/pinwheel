import Pinwheel.Hardware.Processor.SerialSystemConnection

/-! Complete typed cycle refinement for the shared-MMIO sampled-wire MCU.
The validity predicate is exactly the existing system validity and serial
ownership/counter validity, with no new instruction/provider assumptions. -/
namespace Pinwheel.Hardware.Processor.SerialSystemCircuit
open SerialSystemInterface
set_option backward.isDefEq.respectTransparency false

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (d : Uart.Timing)

theorem model_system_decode (i : Values (Input aw)) (s : SerialSystemModel.State aw) :
    SystemCircuit.decode (LoadableSystem.systemPins (modelLoadablePins layout rom d i s)) =
      SerialSystemModel.systemInput layout rom d (decode i) s := by
  change SystemModel.Input.mk _ _ _ _ _ = SystemModel.Input.mk _ _ _ _ _
  congr 1
  · change (i reset ||| i mode == 1) = ((i reset == 1) || (i mode == 1))
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;>
      rcases BitVec.eq_zero_or_eq_one (i mode) with hm | hm <;> simp [hr,hm]
  · exact SerialInterface.ofBool_beq _
  · change (if BitVec.ofBool (SerialSystemModel.frontend layout rom d (decode i) s).arrival.isSome = 1
      then some ((SerialSystemModel.frontend layout rom d (decode i) s).arrival.getD 0) else none) = _
    cases (SerialSystemModel.frontend layout rom d (decode i) s).arrival <;> rfl
  · exact SerialInterface.ofBool_beq _

theorem model_system_step (i : Values (Input aw)) (s : SerialSystemModel.State aw) :
    (LoadableSystem.spec layout rom).step (modelLoadablePins layout rom d i s) s.system =
      (SerialSystemModel.step layout rom d (decode i) s).system := by
  have accepted : LoadableSystem.Accepted (modelLoadablePins layout rom d i s) ↔ SerialSystemModel.Accepted (decode i) := by
    change (i mode = 1 ∧ i reset = 0 ∧ i valid = 1) ↔
      ((i mode == 1) = true ∧ (i reset == 1) = false ∧ (i valid == 1) = true)
    rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;> simp [hr]
  simp only [LoadableSystem.spec,SystemCircuit.spec,model_system_decode,SerialSystemModel.step,accepted]
  rfl

theorem view_step (i : Values (Input aw)) (s : Values (Register aw d)) (h : Valid layout rom d s) :
    view ((circuit layout rom romFits ramFits d).step i s) =
      (spec layout rom d).step i (view s) := by
  change SerialSystemModel.State.mk _ _ = SerialSystemModel.State.mk _ _
  congr 1
  · rw [system_state_step,LoadableSystem.view_step layout rom romFits ramFits _ _ h.1,
      loadablePins_model layout rom d i s h]
    exact model_system_step layout rom d i (view s)
  · rw [uart_state_step]
    have next := congrArg SerialModel.State.uart (SerialCircuit.view_step (serialPins layout i s) (serialState s) h.2.1)
    exact next.trans (uart_step_model layout rom d i s h.1.1)

theorem output_eq (i : Values (Input aw)) (s : Values (Register aw d)) (h : Valid layout rom d s)
    (o : Output b) :
    (circuit layout rom romFits ramFits d).observe i s o = (spec layout rom d).observe i (view s) o := by
  cases o with
  | left o =>
    rw [system_output,LoadableSystem.output_eq layout rom romFits ramFits _ _ h.1,
      loadablePins_model layout rom d i s h]
    rfl
  | right o => exact uart_output_model layout rom d i s h o

def implementation : DecodedImplementation (circuit layout rom romFits ramFits d) (spec layout rom d) where
  Valid := Valid layout rom d
  view := view
  preserved := preserved layout rom romFits ramFits d
  step_eq := view_step layout rom romFits ramFits d
  output_eq i s h {_} o := output_eq layout rom romFits ramFits d i s h o

end Pinwheel.Hardware.Processor.SerialSystemCircuit
