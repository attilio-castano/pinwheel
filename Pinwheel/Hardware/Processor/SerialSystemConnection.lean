import Pinwheel.Hardware.Processor.SerialSystemState

/-! Logical connection of the actual UART pins. Request decoding is used only
away from effective reset; reset directly cancels serial service, independently
of arbitrary inactive CPU request fields. -/
namespace Pinwheel.Hardware.Processor.SerialSystemCircuit
open SerialSystemInterface
set_option backward.isDefEq.respectTransparency false

@[simp] theorem reset_decode (i : Values (Input aw)) (s : Values (Register aw d)) :
    (quietPins i s SystemInterface.reset == 1) = SerialSystemModel.effectiveReset (decode i) := by
  rcases BitVec.eq_zero_or_eq_one (i reset) with hr | hr <;>
    rcases BitVec.eq_zero_or_eq_one (i mode) with hm | hm <;>
    simp [quiet_reset,SerialSystemModel.effectiveReset,decode,hr,hm]

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)

theorem serial_decode (i : Values (Input aw)) (s : Values (Register aw d))
    (hr : i reset ||| i mode = 0) (h : CoreCircuit.Valid (SystemCircuit.coreValues (systemState s))) :
    SerialInterface.decode (serialPins layout i s) =
      SerialSystemModel.serialInput layout rom (decode i) (view s) := by
  have pins : @Eq (Values MmioInterface.Input) (SerialInterface.cpuPins (serialPins layout i s))
      (SystemCircuit.mmioPins layout (quietPins i s) (systemState s)) :=
    funext fun _ => funext fun p => serial_cpu_pins layout i s p
  have decoded := SystemCircuit.mmioPins_decode layout rom (quietPins i s) (systemState s)
    (by simpa using hr) h
  simp only [SerialInterface.decode,pins,decoded,SystemModel.mmioInput,SystemCircuit.decode,
    reset_decode,SerialSystemModel.serialInput]
  rfl

theorem serial_reset_decode (i : Values (Input aw)) (s : Values (Register aw d)) :
    (SerialInterface.decode (serialPins layout i s)).reset = SerialSystemModel.effectiveReset (decode i) := by
  change (serialPins layout i s SerialInterface.reset == 1) = _
  rw [serial_reset]
  simpa only [quiet_reset] using reset_decode i s

/-- Reset cancels the UART regardless of masked or retained offer metadata. -/
theorem uart_observe_model (i : Values (Input aw)) (s : Values (Register aw d))
    (h : CoreCircuit.Valid (SystemCircuit.coreValues (systemState s))) :
    Uart.observe d (SerialModel.uartInput (SerialInterface.decode (serialPins layout i s))
      (SerialCircuit.view (serialState s))) (SerialCircuit.view (serialState s)).uart =
      SerialSystemModel.frontend layout rom d (decode i) (view s) := by
  rcases BitVec.eq_zero_or_eq_one (i reset ||| i mode) with hr | hr
  · rw [serial_decode layout rom d i s hr h,serial_view]
    rfl
  · have resetTrue : SerialSystemModel.effectiveReset (decode i) = true := by
      rw [←reset_decode i s,quiet_reset,hr]; rfl
    have decodedReset : (SerialInterface.decode (serialPins layout i s)).reset = true :=
      (serial_reset_decode layout d i s).trans resetTrue
    simp only [SerialSystemModel.frontend,SerialModel.uartInput,Uart.reset_output,
      decodedReset,SerialSystemModel.serialInput,resetTrue]


theorem uart_output_model (i : Values (Input aw)) (s : Values (Register aw d))
    (h : Valid layout rom d s) (o : Uart.Physical.Output b) :
    (serialOutput layout d (.right o)).eval i s =
      Uart.Physical.outputValues (SerialSystemModel.frontend layout rom d (decode i) (view s)) o := by
  rw [serialOutput_eval]
  change (SerialCircuit.uartOutput d o).eval (serialPins layout i s) (serialState s) = _
  rw [SerialCircuit.uart_output_eval _ _ h.2.1,uart_observe_model layout rom d i s h.1.1]

/-- Complete physical/provider input equality: every returned pulse/data pin is
from the actual UART observation, not a separately recomputed device state. -/
theorem loadablePins_model (i : Values (Input aw)) (s : Values (Register aw d))
    (h : Valid layout rom d s) :
    @Eq (Values (LoadableSystem.Input aw)) (loadablePins layout d i s)
      (modelLoadablePins layout rom d i (view s)) := by
  funext b p
  match b,p with
  | _, .left (.at ⟨0,_⟩) | _, .left (.at ⟨1,_⟩) => rfl
  | _, .left (.at ⟨2,_⟩) | _, .left (.at ⟨3,_⟩) | _, .left (.at ⟨4,_⟩) | _, .left (.at ⟨5,_⟩) =>
    exact uart_output_model layout rom d i s h _
  | _, .left (.at ⟨k+6,bound⟩) => exact False.elim (by change k+6 < 6 at bound; omega)
  | _, .right (.at ⟨0,_⟩) | _, .right (.at ⟨1,_⟩) | _, .right (.at ⟨2,_⟩) | _, .right (.at ⟨3,_⟩) => rfl
  | _, .right (.at ⟨k+4,bound⟩) => exact False.elim (by change k+4 < 4 at bound; omega)

theorem uart_step_model (i : Values (Input aw)) (s : Values (Register aw d))
    (h : CoreCircuit.Valid (SystemCircuit.coreValues (systemState s))) :
    Uart.step d (SerialModel.uartInput (SerialInterface.decode (serialPins layout i s))
      (SerialCircuit.view (serialState s))) (SerialCircuit.view (serialState s)).uart =
      (SerialSystemModel.step layout rom d (decode i) (view s)).uart := by
  rcases BitVec.eq_zero_or_eq_one (i reset ||| i mode) with hr | hr
  · rw [serial_decode layout rom d i s hr h,serial_view]
    rfl
  · have resetTrue : SerialSystemModel.effectiveReset (decode i) = true := by
      rw [←reset_decode i s,quiet_reset,hr]; rfl
    have decodedReset : (SerialInterface.decode (serialPins layout i s)).reset = true :=
      (serial_reset_decode layout d i s).trans resetTrue
    simp only [SerialSystemModel.step,SerialModel.uartInput,Uart.reset_state,
      decodedReset,SerialSystemModel.serialInput,resetTrue]

end Pinwheel.Hardware.Processor.SerialSystemCircuit
