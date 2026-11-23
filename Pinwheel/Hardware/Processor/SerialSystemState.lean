import Pinwheel.Hardware.Processor.SerialSystemWiring

/-! Exact raw state composition. Both views refer to the same MMIO registers;
no ownership assumption is needed for these circuit equalities. -/
namespace Pinwheel.Hardware.Processor.SerialSystemCircuit
open SerialSystemInterface
set_option backward.isDefEq.respectTransparency false

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw)
  (romFits : rw ≤ 30) (ramFits : aw ≤ 30) (d : Uart.Timing)

theorem system_state_step (i : Values (Input aw)) (s : Values (Register aw d)) :
    @Eq (Values (LoadableSystem.Register aw))
      (systemState ((circuit layout rom romFits ramFits d).step i s))
      ((LoadableSystem.circuit layout rom romFits ramFits).step (loadablePins layout d i s) (systemState s)) := by
  funext b r
  simp only [systemState,system,Circuit.step,circuit,Expr.eval_bind,Expr.eval]
  rfl

theorem uart_state_step (i : Values (Input aw)) (s : Values (Register aw d)) :
    @Eq (Values (Uart.Structural.Register d))
      (uartState ((circuit layout rom romFits ramFits d).step i s))
      (SerialCircuit.uartState ((SerialCircuit.circuit d).step (serialPins layout i s) (serialState s))) := by
  funext b r
  simp only [uartState,uart,Circuit.step,circuit,Expr.eval_bind,Expr.eval]
  rfl

/-- Every next-state bit of the shared serial subsystem is exactly the proved
SerialCircuit transition, including the single shared MMIO bank. -/
theorem serial_state_step (i : Values (Input aw)) (s : Values (Register aw d)) :
    @Eq (Values (SerialCircuit.Register d))
      (serialState ((circuit layout rom romFits ramFits d).step i s))
      ((SerialCircuit.circuit d).step (serialPins layout i s) (serialState s)) := by
  funext b r
  cases r with
  | left r =>
    change SystemCircuit.mmioValues (systemState ((circuit layout rom romFits ramFits d).step i s)) r = _
    rw [system_state_step]
    have loader := congrFun (congrFun (LoadableSystem.loader_mmio_step layout rom romFits ramFits
      (loadablePins layout d i s) (systemState s)) b) r
    have base := congrFun (congrFun (SystemCircuit.mmio_step layout rom romFits ramFits
      (LoadableSystem.systemPins (loadablePins layout d i s)) (systemState s)) b) r
    refine loader.trans (base.trans ?_)
    have pins : @Eq (Values MmioInterface.Input)
        (SystemCircuit.mmioPins layout (LoadableSystem.systemPins (loadablePins layout d i s)) (systemState s))
        (SerialCircuit.boundMmioPins d (serialPins layout i s) (serialState s)) :=
      funext fun _ => funext fun p => shared_mmio_pins layout d i s p
    rw [pins]
    exact (SerialCircuit.step_mmio _ _ r).symm
  | right r => exact congrFun (congrFun (uart_state_step layout rom romFits ramFits d i s) b) r

theorem serial_view (s : Values (Register aw d)) :
    SerialCircuit.view (serialState s) = SerialSystemModel.serialState (view s) := rfl

theorem view_valid (s : Values (Register aw d)) (h : Valid layout rom d s) :
    SerialSystemModel.Valid layout rom d (view s) :=
  ⟨h.1.2,SerialCircuit.view_valid _ h.2⟩

theorem preserved (i : Values (Input aw)) (s : Values (Register aw d))
    (h : Valid layout rom d s) : Valid layout rom d ((circuit layout rom romFits ramFits d).step i s) := by
  constructor
  · change SystemCircuit.Valid layout rom (systemState _)
    rw [system_state_step]
    exact LoadableSystem.preserved layout rom romFits ramFits _ _ h.1
  · change SerialCircuit.Valid d (serialState _)
    rw [serial_state_step]
    exact SerialCircuit.valid_step _ _ h.2

theorem system_output (i : Values (Input aw)) (s : Values (Register aw d)) (o : LoadableSystem.Output b) :
    (circuit layout rom romFits ramFits d).observe i s (.left o) =
      (LoadableSystem.circuit layout rom romFits ramFits).observe (loadablePins layout d i s) (systemState s) o := by
  simp only [Circuit.observe,circuit,Expr.eval_bind,Expr.eval]
  rfl

theorem uart_output (i : Values (Input aw)) (s : Values (Register aw d)) (o : Uart.Physical.Output b) :
    (circuit layout rom romFits ramFits d).observe i s (.right o) =
      (SerialCircuit.circuit d).observe (serialPins layout i s) (serialState s) (.right o) :=
  serialOutput_eval layout d i s _

end Pinwheel.Hardware.Processor.SerialSystemCircuit
