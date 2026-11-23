import Pinwheel.Hardware.Processor.SerialSystemModel

namespace Pinwheel.Hardware.Processor.SerialSystemModel

variable (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)

theorem system_reset (i : SystemModel.Input) (s : SystemModel.State aw) (resetHigh : i.reset = true) :
    SystemModel.step layout rom i s = SystemModel.initial s.ram.memory.contents s.ram.memory.q := by
  simp [SystemModel.step,SystemModel.coreInput,SystemModel.ramInput,SystemModel.mmioInput,
    SystemModel.fetchStep,resetHigh,CoreModel.step,CoreModel.tick,Memory.ByteAdapterModel.step,
    Memory.ByteAdapterModel.command,Memory.SinglePort.step,MmioModel.step,SystemModel.initial]

theorem reset_step (i : Input aw) (s : State aw) (resetHigh : i.reset = true) :
    step layout rom d i s = initial s.system.ram.memory.contents s.system.ram.memory.q := by
  have effective : effectiveReset i = true := by simp [effectiveReset,resetHigh]
  have sys := system_reset layout rom (systemInput layout rom d i s) s.system effective
  simp only [step,sys]
  simp [Accepted,resetHigh,initial,SerialModel.uartInput,serialInput,effective,Uart.step,Uart.txStep,Uart.rxStep,Uart.initial]

/-- Holding loader ownership cancels CPU/UART protocol before changing one RAM
word. The previous Q is retained even when the addressed word is rewritten. -/
theorem loading_step (i : Input aw) (s : State aw) (modeHigh : i.mode = true) :
    step layout rom d i s = initial
      (fun k => if i.reset = false ∧ i.valid = true ∧ i.address = k then i.data else s.system.ram.memory.contents k)
      s.system.ram.memory.q := by
  have effective : effectiveReset i = true := by simp [effectiveReset,modeHigh]
  have sys := system_reset layout rom (systemInput layout rom d i s) s.system effective
  simp only [step,sys]
  cases hr : i.reset <;> cases hv : i.valid <;>
    simp [Accepted,modeHigh,hr,hv,patch,initial,SerialModel.uartInput,serialInput,effective,
      Uart.step,Uart.txStep,Uart.rxStep,Uart.initial,SystemModel.initial]

theorem preserved (i : Input aw) (s : State aw) (valid : Valid layout rom d s) :
    Valid layout rom d (step layout rom d i s) := by
  constructor
  · by_cases accepted : Accepted i
    · rw [loading_step layout rom d i s accepted.1]
      exact SystemModel.initial_valid _ _ _ _
    · change SystemModel.Valid layout rom (if Accepted i then _ else _)
      rw [if_neg accepted]
      exact SystemModel.preserved layout rom (systemInput layout rom d i s) s.system valid.1
  · rw [serial_step]
    exact SerialModel.step_valid d _ _ valid.2.1

theorem reset_valid (i : Input aw) (s : State aw) (resetHigh : i.reset = true) :
    Valid layout rom d (step layout rom d i s) := by
  rw [reset_step layout rom d i s resetHigh]
  exact initial_valid _ _ _ _ _

theorem loading_valid (i : Input aw) (s : State aw) (modeHigh : i.mode = true) :
    Valid layout rom d (step layout rom d i s) := by
  rw [loading_step layout rom d i s modeHigh]
  exact initial_valid _ _ _ _ _

/-- CPU TX admission and UART frame acceptance are the same edge and same
byte, including repeated equal byte values in distinct transactions. -/
theorem tx_acceptance (i : Input aw) (s : State aw) (valid : Valid layout rom d s) :
    Uart.accepted (SerialModel.uartInput (serialInput layout rom i s) (serialState s)) s.uart.tx =
      SerialModel.txWrite (serialInput layout rom i s) (serialState s) :=
  SerialModel.tx_acceptance _ _ valid.2.1

theorem tx_edge_balance (i : Input aw) (s : State aw) (valid : Valid layout rom d s) :
    s.system.mmio.tx.toList ++ (SerialModel.txWrite (serialInput layout rom i s) (serialState s)).toList =
      (SerialModel.txRetired d (serialInput layout rom i s) (serialState s)) ++
        (step layout rom d i s).system.mmio.tx.toList := by
  have balance := SerialModel.tx_edge_balance d (serialInput layout rom i s) (serialState s) valid.2.1
  rw [← serial_step layout rom d i s] at balance
  exact balance

end Pinwheel.Hardware.Processor.SerialSystemModel
