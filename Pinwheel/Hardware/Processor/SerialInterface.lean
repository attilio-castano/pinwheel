import Pinwheel.Hardware.Processor.SerialModelProofs
import Pinwheel.Hardware.Processor.MmioInterface
import Pinwheel.Hardware.Uart.Interface
import Pinwheel.Hardware.Stream.Compose

/-! Atomic CPU MMIO pins and one synchronous sampled RX wire. Selector3 retains
the existing explicit register-hole response. The richer output includes all
MMIO diagnostics and UART frontend pulses; there is no response backpressure.
-/
namespace Pinwheel.Hardware.Processor.SerialInterface

abbrev inputPorts : Stream.Ports where
  size := 8
  widths k := if k.val = 2 then 2 else if k.val = 4 then 6 else
    if k.val = 5 ∨ k.val = 6 then 32 else 1
  names k := #["reset","request_valid","device","write","word","data","gpio_input","rx"][k]
  distinct := by decide +kernel
abbrev Input := inputPorts.Signal
abbrev Output := Stream.Joint MmioInterface.Output Uart.Physical.Output
def inputs : Interface Input := inputPorts.interface
def outputs : Interface Output := Stream.Joint.interface MmioInterface.outputs Uart.Physical.outputs

def reset : Input 1 := .at ⟨0,by simp⟩
def requestValid : Input 1 := .at ⟨1,by simp⟩
def device : Input 2 := .at ⟨2,by simp⟩
def write : Input 1 := .at ⟨3,by simp⟩
def word : Input 6 := .at ⟨4,by simp⟩
def data : Input 32 := .at ⟨5,by simp⟩
def gpioInput : Input 32 := .at ⟨6,by simp⟩
def rx : Input 1 := .at ⟨7,by simp⟩

def cpuPins (i : Values Input) : Values MmioInterface.Input
  | _, .at ⟨0,_⟩ => i reset
  | _, .at ⟨1,_⟩ => i requestValid
  | _, .at ⟨2,_⟩ => i device
  | _, .at ⟨3,_⟩ => i write
  | _, .at ⟨4,_⟩ => i word
  | _, .at ⟨5,_⟩ => i data
  | _, .at ⟨6,_⟩ => i gpioInput
  | _, .at ⟨7,_⟩ | _, .at ⟨8,_⟩ | _, .at ⟨9,_⟩ | _, .at ⟨10,_⟩ => 0
  | _, .at ⟨k+11,h⟩ => False.elim (by change k+11 < 11 at h; omega)

def decode (i : Values Input) : SerialModel.Input :=
  let m := MmioInterface.decode (cpuPins i)
  ⟨m.reset,m.operation,m.gpioInput,i rx == 1⟩
def invalid (i : Values Input) : Prop := MmioInterface.invalid (cpuPins i)
def Admitted (i : Values Input) : Prop := MmioInterface.Admitted (cpuPins i)

def mmioPins (d : Uart.Timing) (i : Values Input) (s : SerialModel.State) : Values MmioInterface.Input
  | _, .at ⟨0,_⟩ => i reset
  | _, .at ⟨1,_⟩ => i requestValid
  | _, .at ⟨2,_⟩ => i device
  | _, .at ⟨3,_⟩ => i write
  | _, .at ⟨4,_⟩ => i word
  | _, .at ⟨5,_⟩ => i data
  | _, .at ⟨6,_⟩ => i gpioInput
  | _, .at ⟨7,_⟩ => BitVec.ofBool (Uart.observe d (SerialModel.uartInput (decode i) s) s.uart).complete
  | _, .at ⟨8,_⟩ => BitVec.ofBool (Uart.observe d (SerialModel.uartInput (decode i) s) s.uart).arrival.isSome
  | _, .at ⟨9,_⟩ => (Uart.observe d (SerialModel.uartInput (decode i) s) s.uart).arrival.getD 0
  | _, .at ⟨10,_⟩ => BitVec.ofBool (Uart.observe d (SerialModel.uartInput (decode i) s) s.uart).framingError
  | _, .at ⟨k+11,h⟩ => False.elim (by change k+11 < 11 at h; omega)

def outputValues (d : Uart.Timing) (i : Values Input) (s : SerialModel.State) : Values Output :=
  Stream.Joint.values (MmioInterface.outputValues (mmioPins d i s) s.mmio)
    (Uart.Physical.outputValues (Uart.observe d (SerialModel.uartInput (decode i) s) s.uart))

def spec (d : Uart.Timing) : Timed.Component (Values Input) SerialModel.State (Values Output) where
  step i s := SerialModel.step d (decode i) s
  observe := outputValues d

end Pinwheel.Hardware.Processor.SerialInterface
