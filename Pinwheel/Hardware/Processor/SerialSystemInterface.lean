import Pinwheel.Hardware.Processor.SerialSystemModelProofs
import Pinwheel.Hardware.Processor.LoadableSystemModel
import Pinwheel.Hardware.Uart.Interface

/-! Seven top-level pins: external reset, GPIO, synchronous sampled RX and the
four explicit RAM-loader pins. Complete output coverage retains all core/MMIO,
loader status and UART diagnostic/wire ports. -/
namespace Pinwheel.Hardware.Processor.SerialSystemInterface

abbrev inputPorts (aw : Nat) : Stream.Ports where
  size := 7
  widths k := if k.val = 1 ∨ k.val = 6 then 32 else if k.val = 5 then aw else 1
  names k := #["reset","gpio_input","rx","loader_mode","loader_valid","loader_address","loader_data"][k]
  distinct := by decide +kernel
abbrev Input (aw : Nat) := (inputPorts aw).Signal
abbrev Output := Stream.Joint LoadableSystem.Output Uart.Physical.Output

def inputs (aw : Nat) : Interface (Input aw) := (inputPorts aw).interface
def outputs : Interface Output := Stream.Joint.interface LoadableSystem.outputs Uart.Physical.outputs

def reset : Input aw 1 := .at ⟨0,by simp⟩
def gpio : Input aw 32 := .at ⟨1,by simp⟩
def rx : Input aw 1 := .at ⟨2,by simp⟩
def mode : Input aw 1 := .at ⟨3,by simp⟩
def valid : Input aw 1 := .at ⟨4,by simp⟩
def address : Input aw aw := .at ⟨5,by simp⟩
def data : Input aw 32 := .at ⟨6,by simp⟩

def decode (i : Values (Input aw)) : SerialSystemModel.Input aw :=
  ⟨i reset == 1,i gpio,i rx == 1,i mode == 1,i valid == 1,i address,i data⟩

def modelLoadablePins (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)
    (i : Values (Input aw)) (s : SerialSystemModel.State aw) : Values (LoadableSystem.Input aw)
  | _, .left (.at ⟨0,_⟩) => i reset
  | _, .left (.at ⟨1,_⟩) => i gpio
  | _, .left (.at ⟨2,_⟩) => BitVec.ofBool (SerialSystemModel.frontend layout rom d (decode i) s).complete
  | _, .left (.at ⟨3,_⟩) => BitVec.ofBool (SerialSystemModel.frontend layout rom d (decode i) s).arrival.isSome
  | _, .left (.at ⟨4,_⟩) => (SerialSystemModel.frontend layout rom d (decode i) s).arrival.getD 0
  | _, .left (.at ⟨5,_⟩) => BitVec.ofBool (SerialSystemModel.frontend layout rom d (decode i) s).framingError
  | _, .left (.at ⟨k+6,h⟩) => False.elim (by change k+6 < 6 at h; omega)
  | _, .right (.at ⟨0,_⟩) => i mode
  | _, .right (.at ⟨1,_⟩) => i valid
  | _, .right (.at ⟨2,_⟩) => i address
  | _, .right (.at ⟨3,_⟩) => i data
  | _, .right (.at ⟨k+4,h⟩) => False.elim (by change k+4 < 4 at h; omega)

def outputValues (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)
    (i : Values (Input aw)) (s : SerialSystemModel.State aw) : Values Output :=
  Stream.Joint.values
    ((LoadableSystem.spec layout rom).observe (modelLoadablePins layout rom d i s) s.system)
    (Uart.Physical.outputValues (SerialSystemModel.frontend layout rom d (decode i) s))

def spec (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing) :
    Timed.Component (Values (Input aw)) (SerialSystemModel.State aw) (Values Output) where
  step i s := SerialSystemModel.step layout rom d (decode i) s
  observe := outputValues layout rom d

theorem input_count (aw : Nat) : (inputs aw).size = 7 := rfl
theorem output_count : outputs.size = 45 := rfl

end Pinwheel.Hardware.Processor.SerialSystemInterface
