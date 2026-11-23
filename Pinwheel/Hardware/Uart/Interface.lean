import Pinwheel.Hardware.Uart.Model
import Pinwheel.Hardware.Stream.Ports

/-! Digital UART pins. `rx` is an already synchronous sampled input. TX offers
use pre-edge readiness and have no same-edge completion/refill. Received bytes
and framing errors are pulses, independent of a downstream receive buffer.
-/
namespace Pinwheel.Hardware.Uart.Physical

abbrev inputPorts : Hardware.Stream.Ports where
  size := 4
  widths k := if k.val = 2 then 8 else 1
  names k := #["reset", "tx_valid", "tx_data", "rx"][k]
  distinct := by decide +kernel

abbrev outputPorts : Hardware.Stream.Ports where
  size := 6
  widths k := if k.val = 4 then 8 else 1
  names k := #["tx", "tx_ready", "tx_complete", "rx_valid", "rx_data", "framing_error"][k]
  distinct := by decide +kernel

abbrev Input := inputPorts.Signal
abbrev Output := outputPorts.Signal

def reset : Input 1 := .at ⟨0, by simp⟩
def txValid : Input 1 := .at ⟨1, by simp⟩
def txData : Input 8 := .at ⟨2, by simp⟩
def rx : Input 1 := .at ⟨3, by simp⟩
def tx : Output 1 := .at ⟨0, by simp⟩
def txReady : Output 1 := .at ⟨1, by simp⟩
def txComplete : Output 1 := .at ⟨2, by simp⟩
def rxValid : Output 1 := .at ⟨3, by simp⟩
def rxData : Output 8 := .at ⟨4, by simp⟩
def framingError : Output 1 := .at ⟨5, by simp⟩
def inputs : Hardware.Interface Input := inputPorts.interface
def outputs : Hardware.Interface Output := outputPorts.interface

def decode (i : Values Input) : Uart.Input :=
  ⟨i reset == 1, if i txValid = 1 then some (i txData) else none, i rx == 1⟩

def outputValues (o : Uart.Output) : Values Output
  | _, .at ⟨0, _⟩ => BitVec.ofBool o.line
  | _, .at ⟨1, _⟩ => BitVec.ofBool o.ready
  | _, .at ⟨2, _⟩ => BitVec.ofBool o.complete
  | _, .at ⟨3, _⟩ => BitVec.ofBool o.arrival.isSome
  | _, .at ⟨4, _⟩ => o.arrival.getD 0
  | _, .at ⟨5, _⟩ => BitVec.ofBool o.framingError
  | _, .at ⟨k+6, h⟩ => False.elim (by change k+6 < 6 at h; omega)

def spec (d : Timing) : Timed.Component (Values Input) Uart.State (Values Output) where
  step i s := Uart.step d (decode i) s
  observe i s := outputValues (Uart.observe d (decode i) s)

end Pinwheel.Hardware.Uart.Physical
