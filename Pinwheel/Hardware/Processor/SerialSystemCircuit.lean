import Pinwheel.Hardware.Processor.SerialSystemInterface
import Pinwheel.Hardware.Processor.SerialCircuit
import Pinwheel.Hardware.Processor.LoadableSystem

/-! Shared-MMIO composition: the processor owns its original MMIO bank, and
only the six UART registers are added. The UART branch of SerialCircuit is
bound to that same bank. CPU request pins are computed with zero frontend
pulses; the resulting UART outputs then drive the existing loadable system.
This is an acyclic expression graph using only existing constructors.
-/
namespace Pinwheel.Hardware.Processor.SerialSystemCircuit
open SerialSystemInterface

abbrev Register (aw : Nat) (d : Uart.Timing) := Stream.Joint (LoadableSystem.Register aw) (Uart.Structural.Register d)
def registers (aw : Nat) (d : Uart.Timing) : Interface (Register aw d) :=
  Stream.Joint.interface (LoadableSystem.registers aw) (Uart.Structural.registers d)
def system (r : LoadableSystem.Register aw b) : Register aw d b := .left r
def uart (r : Uart.Structural.Register d b) : Register aw d b := .right r

def serialRegister : SerialCircuit.Register d b → Register aw d b
  | .left r => system (SystemCircuit.mmio r)
  | .right r => uart r

def systemState (s : Values (Register aw d)) : Values (LoadableSystem.Register aw) := fun r => s (system r)
def uartState (s : Values (Register aw d)) : Values (Uart.Structural.Register d) := fun r => s (uart r)
def serialState (s : Values (Register aw d)) : Values (SerialCircuit.Register d) := fun r => s (serialRegister r)
def view (s : Values (Register aw d)) : SerialSystemModel.State aw :=
  ⟨SystemCircuit.view (systemState s),Uart.Structural.view (uartState s)⟩
def Valid (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)
    (s : Values (Register aw d)) : Prop :=
  SystemCircuit.Valid layout rom (systemState s) ∧ SerialCircuit.Valid d (serialState s)

abbrev E (aw : Nat) (d : Uart.Timing) (b : Nat) := Expr (Input aw) (Register aw d) b

def effectiveReset : E aw d 1 := WordOps.wordOr (.input reset) (.input mode)

def quietSystemInput : {b : Nat} → SystemInterface.Input b → E aw d b
  | _, .at ⟨0,_⟩ => effectiveReset
  | _, .at ⟨1,_⟩ => .input gpio
  | _, .at ⟨2,_⟩ | _, .at ⟨3,_⟩ | _, .at ⟨4,_⟩ | _, .at ⟨5,_⟩ => .lit 0
  | _, .at ⟨k+6,h⟩ => False.elim (by change k+6 < 6 at h; omega)

def cpuMmioInput (layout : AddressMap.Layout rw aw) (p : MmioInterface.Input b) : E aw d b :=
  (SystemCircuit.mmioInput layout p).bind quietSystemInput (fun r => .reg (system r))

def serialInput (layout : AddressMap.Layout rw aw) : {b : Nat} → SerialInterface.Input b → E aw d b
  | _, .at ⟨0,_⟩ => effectiveReset
  | _, .at ⟨1,_⟩ => cpuMmioInput layout MmioInterface.requestValid
  | _, .at ⟨2,_⟩ => cpuMmioInput layout MmioInterface.device
  | _, .at ⟨3,_⟩ => cpuMmioInput layout MmioInterface.write
  | _, .at ⟨4,_⟩ => cpuMmioInput layout MmioInterface.word
  | _, .at ⟨5,_⟩ => cpuMmioInput layout MmioInterface.data
  | _, .at ⟨6,_⟩ => .input gpio
  | _, .at ⟨7,_⟩ => .input rx
  | _, .at ⟨k+8,h⟩ => False.elim (by change k+8 < 8 at h; omega)

def serialOutput (layout : AddressMap.Layout rw aw) (d : Uart.Timing) (o : SerialInterface.Output b) : E aw d b :=
  ((SerialCircuit.circuit d).output o).bind (serialInput layout) (fun r => .reg (serialRegister r))

def loadableInput (layout : AddressMap.Layout rw aw) (d : Uart.Timing) :
    {b : Nat} → LoadableSystem.Input aw b → E aw d b
  | _, .left (.at ⟨0,_⟩) => .input reset
  | _, .left (.at ⟨1,_⟩) => .input gpio
  | _, .left (.at ⟨2,_⟩) => serialOutput layout d (.right Uart.Physical.txComplete)
  | _, .left (.at ⟨3,_⟩) => serialOutput layout d (.right Uart.Physical.rxValid)
  | _, .left (.at ⟨4,_⟩) => serialOutput layout d (.right Uart.Physical.rxData)
  | _, .left (.at ⟨5,_⟩) => serialOutput layout d (.right Uart.Physical.framingError)
  | _, .left (.at ⟨k+6,h⟩) => False.elim (by change k+6 < 6 at h; omega)
  | _, .right (.at ⟨0,_⟩) => .input mode
  | _, .right (.at ⟨1,_⟩) => .input valid
  | _, .right (.at ⟨2,_⟩) => .input address
  | _, .right (.at ⟨3,_⟩) => .input data
  | _, .right (.at ⟨k+4,h⟩) => False.elim (by change k+4 < 4 at h; omega)

def serialPins (layout : AddressMap.Layout rw aw) (i : Values (Input aw)) (s : Values (Register aw d)) :
    Values SerialInterface.Input := fun p => (serialInput layout p).eval i s

def loadablePins (layout : AddressMap.Layout rw aw) (d : Uart.Timing) (i : Values (Input aw))
    (s : Values (Register aw d)) : Values (LoadableSystem.Input aw) := fun p => (loadableInput layout d p).eval i s

def quietPins (i : Values (Input aw)) (s : Values (Register aw d)) : Values SystemInterface.Input :=
  fun p => (quietSystemInput p).eval i s

def circuit (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (romFits : rw ≤ 30) (ramFits : aw ≤ 30)
    (d : Uart.Timing) : Circuit (Input aw) (Register aw d) Output where
  next r := match r with
    | .left r => ((LoadableSystem.circuit layout rom romFits ramFits).next r).bind
        (loadableInput layout d) (fun r => .reg (system r))
    | .right r => ((SerialCircuit.circuit d).next (.right r)).bind
        (serialInput layout) (fun r => .reg (serialRegister r))
  output o := match o with
    | .left o => ((LoadableSystem.circuit layout rom romFits ramFits).output o).bind
        (loadableInput layout d) (fun r => .reg (system r))
    | .right o => serialOutput layout d (.right o)

theorem register_count (aw : Nat) (d : Uart.Timing) : (registers aw d).size = 2^aw+62 := by
  change 37 + ((2^aw+8) + (8+3)) + 6 = 2^aw+62
  omega

end Pinwheel.Hardware.Processor.SerialSystemCircuit
