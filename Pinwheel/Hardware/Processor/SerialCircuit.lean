import Pinwheel.Hardware.Processor.SerialInterface
import Pinwheel.Hardware.Processor.MmioCircuit
import Pinwheel.Hardware.Uart.Circuit

/-! MMIO's CPU-only TX update bypasses into the UART on the accepted CPU edge.
UART pulses feed the actual MMIO update, but never the bypass predicate. All
fourteen registers are the original component registers with no extra state.
-/
namespace Pinwheel.Hardware.Processor.SerialCircuit
open SerialInterface

abbrev Register (d : Uart.Timing) := Stream.Joint MmioCircuit.Register (Uart.Structural.Register d)
def registers (d : Uart.Timing) : Interface (Register d) :=
  Stream.Joint.interface MmioCircuit.registers (Uart.Structural.registers d)
def mmio (r : MmioCircuit.Register b) : Register d b := .left r
def uart (r : Uart.Structural.Register d b) : Register d b := .right r
def mmioState (s : Values (Register d)) : Values MmioCircuit.Register := fun r => s (mmio r)
def uartState (s : Values (Register d)) : Values (Uart.Structural.Register d) := fun r => s (uart r)
def view (s : Values (Register d)) : SerialModel.State :=
  ⟨MmioCircuit.view (mmioState s),Uart.Structural.view (uartState s)⟩
def Valid (d : Uart.Timing) (s : Values (Register d)) : Prop :=
  Uart.Structural.Valid d (uartState s) ∧ SerialModel.Owned (view s)
def encode (d : Uart.Timing) (s : SerialModel.State) : Values (Register d) :=
  Stream.Joint.values (MmioCircuit.encode s.mmio) (Uart.Structural.encode d s.uart)
abbrev E (d : Uart.Timing) (b : Nat) := Expr Input (Register d) b

def cpuInput : {b : Nat} → MmioInterface.Input b → E d b
  | _, .at ⟨0,_⟩ => .input reset
  | _, .at ⟨1,_⟩ => .input requestValid
  | _, .at ⟨2,_⟩ => .input device
  | _, .at ⟨3,_⟩ => .input write
  | _, .at ⟨4,_⟩ => .input word
  | _, .at ⟨5,_⟩ => .input data
  | _, .at ⟨6,_⟩ => .input gpioInput
  | _, .at ⟨7,_⟩ | _, .at ⟨8,_⟩ | _, .at ⟨9,_⟩ | _, .at ⟨10,_⟩ => .lit 0
  | _, .at ⟨k+11,h⟩ => False.elim (by change k+11 < 11 at h; omega)

def txStart : E d 1 := MmioCircuit.txStart.bind cpuInput (fun r => .reg (mmio r))
def uartInput : {b : Nat} → Uart.Physical.Input b → E d b
  | _, .at ⟨0,_⟩ => .input reset
  | _, .at ⟨1,_⟩ => txStart.bor (.reg (mmio MmioCircuit.txActiveReg))
  | _, .at ⟨2,_⟩ => .mux txStart (.slice 0 8 (by decide) (.input data)) (.reg (mmio MmioCircuit.txDataReg))
  | _, .at ⟨3,_⟩ => .input rx
  | _, .at ⟨k+4,h⟩ => False.elim (by change k+4 < 4 at h; omega)

def uartOutput (d : Uart.Timing) (o : Uart.Physical.Output b) : E d b :=
  ((Uart.Structural.circuit d).output o).bind uartInput (fun r => .reg (uart r))

def mmioInput (d : Uart.Timing) : {b : Nat} → MmioInterface.Input b → E d b
  | _, .at ⟨7,_⟩ => uartOutput d Uart.Physical.txComplete
  | _, .at ⟨8,_⟩ => uartOutput d Uart.Physical.rxValid
  | _, .at ⟨9,_⟩ => uartOutput d Uart.Physical.rxData
  | _, .at ⟨10,_⟩ => uartOutput d Uart.Physical.framingError
  | _, p => cpuInput p

def uartPins (i : Values Input) (s : Values (Register d)) : Values Uart.Physical.Input := fun p => (uartInput p).eval i s
def boundMmioPins (d : Uart.Timing) (i : Values Input) (s : Values (Register d)) : Values MmioInterface.Input :=
  fun p => (mmioInput d p).eval i s

def circuit (d : Uart.Timing) : Circuit Input (Register d) Output where
  next r := match r with
    | .left r => (MmioCircuit.circuit.next r).bind (mmioInput d) (fun r => .reg (mmio r))
    | .right r => ((Uart.Structural.circuit d).next r).bind uartInput (fun r => .reg (uart r))
  output o := match o with
    | .left o => (MmioCircuit.circuit.output o).bind (mmioInput d) (fun r => .reg (mmio r))
    | .right o => uartOutput d o

end Pinwheel.Hardware.Processor.SerialCircuit
