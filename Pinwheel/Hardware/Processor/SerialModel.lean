import Pinwheel.Hardware.Processor.MmioModel
import Pinwheel.Hardware.Uart.Model

/-! Digital MMIO/UART composition. CPU accesses inspect pre-edge device state.
The CPU-only TX update bypasses to the UART offer on the same edge; completion
of the old frame then clears the MMIO slot. RX samples are synchronous digital
inputs, with no analog synchronization or oscillator-tolerance claim.
-/
namespace Pinwheel.Hardware.Processor.SerialModel

structure State where
  mmio : MmioModel.State
  uart : Uart.State
  deriving DecidableEq, Repr

structure Input where
  reset : Bool := false
  operation : Option MmioModel.Request := none
  gpioInput : BitVec 32 := 0
  rx : Bool := true
  deriving DecidableEq, Repr

structure Output where
  response : Option MmioModel.Response
  gpioOutput : BitVec 32
  frontend : Uart.Output
  deriving DecidableEq, Repr

def initial : State := ⟨MmioModel.initial, Uart.initial⟩

/-- CPU-only state is independent of all serial frontend pulses. -/
def cpuInput (i : Input) : MmioModel.Input :=
  ⟨i.reset, i.operation, i.gpioInput, false, none, false⟩

def cpuState (i : Input) (s : State) : MmioModel.State := MmioModel.cpuState (cpuInput i) s.mmio

def uartInput (i : Input) (s : State) : Uart.Input := ⟨i.reset, (cpuState i s).tx, i.rx⟩

def mmioInput (d : Uart.Timing) (i : Input) (s : State) : MmioModel.Input :=
  let frontend := Uart.observe d (uartInput i s) s.uart
  ⟨i.reset, i.operation, i.gpioInput, frontend.complete, frontend.arrival, frontend.framingError⟩

def step (d : Uart.Timing) (i : Input) (s : State) : State :=
  ⟨MmioModel.step (mmioInput d i s) s.mmio, Uart.step d (uartInput i s) s.uart⟩

def observe (d : Uart.Timing) (i : Input) (s : State) : Output :=
  ⟨MmioModel.observe (mmioInput d i s) s.mmio,
    if i.reset then 0 else s.mmio.gpioOut, Uart.observe d (uartInput i s) s.uart⟩

def component (d : Uart.Timing) : Timed.Component Input State Output := ⟨step d, observe d⟩

def Owned (s : State) : Prop := s.mmio.tx = Uart.txPending s.uart.tx
def Valid (d : Uart.Timing) (s : State) : Prop := Owned s ∧ Uart.Valid d s.uart

/-- CPU-side admission, independent of UART acceptance. Busy writes still fault
on a completion edge; equal bytes from distinct writes remain distinct events. -/
def txWrite (i : Input) (s : State) : Option Uart.Byte :=
  if i.reset then none else match i.operation with
  | none => none
  | some r => if r.device = .uart ∧ r.word = 1 ∧ r.write = true ∧ s.mmio.tx = none
      then some (r.data.extractLsb' 0 8) else none

def txComplete (d : Uart.Timing) (i : Input) (s : State) : Option Uart.Byte :=
  Uart.completed d (uartInput i s) s.uart.tx
def txCancel (i : Input) (s : State) : Option Uart.Byte := if i.reset then s.mmio.tx else none

def rxConsumed (i : Input) (s : State) : Option Uart.Byte :=
  if i.reset then none else if (cpuState i s).rx.isNone then s.mmio.rx else none
def rxCancel (i : Input) (s : State) : Option Uart.Byte := if i.reset then s.mmio.rx else none
def rxAccepted (d : Uart.Timing) (i : Input) (s : State) : Option Uart.Byte :=
  if (cpuState i s).rx.isNone then (mmioInput d i s).rxArrival else none
def rxDropped (d : Uart.Timing) (i : Input) (s : State) : Option Uart.Byte :=
  if (cpuState i s).rx.isSome then (mmioInput d i s).rxArrival else none

/-- Actual MMIO CPU/autonomous ordering, retaining faults and dropped arrivals. -/
def deviceEvents (d : Uart.Timing) (i : Input) (s : State) : List MmioModel.Event :=
  MmioModel.events (mmioInput d i s) s.mmio

def history (d : Uart.Timing) (extract : Input → State → List α) (s : State) : List Input → List α
  | [] => []
  | i :: rest => extract i s ++ history d extract (step d i s) rest

def txRetired (d : Uart.Timing) (i : Input) (s : State) : List Uart.Byte :=
  (txComplete d i s).toList ++ (txCancel i s).toList
def rxRetired (i : Input) (s : State) : List Uart.Byte :=
  (rxConsumed i s).toList ++ (rxCancel i s).toList

end Pinwheel.Hardware.Processor.SerialModel
