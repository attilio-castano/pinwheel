import Pinwheel.Hardware.Processor.SystemModelProofs
import Pinwheel.Hardware.Processor.SerialModelProofs

/-! A sampled-wire MCU model with one shared MMIO state. CPU-only TX acceptance
bypasses into the UART offer on the same edge; the actual frontend pulses then
feed the connected processor's MMIO transition. Loader ownership holds both
processor and UART reset, while accepted loader words initialize RAM explicitly.
-/
namespace Pinwheel.Hardware.Processor.SerialSystemModel

structure State (aw : Nat) where
  system : SystemModel.State aw
  uart : Uart.State

structure Input (aw : Nat) where
  reset : Bool := false
  gpio : BitVec 32 := 0
  rx : Bool := true
  mode : Bool := false
  valid : Bool := false
  address : BitVec aw := 0
  data : BitVec 32 := 0
  deriving DecidableEq, Repr

def effectiveReset (i : Input aw) : Bool := i.reset || i.mode
def Accepted (i : Input aw) : Prop := i.mode = true ∧ i.reset = false ∧ i.valid = true
instance (i : Input aw) : Decidable (Accepted i) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def serialState (s : State aw) : SerialModel.State := ⟨s.system.mmio,s.uart⟩
def initial (contents : BitVec aw → BitVec 32) (q : BitVec 32) : State aw :=
  ⟨SystemModel.initial contents q,Uart.initial⟩

def serialInput (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (i : Input aw) (s : State aw) :
    SerialModel.Input :=
  ⟨effectiveReset i,
    match SystemModel.pendingPlan layout rom s.system with | some (.mmio request) => some request | _ => none,
    i.gpio,i.rx⟩

def frontend (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)
    (i : Input aw) (s : State aw) : Uart.Output :=
  Uart.observe d (SerialModel.uartInput (serialInput layout rom i s) (serialState s)) s.uart

def systemInput (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)
    (i : Input aw) (s : State aw) : SystemModel.Input :=
  let observed := frontend layout rom d i s
  ⟨effectiveReset i,i.gpio,observed.complete,observed.arrival,observed.framingError⟩

/-- Loader effects update words only. Q and all CPU/provider state are those
of the preceding effective-reset transition on an accepted loader edge. -/
def patch (s : SystemModel.State aw) (address : BitVec aw) (data : BitVec 32) : SystemModel.State aw :=
  {s with ram := {s.ram with memory := {s.ram.memory with
    contents := fun k => if address = k then data else s.ram.memory.contents k}}}

def step (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)
    (i : Input aw) (s : State aw) : State aw :=
  let base := SystemModel.step layout rom (systemInput layout rom d i s) s.system
  ⟨if Accepted i then patch base i.address i.data else base,
    Uart.step d (SerialModel.uartInput (serialInput layout rom i s) (serialState s)) s.uart⟩

structure Output where
  system : SystemModel.Output
  uart : Uart.Output
  loaderReady : Bool
  running : Bool

def observe (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)
    (i : Input aw) (s : State aw) : Output :=
  ⟨SystemModel.observe layout rom (systemInput layout rom d i s) s.system,
    frontend layout rom d i s,i.mode && !i.reset,!i.mode && !i.reset⟩

def component (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing) :
    Timed.Component (Input aw) (State aw) Output := ⟨step layout rom d,observe layout rom d⟩

def Valid (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing) (s : State aw) : Prop :=
  SystemModel.Valid layout rom s.system ∧ SerialModel.Valid d (serialState s)

theorem shared_mmio_input (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)
    (i : Input aw) (s : State aw) :
    SystemModel.mmioInput layout rom (systemInput layout rom d i s) s.system =
      SerialModel.mmioInput d (serialInput layout rom i s) (serialState s) := rfl

theorem serial_step (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)
    (i : Input aw) (s : State aw) :
    serialState (step layout rom d i s) = SerialModel.step d (serialInput layout rom i s) (serialState s) := by
  unfold serialState step
  split <;> rfl

theorem initial_valid (layout : AddressMap.Layout rw aw) (rom : SystemModel.Rom rw) (d : Uart.Timing)
    (contents : BitVec aw → BitVec 32) (q : BitVec 32) : Valid layout rom d (initial contents q) :=
  ⟨SystemModel.initial_valid _ _ _ _,SerialModel.initial_valid d⟩

end Pinwheel.Hardware.Processor.SerialSystemModel
