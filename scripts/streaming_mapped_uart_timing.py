"""Additional mapped public-BUSY timing corollaries; mandatory44 stay intact.

Each generated proof imports the reconstructed mapped whole-device session and
transports the typed UART first-terminal result through its checked run and
pad observation equations. Module/instance names supply no behavioral premise.
"""

THEOREMS = ('uart_first_terminal_correct', 'uart_bad_stop_first_terminal_correct',
    'uart_false_start_first_terminal_correct')


def required_qnames():
    return extra_qnames(1) + extra_qnames(2)


def extra_qnames(addr_bits):
    if type(addr_bits) is not int or addr_bits not in (1, 2):
        raise ValueError('Mapped UART timing requires queue address width1 or2')
    return ['Pinwheel.Artifact.StreamingMappedSessionD' + str(2 ** addr_bits) + '.' + theorem for theorem in THEOREMS]


def generate(addr_bits):
    if type(addr_bits) is not int or addr_bits not in (1, 2):
        raise ValueError('Mapped UART timing requires queue address width1 or2')
    depth = str(2 ** addr_bits)
    source = r'''import StreamingMappedSessionD@D@
import Pinwheel.Hardware.StreamingMapped.UARTTiming

namespace Pinwheel.Artifact.StreamingMappedSessionD@D@
open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady
open Pinwheel.Program.StreamingReady

def uartBusyPad (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2) (edges : Nat) (observation : BitVec 2) : Bool :=
  (physicalObserve (physicalRun startup (uartArmPins rate ++
      (Pinwheel.Hardware.StreamingUART.Frame.pins raw edges).map PublicPins.embed))
    (Pinwheel.Hardware.StreamingMapped.UARTTiming.padPin observation) .uo).getLsbD 5

theorem uart_busy_transport (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2) (edges : Nat) (observation : BitVec 2) :
    uartBusyPad rate startup raw edges observation = Pinwheel.Hardware.StreamingMapped.UARTTiming.busyPad
      (Pinwheel.Hardware.StreamingUART.Frame.actualRun rate startup raw edges) observation := by
  rw [uartBusyPad,physical_observe_correct,uart_actual_frame]
  rfl

def UARTFirstBusy (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2) (edges : Nat) : Prop :=
  (∀ observation, uartBusyPad rate startup raw edges observation = false) ∧
    ∀ earlier, earlier < edges → ∀ observation, uartBusyPad rate startup raw earlier observation = true

theorem uart_first_terminal_transport (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2) (edges : Nat)
    (first : Pinwheel.Hardware.StreamingMapped.UARTTiming.FirstBusy rate startup raw edges) :
    UARTFirstBusy rate startup raw edges := by
  constructor
  · intro observation
    rw [uart_busy_transport]
    exact first.1 observation
  · intro earlier before observation
    rw [uart_busy_transport]
    exact first.2 earlier before observation

theorem uart_first_terminal_correct (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2) (payload : BitVec 8)
    (falling : (raw 0)[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (startLow : (raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (samples : Pinwheel.Program.StreamingUART.Frame.DataSamples (Pinwheel.Hardware.StreamingUART.Boot.profile rate)
      (Pinwheel.Hardware.StreamingUART.Frame.incoming raw) payload)
    (stopHigh : (raw (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = true) :
    UARTFirstBusy rate startup raw (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q+4) := by
  apply uart_first_terminal_transport
  exact Pinwheel.Hardware.StreamingMapped.UARTTiming.good_first rate startup raw payload (by decide)
    falling startLow samples stopHigh

theorem uart_bad_stop_first_terminal_correct (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2) (payload : BitVec 8)
    (falling : (raw 0)[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (startLow : (raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (samples : Pinwheel.Program.StreamingUART.Frame.DataSamples (Pinwheel.Hardware.StreamingUART.Boot.profile rate)
      (Pinwheel.Hardware.StreamingUART.Frame.incoming raw) payload)
    (stopLow : (raw (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false) :
    UARTFirstBusy rate startup raw (38*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q+3) := by
  apply uart_first_terminal_transport
  exact Pinwheel.Hardware.StreamingMapped.UARTTiming.bad_stop_first rate startup raw payload (by decide)
    falling startLow samples stopLow

theorem uart_false_start_first_terminal_correct (rate : Fin 3) (startup : Package.State @A@)
    (raw : Nat → BitVec 2)
    (falling : (raw 0)[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = false)
    (startHigh : (raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q))[(Pinwheel.Hardware.StreamingUART.Boot.profile rate).rxInput.val] = true) :
    UARTFirstBusy rate startup raw (2*(Pinwheel.Hardware.StreamingUART.Boot.profile rate).Q+3) := by
  apply uart_first_terminal_transport
  exact Pinwheel.Hardware.StreamingMapped.UARTTiming.false_start_first rate startup raw (by decide) falling startHigh

end Pinwheel.Artifact.StreamingMappedSessionD@D@
'''
    source = source.replace('@D@', depth).replace('@A@', str(addr_bits))
    return {'StreamingMappedUARTTimingD' + depth: source}
