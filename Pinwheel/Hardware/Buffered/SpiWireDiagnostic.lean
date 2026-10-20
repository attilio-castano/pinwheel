import Pinwheel.Hardware.Buffered.GenericLogicalWireDiagnostic

/-! A source-only diagnostic witness: a zero-length accepted TX request faults
at the first SPI SHIFT entry, and arbitrary later raw clocks retain that stop.
This is not a claim of protocol success. -/
namespace Pinwheel.Hardware.Buffered.SpiWireDiagnostic
open Pinwheel.Hardware Pinwheel.Program Pinwheel.Engine.Reactive
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem fetch_zero (c : BufferedSPI.Config) :
    (BufferedSPI.program c).fetch 0 = some (BufferedSPI.low c.halfCyclesMinusOne) := by
  rw [BufferedSPI.fetch_shape]
  have positive : 0 < 16 * (c.bytesMinusOne.val+1) := by omega
  simp [positive]

theorem started_underflow (c : BufferedSPI.Config) (r : Values Reactive.Register)
    (i : Values Reactive.Input) (empty : i .txLength = 0) :
    (GenericStart.started (BufferedSPI.program c) r i).core.control = .stopped .fault := by
  simp [GenericStart.started,GenericStart.seed,GenericStart.resample,
    Program.Buffered.start,Program.Buffered.owned,Program.Buffered.lower,
    Fetch.start,Fetch.enter,fetch_zero,BufferedSPI.low,Program.Buffered.normalize,
    Program.Buffered.entryEffects,Program.Buffered.settle,
    Program.Buffered.consumed,Program.Buffered.terminal,Fetch.stop,Transfer.step,
    Transfer.Command.identity,Transfer.admittedStep,Transfer.Slot.identity,
    Transfer.reject,SpiStart.request,empty,SpiPacking.txBits]

theorem sourceAfter_underflow (c : BufferedSPI.Config) {before}
    (transaction : SerialWire.Transaction before)
    (empty : transaction.framed.coreInputs transaction.dispatch .txLength = 0) :
    (SerialStartAdmission.sourceAfter (BufferedSPI.program c) transaction).core.control = .stopped .fault := by
  unfold SerialStartAdmission.sourceAfter SerialSourceSession.Delivery.started
  rw [← SerialSourceTransaction.sourceRun_append]
  change (SerialSourceRead.sourceRun (BufferedSPI.program c)
    (GenericStart.started (BufferedSPI.program c) transaction.framed.controller.core
      (transaction.framed.coreInputs transaction.dispatch))
    ([transaction.capture] ++ transaction.read.pins)).core.control = .stopped .fault
  have stopped := started_underflow c transaction.framed.controller.core
    (transaction.framed.coreInputs transaction.dispatch) empty
  exact (congrArg (fun state : Program.Buffered.State => state.core.control)
    (SerialSessionWitness.sourceRun_stopped _ _ .fault stopped _)).trans stopped

theorem concrete_underflow (c : BufferedSPI.Config) (before : SerialPackage.State)
    (available : Serial.Frames.Available before.record) (sequence : BitVec 16)
    (payload : BitVec 32) (rx : BitVec 6) (raw : BitVec 2) :
    (SerialStartAdmission.sourceAfter (BufferedSPI.program c)
      (SerialStartAdmission.concreteStart before available sequence payload 0 rx raw)).core.control = .stopped .fault := by
  let transaction := SerialStartAdmission.concreteStart before available sequence payload 0 rx raw
  have word : transaction.request.word = SerialStartAdmission.startWord sequence
      (before.controller.core .generation) payload 0 rx := SerialWire.concrete_word ..
  have closed := transaction.request.closed
  rw [word] at closed
  have input := SerialStartAdmission.operands transaction.framed transaction.dispatch
    sequence _ payload 0 rx closed transaction.dispatchIdle.1
  exact sourceAfter_underflow c transaction input.tx

end Pinwheel.Hardware.Buffered.SpiWireDiagnostic
