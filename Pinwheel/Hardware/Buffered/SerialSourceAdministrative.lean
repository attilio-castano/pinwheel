import Pinwheel.Hardware.Buffered.SerialSourceTransaction
import Pinwheel.Hardware.Buffered.GenericCommandSimulation

/-! A non-reset administrative request can cross the running-to-retained
boundary while its raw wire frame is clocked. The actual non-RELEASE admission
at dispatch is sufficient; completion before dispatch does not lose the
source relation or change the capture cut. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceAdministrative
open Pinwheel.Hardware Pinwheel.Program Serial.Frames

theorem administrative_transaction {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    (s : SerialPackage.State) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload s.controller source)
    (word : BitVec 160) (assert close : SerialPackage.Pins) (samples : List SerialPackage.Pins)
    (available : Available s.record) (low : Low (s.inputs assert))
    (bits : IsBits (wordBits word) ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true)
    (opcode : SerialSourceRequest.ExecutionOpcode word)
    (dispatch capture : SerialPackage.Pins)
    (dispatchIdle : dispatch.cold = false ∧ dispatch.csn = true)
    (captureIdle : capture.cold = false ∧ capture.csn = true)
    (notRelease : Reactive.releasing.eval
      ((s.run (assert :: (samples ++ [close]))).coreInputs dispatch)
      (s.run (assert :: (samples ++ [close]))).controller.core = 0)
    (readAssert readClose : SerialPackage.Pins) (readBits : List Bool)
    (readSamples : List SerialPackage.Pins)
    (readLow : Low (((s.run (assert :: (samples ++ [close]))).step dispatch |>.step capture).inputs readAssert))
    (readWire : IsBits readBits
      ((((s.run (assert :: (samples ++ [close]))).step dispatch |>.step capture).step readAssert).frontendInputs readSamples))
    (readIdle : readClose.cold = false ∧ readClose.csn = true) (length : readBits.length = 192) :
    let framed := s.run (assert :: (samples ++ [close]))
    let current := SerialSourceRead.sourceRun program source (assert :: (samples ++ [close]))
    let rejection := (codeOf word == 0) && (framed.status dispatch .rejected == 1)
    SerialSourceTransaction.ReadResult program layout payload (framed.step dispatch)
      (Program.Buffered.advance program Refinement.capacity current dispatch.rawInputs)
      word rejection capture readAssert readClose readSamples := by
  let framed := s.run (assert :: (samples ++ [close]))
  have frame := SerialSourceRequest.frame_source s source related word assert close samples
    available low bits idle
  have inputs := SerialSourceRequest.execution_inputs framed dispatch word frame.1 dispatchIdle.1 opcode
  have delivered := frame.2.step_administrative (framed.coreInputs dispatch)
    ⟨inputs.1, inputs.2, notRelease⟩
  have pending : Capturing word
      ((codeOf word == 0) && (framed.status dispatch .rejected == 1)) (framed.step dispatch).record := by
    rw [framed.record_step]
    exact frame.1.step_dispatch (framed.inputs dispatch) dispatchIdle
  exact SerialSourceRead.capture_read (framed.step dispatch) _ delivered word _ pending
    capture captureIdle readAssert readClose readBits readSamples readLow readWire readIdle length

end Pinwheel.Hardware.Buffered.SerialSourceAdministrative
