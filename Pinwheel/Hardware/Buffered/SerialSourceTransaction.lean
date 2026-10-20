import Pinwheel.Hardware.Buffered.SerialSourceRequest
import Pinwheel.Hardware.Buffered.LifecycleSramExecution

/-! A sampled request frame, busy administrative dispatch, capture edge and
exact receipt read form one source-grounded transaction. Every sampled edge
still clocks the controller; the receipt refers to the post-dispatch source. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceTransaction
open Pinwheel.Hardware Pinwheel.Program Serial.Frames

private theorem busy_retained {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {actual : SramState.State} {source : Program.Buffered.State}
    (related : Refinement.RelatedSram program layout payload actual source)
    (busy : Engine.Reactive.busy source.core = true) : actual.core .retained = 0 := by
  obtain ⟨rows, dictionary, resident, ready, relation⟩ := related
  rcases relation with ⟨e, instruction, pc, running⟩ | ⟨e, outcome, stopped⟩
  · exact running.retained
  · simp [stopped.control, Engine.Reactive.busy] at busy

theorem sourceRun_append (program : Program.Buffered.Program) (source : Program.Buffered.State)
    (first rest : List SerialPackage.Pins) :
    SerialSourceRead.sourceRun program source (first ++ rest) =
      SerialSourceRead.sourceRun program (SerialSourceRead.sourceRun program source first) rest :=
  List.foldl_append

def ReadResult (program : Program.Buffered.Program) (layout : GenericCertificate.Layout program)
    (payload : BitVec 32) (s : SerialPackage.State) (source : Program.Buffered.State)
    (word : BitVec 160) (rejection : Bool) (capture assert close : SerialPackage.Pins)
    (samples : List SerialPackage.Pins) : Prop :=
  let receipt := (s.step capture).record.response
  let read := assert :: (samples ++ [close])
  SerialSourceReceipt.Meaning receipt s.record source ∧
    receipt.extractLsb' 160 16 = word.extractLsb' 128 16 ∧
    receipt.extractLsb' 4 1 = BitVec.ofBool rejection ∧
    Available ((s.step capture).run read).record ∧
    ((s.step capture).run read).record.response = receipt ∧
    (s.step capture).readObserved read =
      (List.range 192).map (fun k => receipt.getLsbD (191-k)) ∧
    Refinement.RelatedSram program layout payload ((s.step capture).run read).controller
      (SerialSourceRead.sourceRun program source (capture :: read))

private theorem busy_step {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    {actual : SramState.State} {source : Program.Buffered.State}
    (related : Refinement.RelatedSram program layout payload actual source)
    (i : Values Reactive.Input) (cold : i .initialize = 0) (warm : i .command ≠ 7#3)
    (busy : Engine.Reactive.busy source.core = true) :
    Refinement.RelatedSram program layout payload (actual.step i)
      (Program.Buffered.advance program Refinement.capacity source (i .rawInputs)) := by
  rw [Lifecycle.execution_clock actual i cold warm
    (by exact (related.busy i).trans (by rw [busy]; rfl)) (busy_retained related busy)]
  exact related.step (Lifecycle.quiet i) (Lifecycle.quiet_input i)

theorem busy_transaction {program : Program.Buffered.Program}
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
    (busy : Engine.Reactive.busy
      (SerialSourceRead.sourceRun program source (assert :: (samples ++ [close]))).core = true)
    (readAssert readClose : SerialPackage.Pins) (readBits : List Bool)
    (readSamples : List SerialPackage.Pins)
    (readLow : Low (((s.run (assert :: (samples ++ [close]))).step dispatch |>.step capture).inputs readAssert))
    (readWire : IsBits readBits
      ((((s.run (assert :: (samples ++ [close]))).step dispatch |>.step capture).step readAssert).frontendInputs readSamples))
    (readIdle : readClose.cold = false ∧ readClose.csn = true) (length : readBits.length = 192) :
    let framed := s.run (assert :: (samples ++ [close]))
    let current := SerialSourceRead.sourceRun program source (assert :: (samples ++ [close]))
    let rejection := (codeOf word == 0) && (framed.status dispatch .rejected == 1)
    ReadResult program layout payload (framed.step dispatch)
      (Program.Buffered.advance program Refinement.capacity current dispatch.rawInputs)
      word rejection capture readAssert readClose readSamples := by
  let framed := s.run (assert :: (samples ++ [close]))
  have frame := SerialSourceRequest.frame_source s source related word assert close samples
    available low bits idle
  have inputs := SerialSourceRequest.execution_inputs framed dispatch word frame.1 dispatchIdle.1 opcode
  have delivered := busy_step frame.2 (framed.coreInputs dispatch) inputs.1 inputs.2 busy
  have pending : Capturing word
      ((codeOf word == 0) && (framed.status dispatch .rejected == 1)) (framed.step dispatch).record := by
    rw [framed.record_step]
    exact frame.1.step_dispatch (framed.inputs dispatch) dispatchIdle
  exact SerialSourceRead.capture_read (framed.step dispatch) _ delivered word _ pending
    capture captureIdle readAssert readClose readBits readSamples readLow readWire readIdle length

end Pinwheel.Hardware.Buffered.SerialSourceTransaction
