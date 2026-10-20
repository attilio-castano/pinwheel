import Pinwheel.Hardware.Buffered.SerialSourceTransaction

/-! A short read retains the same immutable receipt while source execution
continues. A subsequent exact read starts at the most-significant bit again;
its source state includes every sampled edge of both reads. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceRetry
open Pinwheel.Hardware Pinwheel.Program Serial.Frames

theorem retry_read {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    (s : SerialPackage.State) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload s.controller source)
    (assert close : SerialPackage.Pins) (bits : List Bool) (samples : List SerialPackage.Pins)
    (ready : ReceiptReady s.record) (low : Low (s.inputs assert))
    (wire : IsBits bits ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) (length : bits.length ≠ 192) :
    let pins := assert :: (samples ++ [close])
    ReceiptReady (s.run pins).record ∧
      (s.run pins).record.response = s.record.response ∧
      Refinement.RelatedSram program layout payload (s.run pins).controller
        (SerialSourceRead.sourceRun program source pins) := by
  have held := s.receipt_retry_read assert close bits samples ready low wire idle length
  exact ⟨held.1, held.2, SerialSourceRead.quiet_run related _
    (s.receipt_read_quiet assert close bits samples ready low wire idle)⟩

theorem retry_exact_read {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    (s : SerialPackage.State) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload s.controller source)
    (shortAssert shortClose : SerialPackage.Pins) (shortBits : List Bool)
    (shortSamples : List SerialPackage.Pins)
    (ready : ReceiptReady s.record) (low : Low (s.inputs shortAssert))
    (wire : IsBits shortBits ((s.step shortAssert).frontendInputs shortSamples))
    (idle : shortClose.cold = false ∧ shortClose.csn = true) (length : shortBits.length ≠ 192)
    (assert close : SerialPackage.Pins) (bits : List Bool) (samples : List SerialPackage.Pins)
    (readLow : Low ((s.run (shortAssert :: (shortSamples ++ [shortClose]))).inputs assert))
    (readWire : IsBits bits
      (((s.run (shortAssert :: (shortSamples ++ [shortClose]))).step assert).frontendInputs samples))
    (readIdle : close.cold = false ∧ close.csn = true) (readLength : bits.length = 192) :
    let short := shortAssert :: (shortSamples ++ [shortClose])
    let read := assert :: (samples ++ [close])
    let retry := s.run short
    Available (retry.run read).record ∧
      (retry.run read).record.response = s.record.response ∧
      retry.readObserved read =
        (List.range 192).map (fun k => s.record.response.getLsbD (191-k)) ∧
      Refinement.RelatedSram program layout payload (retry.run read).controller
        (SerialSourceRead.sourceRun program source (short ++ read)) := by
  have short := retry_read s source related shortAssert shortClose shortBits shortSamples
    ready low wire idle length
  have full := (s.run (shortAssert :: (shortSamples ++ [shortClose]))).receipt_exact_read
    assert close bits samples short.1 readLow readWire readIdle readLength
  have relation := SerialSourceRead.quiet_run short.2.2 _
    ((s.run (shortAssert :: (shortSamples ++ [shortClose]))).receipt_read_quiet
      assert close bits samples short.1 readLow readWire readIdle)
  refine ⟨full.1, full.2.1.trans short.2.1, ?_, ?_⟩
  · rw [full.2.2, short.2.1]
  · rw [SerialSourceTransaction.sourceRun_append]
    exact relation

end Pinwheel.Hardware.Buffered.SerialSourceRetry
