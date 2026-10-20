import Pinwheel.Hardware.Buffered.SerialSourceReceipt
import Pinwheel.Hardware.Buffered.GenericSramSimulation

/-! A frozen receipt describes the pre-capture source snapshot while capture
and every sampled read edge continue to clock the execution. The observed
192-bit stream is the exact held receipt, with its original sequence/rejection. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceRead
open Pinwheel.Hardware Pinwheel.Program Serial.Frames

def sourceRun (program : Program.Buffered.Program) (source : Program.Buffered.State)
    (pins : List SerialPackage.Pins) : Program.Buffered.State :=
  pins.foldl (fun state pin => Program.Buffered.advance program Refinement.capacity state pin.rawInputs) source

theorem commands_sourceRun (program : Program.Buffered.Program) (s : SerialPackage.State)
    (source : Program.Buffered.State) (pins : List SerialPackage.Pins) :
    (s.commands pins).foldl
      (fun state input => Program.Buffered.advance program Refinement.capacity state (input .rawInputs)) source =
      sourceRun program source pins := by
  induction pins generalizing s source with
  | nil => rfl
  | cons pin rest ih =>
    exact ih (s.step pin) (Program.Buffered.advance program Refinement.capacity source pin.rawInputs)

theorem quiet_run {program : Program.Buffered.Program} {layout : GenericCertificate.Layout program}
    {payload : BitVec 32} {s : SerialPackage.State} {source : Program.Buffered.State}
    (related : Refinement.RelatedSram program layout payload s.controller source)
    (pins : List SerialPackage.Pins) (quiet : ∀ i ∈ s.commands pins, SpiCircuit.Quiet i) :
    Refinement.RelatedSram program layout payload (s.run pins).controller
      (sourceRun program source pins) := by
  rw [s.run_controller]
  rw [← commands_sourceRun program s source pins]
  exact related.run_inputs (s.commands pins) quiet

theorem core_quiet (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (cold : pin.cold = false) (dispatch : s.record.dispatch = false) :
    SpiCircuit.Quiet (s.coreInputs pin) := by
  have quiet := Serial.Frames.fed_quiet s.record (s.inputs pin) cold dispatch
  exact ⟨(s.record_coreInputs pin .initialize).trans quiet.1,
    (s.record_coreInputs pin .command).trans quiet.2⟩

theorem capture_read {program : Program.Buffered.Program} {layout : GenericCertificate.Layout program}
    {payload : BitVec 32} (s : SerialPackage.State) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload s.controller source)
    (word : BitVec 160) (rejection : Bool) (capturing : Capturing word rejection s.record)
    (capture : SerialPackage.Pins) (captureIdle : capture.cold = false ∧ capture.csn = true)
    (assert close : SerialPackage.Pins) (bits : List Bool) (samples : List SerialPackage.Pins)
    (low : Low ((s.step capture).inputs assert))
    (wire : IsBits bits (((s.step capture).step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) (length : bits.length = 192) :
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
        (sourceRun program source (capture :: read)) := by
  have meaning := (SerialSourceReceipt.capture_source s source related capture
    captureIdle.1 capturing.capture).1
  have ready : ReceiptReady (s.step capture).record := by
    rw [s.record_step]
    exact (capturing.step_capture (s.inputs capture) captureIdle).1
  have read := (s.step capture).receipt_exact_read assert close bits samples ready low wire idle length
  have captureRelated := related.step (s.coreInputs capture)
    (core_quiet s capture captureIdle.1 capturing.dispatch)
  have suffix := quiet_run captureRelated (assert :: (samples ++ [close]))
    ((s.step capture).receipt_read_quiet assert close bits samples ready low wire idle)
  exact ⟨meaning, meaning.sequence.trans capturing.sequence,
    by rw [meaning.rejected, capturing.rejected], read.1, read.2.1, read.2.2, suffix⟩

end Pinwheel.Hardware.Buffered.SerialSourceRead
