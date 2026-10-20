import Pinwheel.Hardware.Buffered.SerialPackageFrames
import Pinwheel.Hardware.Buffered.SerialCorrespondenceRead

/-! Actual MISO receipt serialization for the closed-loop serial/SRAM product.
All engine clocks remain present while a receipt is read or retried. -/
namespace Pinwheel.Hardware.Buffered.SerialPackage
open Pinwheel.Hardware Serial.Frames

def State.readObserved (s : State) : List Pins → List Bool
  | [] => []
  | p :: rest => if Serial.Read.rising s.record (s.inputs p) then
      (s.observe p .miso == 1) :: (s.step p).readObserved rest
    else (s.step p).readObserved rest

theorem State.readObserved_record (s : State) (pins : List Pins) :
    s.readObserved pins = Serial.Read.observed s.record (s.frontendInputs pins) := by
  induction pins generalizing s with
  | nil => rfl
  | cons p rest ih =>
    change (if Serial.Read.rising s.record (s.inputs p) then
        (s.observe p .miso == 1) :: (s.step p).readObserved rest
      else (s.step p).readObserved rest) =
      (if Serial.Read.rising s.record (s.inputs p) then
        (s.record.miso (s.inputs p) == 1) ::
          Serial.Read.observed (s.record.step (s.inputs p)) ((s.step p).frontendInputs rest)
      else Serial.Read.observed (s.record.step (s.inputs p)) ((s.step p).frontendInputs rest))
    have value : s.observe p .miso = s.record.miso (s.inputs p) := s.record_observe p .miso
    rw [value, ih, s.record_step]
  done

theorem State.receipt_exact_read (s : State) (assert close : Pins) (bits : List Bool)
    (samples : List Pins) (ready : ReceiptReady s.record)
    (low : Low (s.inputs assert))
    (wire : IsBits bits ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) (length : bits.length = 192) :
    Available (s.run (assert :: (samples ++ [close]))).record ∧
    (s.run (assert :: (samples ++ [close]))).record.response = s.record.response ∧
    s.readObserved (assert :: (samples ++ [close])) =
      (List.range 192).map (fun k => s.record.response.getLsbD (191-k)) := by
  rw [s.record_run, s.readObserved_record]
  simp only [State.frontendInputs, State.frontendInputs_append]
  apply Serial.Read.exact_read s.record (s.inputs assert)
  · exact ready
  · exact low
  · exact wire
  · exact idle
  · exact length
  done

theorem State.receipt_retry_read (s : State) (assert close : Pins) (bits : List Bool)
    (samples : List Pins) (ready : ReceiptReady s.record)
    (low : Low (s.inputs assert))
    (wire : IsBits bits ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) (length : bits.length ≠ 192) :
    ReceiptReady (s.run (assert :: (samples ++ [close]))).record ∧
    (s.run (assert :: (samples ++ [close]))).record.response = s.record.response := by
  rw [s.record_run]
  simp only [State.frontendInputs, State.frontendInputs_append]
  apply Serial.Read.retry_read s.record (s.inputs assert)
  · exact ready
  · exact low
  · exact wire
  · exact idle
  · exact length
  done

theorem State.receipt_read_quiet (s : State) (assert close : Pins) (bits : List Bool)
    (samples : List Pins) (ready : ReceiptReady s.record)
    (low : Low (s.inputs assert))
    (wire : IsBits bits ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) :
    ∀ input ∈ s.commands (assert :: (samples ++ [close])), Quiet input := by
  rw [s.commands_record]
  simp only [State.frontendInputs, State.frontendInputs_append]
  apply Serial.Read.transaction_quiet s.record (s.inputs assert)
  · exact ready
  · exact low
  · exact wire
  · exact idle
  done

end Pinwheel.Hardware.Buffered.SerialPackage
