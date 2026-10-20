import Pinwheel.Hardware.Buffered.SerialPackage
import Pinwheel.Hardware.Buffered.SerialCorrespondenceFrames

/-! The actual sampled serial/SRAM package inherits frame delivery from its
independent frontend model. The frame witnesses constrain sampled CS/SCK/MOSI;
they place no constraint on live status or raw protocol inputs. Every sample
continues to appear in the actual controller command history. -/
namespace Pinwheel.Hardware.Buffered.SerialPackage
open Pinwheel.Hardware
open Serial.Frames

theorem State.frontendInputs_append (s : State) (a b : List Pins) :
    s.frontendInputs (a ++ b) = s.frontendInputs a ++ (s.run a).frontendInputs b := by
  induction a generalizing s with
  | nil => rfl
  | cons p rest ih => simp only [State.frontendInputs, State.run, List.foldl_cons,
      List.cons_append, ih]
  done

theorem State.record_run (s : State) (pins : List Pins) :
    (s.run pins).record = s.record.run (s.frontendInputs pins) := by
  induction pins generalizing s with
  | nil => rfl
  | cons p rest ih =>
    change ((s.step p).run rest).record =
      (s.record.step (s.inputs p)).run ((s.step p).frontendInputs rest)
    rw [← s.record_step]
    exact ih (s.step p)
  done

theorem State.commands_record (s : State) (pins : List Pins) :
    s.commands pins = fed s.record (s.frontendInputs pins) := by
  induction pins generalizing s with
  | nil => rfl
  | cons p rest ih =>
    change (fun {w} (port : Reactive.Input w) => s.coreInputs p port) :: (s.step p).commands rest =
      (fun {w} (port : Reactive.Input w) => s.record.coreInput (s.inputs p) port) ::
        fed (s.record.step (s.inputs p)) ((s.step p).frontendInputs rest)
    congr 1
    · funext w port
      exact s.record_coreInputs p port
    · rw [ih, s.record_step]
  done

theorem State.frame_closed (s : State) (word : BitVec 160) (assert close : Pins)
    (samples : List Pins) (available : Available s.record)
    (low : Low (s.inputs assert))
    (bits : IsBits (wordBits word) ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) :
    Closed word (s.run (assert :: (samples ++ [close]))).record := by
  rw [s.record_run]
  simp only [State.frontendInputs, State.frontendInputs_append]
  apply Serial.Frames.frame_closed s.record word (s.inputs assert)
  · exact available
  · exact low
  · exact bits
  · exact idle
  done

theorem State.frame_quiet (s : State) (word : BitVec 160) (assert close : Pins)
    (samples : List Pins) (available : Available s.record)
    (low : Low (s.inputs assert))
    (bits : IsBits (wordBits word) ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) :
    ∀ input ∈ s.commands (assert :: (samples ++ [close])), Quiet input := by
  rw [s.commands_record]
  simp only [State.frontendInputs, State.frontendInputs_append]
  apply Serial.Frames.frame_quiet s.record word (s.inputs assert)
  · exact available
  · exact low
  · exact bits
  · exact idle
  done

theorem State.closed_coreInputs (s : State) (p : Pins) (h : Closed word s.record)
    (port : Reactive.Input w) :
    s.coreInputs p port =
      ({count := 160, request := word, dispatch := true, code := codeOf word} : Serial.State).coreInput
        (s.inputs p) port := by
  rw [s.record_coreInputs]
  exact congrFun (congrFun (h.coreInputs (s.inputs p)) w) port
  done

end Pinwheel.Hardware.Buffered.SerialPackage
