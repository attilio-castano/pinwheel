import Pinwheel.Hardware.Buffered.SerialSourceRead

/-! Sampled request frames clock the source while the frontend receives bits.
The opcode bound below excludes wire RESET/POR before command delivery; no
ideal delivered-command trace is supplied as a premise. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceRequest
open Pinwheel.Hardware Pinwheel.Program Serial.Frames

def ExecutionOpcode (word : BitVec 160) : Prop :=
  (word.extractLsb' 144 4).toNat < 7

theorem frame_source {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    (s : SerialPackage.State) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload s.controller source)
    (word : BitVec 160) (assert close : SerialPackage.Pins) (samples : List SerialPackage.Pins)
    (available : Available s.record) (low : Low (s.inputs assert))
    (bits : IsBits (wordBits word) ((s.step assert).frontendInputs samples))
    (idle : close.cold = false ∧ close.csn = true) :
    let pins := assert :: (samples ++ [close])
    Closed word (s.run pins).record ∧
      Refinement.RelatedSram program layout payload (s.run pins).controller
        (SerialSourceRead.sourceRun program source pins) :=
  ⟨s.frame_closed word assert close samples available low bits idle,
    SerialSourceRead.quiet_run related _ (s.frame_quiet word assert close samples available low bits idle)⟩

theorem execution_inputs (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (word : BitVec 160) (closed : Closed word s.record)
    (cold : pin.cold = false) (opcode : ExecutionOpcode word) :
    s.coreInputs pin .initialize = 0 ∧ s.coreInputs pin .command ≠ 7#3 := by
  have bound : Serial.requestOpcode s.record < 7 := by
    simpa only [Serial.requestOpcode, closed.request, ExecutionOpcode,
      BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] using opcode
  constructor
  · rw [s.record_coreInputs pin .initialize]
    simp [Serial.State.coreInput, SerialPackage.State.inputs, SerialPackage.Pins.inputs,
      cold, show (Serial.requestOpcode s.record == 8) = false from by
        simp only [beq_eq_false_iff_ne]; omega]
  · rw [s.record_coreInputs pin .command]
    unfold Serial.State.coreInput
    split
    · rw [Serial.requestField_eq]
      intro same
      have value := congrArg BitVec.toNat same
      simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at value
      change s.record.request.toNat / 2^144 % 8 = 7 at value
      unfold Serial.requestOpcode at bound
      omega
    · change 0#3 ≠ 7#3
      decide +kernel

end Pinwheel.Hardware.Buffered.SerialSourceRequest
