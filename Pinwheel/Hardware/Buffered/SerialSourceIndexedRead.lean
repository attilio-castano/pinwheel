import Pinwheel.Hardware.Buffered.GenericReadback
import Pinwheel.Hardware.Buffered.SerialSourceReceipt

/-! The two indexed RX-read bits in a frozen serial receipt are grounded in
the retained source completion at the pre-capture cut. Exact MISO serialization
of this same frozen word is supplied by SerialSourceRead.capture_read. -/
namespace Pinwheel.Hardware.Buffered.SerialSourceIndexedRead
open Pinwheel.Hardware Pinwheel.Program

theorem captured_read_fields (record : Serial.State) (input : Serial.Inputs) :
    (record.capturedResponse input).extractLsb' 73 1 = input.status .readValid ∧
      (record.capturedResponse input).extractLsb' 74 1 = input.status .readBit := by
  constructor
  all_goals rw [← Serial.capturedResponse_correct record input]
  all_goals simp (disch := decide) only [Serial.capturedResponse, Serial.packedStatus,
    Expr.eval, Serial.Inputs.values, Serial.State.values,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le]
  all_goals simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.extractLsb'_eq_self]
  all_goals rfl

theorem capture_readback {program : Program.Buffered.Program}
    {layout : GenericCertificate.Layout program} {payload : BitVec 32}
    (s : SerialPackage.State) (source : Program.Buffered.State)
    (related : Refinement.RelatedSram program layout payload s.controller source)
    (retained : s.controller.core .retained = 1)
    (pin : SerialPackage.Pins) (cold : pin.cold = false) (capture : s.record.capture = true) :
    ∃ e outcome,
      source.buffers.slot = .completed ⟨e, outcome⟩ ∧
      Transfer.step Refinement.capacity source.buffers (.read source.owner) =
        ⟨source.buffers, .result ⟨e, outcome⟩⟩ ∧
      (s.step pin).record.response.extractLsb' 73 1 =
        BitVec.ofBool (decide (((s.coreInputs pin) .readIndex).toNat < e.rx.length)) ∧
      (s.step pin).record.response.extractLsb' 74 1 =
        BitVec.ofBool (e.rx.getD ((s.coreInputs pin) .readIndex).toNat false) := by
  obtain ⟨e, outcome, slot, read, valid, bit⟩ :=
    Refinement.retained_read related retained (s.coreInputs pin)
  have fields := captured_read_fields s.record (s.inputs pin)
  rw [← (s.capture_response pin cold capture).1] at fields
  exact ⟨e, outcome, slot, read, fields.1.trans valid, fields.2.trans bit⟩

end Pinwheel.Hardware.Buffered.SerialSourceIndexedRead
