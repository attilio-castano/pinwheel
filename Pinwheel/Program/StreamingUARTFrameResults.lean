import Pinwheel.Program.StreamingUARTFrame

namespace Pinwheel.Program.StreamingUART.Frame
open Pinwheel.Program.StreamingReady
open QuietTiming FrameSamples FrameCell FrameData FramePrelude

/-- A conventional constant-baud digital frame, with arbitrary other-channel
activity and arbitrary unused host operands. The start edge is index zero. -/
structure StableFrame (p : Profile) (incoming : Nat → Input) (payload : BitVec 8) : Prop where
  start : ∀ n, n < 4*p.Q → (incoming n).rawInputs[p.rxInput.val] = false
  data : ∀ (j : Nat) (within : j < 8) n,
    (4+4*j)*p.Q ≤ n → n < (8+4*j)*p.Q →
      (incoming n).rawInputs[p.rxInput.val] = payload[j]'within
  stop : ∀ n, 36*p.Q ≤ n → n < 40*p.Q → (incoming n).rawInputs[p.rxInput.val] = true

theorem StableFrame.samples (p : Profile) (incoming : Nat → Input) (payload : BitVec 8)
    (frame : StableFrame p incoming payload) : DataSamples p incoming payload := by
  intro j within
  have positive := p.Q_ge4
  apply frame.data j within ((6+4*j)*p.Q)
  all_goals simp only [Nat.add_mul] <;> omega

/-- Decode the chronology of received bits in UART least-significant-first order. -/
def decodeBits (chronology : List Bool) : BitVec 8 :=
  (BitVec.ofBoolListLE chronology).setWidth 8

theorem decode_bits (payload : BitVec 8) : decodeBits (bits payload) = payload := by
  apply BitVec.eq_of_getLsbD_eq
  intro n within
  simp only [decodeBits,BitVec.getLsbD_setWidth,within,decide_true,Bool.true_and,
    BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,bits,List.getElem?_ofFn,
    dif_pos True.intro,Option.getD_some]
  rw [BitVec.getLsbD_eq_getElem within]

/-- No operational transcript is stored: chronology is recovered from the one
queued RX chunk and interpreted by the host's UART-order decoder. -/
structure Received (generation transfer : BitVec 16) (payload : BitVec 8) (s : State a) : Prop where
  count : s.rx.count.val = 1
  chunk : s.rx.peek = ⟨Streaming.Packing.rxWord (bits payload),⟨7,by decide⟩⟩
  chronology : s.rx.peek.rxBits = bits payload
  decoded : decodeBits s.rx.peek.rxBits = payload
  produced : s.rxProduced = 8#16
  popped : s.rxPopped = 0#16
  txAccepted : s.txAccepted = 0#16
  txConsumed : s.txConsumed = 0#16
  txCount : s.tx.count.val = 0
  remaining : s.remaining = 0#16
  total : s.total = 8#16
  generation : s.generation = generation
  transfer : s.transfer = transfer

theorem received_afterData {a : Nat} (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8) :
    Received generation transfer payload (afterData (a := a) p generation transfer payload) := by
  have receipt := data_receipt (a := a) p generation transfer payload
  have chronology : (afterData (a := a) p generation transfer payload).rx.peek.rxBits = bits payload := by
    rw [receipt.2]
    change Streaming.Packing.rxBits (Streaming.Packing.rxWord (bits payload)) 8 = _
    simpa only [bits_length] using Streaming.Packing.rxWord_roundtrip (bits payload) (by simp [bits_length])
  exact ⟨receipt.1,receipt.2,chronology,by rw [chronology,decode_bits],rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem Received.sampleInputs (generation transfer : BitVec 16) (payload : BitVec 8)
    (s : State a) (received : Received generation transfer payload s) (inputs : List Input) :
    Received generation transfer payload (sampleInputs s inputs) := by
  rw [sampleInputs_pair]
  rcases received with ⟨count,chunk,chronology,decoded,produced,popped,accepted,consumed,txCount,remaining,total,gen,tag⟩
  exact ⟨count,chunk,chronology,decoded,produced,popped,accepted,consumed,txCount,remaining,total,gen,tag⟩

theorem received_completed {a : Nat} (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8) :
    Received generation transfer payload (completed (a := a) p generation transfer payload) := by
  rcases received_afterData (a := a) p generation transfer payload with
    ⟨count,chunk,chronology,decoded,produced,popped,accepted,consumed,txCount,remaining,total,gen,tag⟩
  exact ⟨count,chunk,chronology,decoded,produced,popped,accepted,consumed,txCount,remaining,total,gen,tag⟩

theorem received_badStop {a : Nat} (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8) :
    Received generation transfer payload (badStop (a := a) p generation transfer payload) := by
  rcases received_afterData (a := a) p generation transfer payload with
    ⟨count,chunk,chronology,decoded,produced,popped,accepted,consumed,txCount,remaining,total,gen,tag⟩
  exact ⟨count,chunk,chronology,decoded,produced,popped,accepted,consumed,txCount,remaining,total,gen,tag⟩

theorem good_frame_result {a : Nat} (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopHigh : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = true) :
    let finalState := run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 (38*p.Q+4))
    finalState.phase = .completed ∧ Received generation transfer payload finalState := by
  dsimp only
  rw [good_frame p generation transfer payload incoming quiet falling startLow samples stopHigh]
  exact ⟨by rw [sampleInputs_phase]; rfl,
    Received.sampleInputs generation transfer payload _ (received_completed p generation transfer payload) _⟩

theorem bad_stop_result {a : Nat} (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopLow : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = false) :
    let finalState := run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 (38*p.Q+3))
    finalState.phase = .fault ∧ Received generation transfer payload finalState := by
  dsimp only
  rw [bad_stop p generation transfer payload incoming quiet falling startLow samples stopLow]
  exact ⟨by rw [sampleInputs_phase]; rfl,
    Received.sampleInputs generation transfer payload _ (received_badStop p generation transfer payload) _⟩

theorem stable_frame_result {a : Nat} (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (frame : StableFrame p incoming payload) :
    let finalState := run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 (38*p.Q+4))
    finalState.phase = .completed ∧ Received generation transfer payload finalState := by
  have positive := p.Q_ge4
  exact good_frame_result p generation transfer payload incoming quiet
    (frame.start 0 (by omega)) (frame.start (2*p.Q) (by omega)) (frame.samples p incoming payload)
    (frame.stop (38*p.Q) (by omega) (by omega))

end Pinwheel.Program.StreamingUART.Frame
