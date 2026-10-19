import Pinwheel.Program.StreamingUARTFramePrelude

/-! Autonomous one-frame UART source semantics. The pin contract is stated at
raw sample instants, and all state/results are derived from actual steps. -/
namespace Pinwheel.Program.StreamingUART.Frame
open Pinwheel.Program.StreamingReady
open QuietTiming FrameSamples FrameControl FrameCell FrameData FramePrelude

/-- UART payload order on the pin is least-significant bit first. -/
def DataSamples (p : Profile) (incoming : Nat → Input) (payload : BitVec 8) : Prop :=
  ∀ (j : Nat) (within : j < 8),
    (incoming ((6+4*j)*p.Q)).rawInputs[p.rxInput.val] = payload[j]'within

def afterData (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8) : State a :=
  bytePrefix (dataBase p generation transfer) payload 8

theorem bytePrefix_samples (s : State a) (payload : BitVec 8) (k : Nat) (inputs : List Input) :
    bytePrefix (sampleInputs s inputs) payload k = sampleInputs (bytePrefix s payload k) inputs := by
  simp [bytePrefix,sampleInputs_pair]

theorem data_run {a : Nat} (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 (36*p.Q+3)) =
      sampleInputs (afterData p generation transfer payload) (clocks incoming 0 (36*p.Q+3)) := by
  have split : 36*p.Q+3 = (4*p.Q+3)+(4*p.Q)*8 := by omega
  rw [split,clocks_add,run_append,prelude p generation transfer incoming quiet falling startLow]
  have bytes := data_prefix p
    (sampleInputs (dataBase (a := a) p generation transfer) (clocks incoming 0 (4*p.Q+3)))
    payload incoming (0+(4*p.Q+3)) 8 (by decide)
    (by simp [sampleInputs_pair,dataBase]) quiet
    (by
      intro j bound
      have q := p.Q_ge4
      have index : 0+(4*p.Q+3)+(4*p.Q)*j+2*p.Q-3 = (6+4*j)*p.Q := by
        simp only [Nat.add_mul,Nat.mul_assoc,Nat.mul_comm p.Q j]
        omega
      rw [index]
      exact samples j bound)
  have initial : bytePrefix
      (sampleInputs (dataBase (a := a) p generation transfer) (clocks incoming 0 (4*p.Q+3))) payload 0 =
      sampleInputs (dataBase (a := a) p generation transfer) (clocks incoming 0 (4*p.Q+3)) := by
    apply bytePrefix_zero
    all_goals simp [sampleInputs_pair,dataBase,Arm.armed]
  rw [initial] at bytes
  rw [bytes,bytePrefix_samples,← FrameData.sampleInputs_append]
  rfl

def afterTail (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8) : State a :=
  pulseFinish (afterData p generation transfer payload) (pulseA p)

theorem tail_run {a : Nat} (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 (38*p.Q+1)) =
      sampleInputs (afterTail p generation transfer payload) (clocks incoming 0 (38*p.Q+1)) := by
  have q := p.Q_ge4
  have split : 38*p.Q+1 = (36*p.Q+3)+((pulseA p).lowDuration.val+(pulseA p).highDuration.val+4) := by
    simp only [pulseA]
    omega
  rw [split,clocks_add,run_append,data_run p generation transfer payload incoming quiet falling startLow samples]
  have pulse := pulse_run (image p).program
    (sampleInputs (afterData (a := a) p generation transfer payload) (clocks incoming 0 (36*p.Q+3))) (pulseA p)
    (clocks incoming (0+(36*p.Q+3)) ((pulseA p).lowDuration.val+(pulseA p).highDuration.val+4))
    (by simp [sampleInputs_pair,afterData,bytePrefix])
    (by rw [sampleInputs_pc]; change (image p).program.fetch 6 = _; rw [source_fetch p 6 (by decide)]; rfl)
    (clocks_quiet incoming quiet _ _) (clocks_length _ _ _)
  rw [pulse,pulseFinish_samples,pulseFinish_samples,← FrameData.sampleInputs_append]
  rfl

def afterStop (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8) : State a :=
  guardExit (afterTail p generation transfer payload) ⟨0,0⟩ (checkStop p)

theorem stop_good {a : Nat} (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopHigh : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = true) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 (38*p.Q+3)) =
      sampleInputs (afterStop p generation transfer payload) (clocks incoming 0 (38*p.Q+3)) := by
  have split : 38*p.Q+3 = (38*p.Q+1)+2 := by omega
  rw [split,clocks_add,run_append,tail_run p generation transfer payload incoming quiet falling startLow samples]
  simp only [Nat.zero_add,clocks_two]
  have firstSample : (sampleInputs (afterTail (a := a) p generation transfer payload)
      (clocks incoming 0 (38*p.Q+1))).samplerFirst = (incoming (38*p.Q)).rawInputs := by
    change (sampled _ _).samplerFirst = _
    simpa only [Nat.zero_add] using sampled_last (afterTail (a := a) p generation transfer payload) incoming 0 (38*p.Q)
  have guardStep := guard_success (image p).program
    (sampleInputs (afterTail (a := a) p generation transfer payload) (clocks incoming 0 (38*p.Q+1)))
    ⟨0,0⟩ (checkStop p) (incoming (38*p.Q+1)) (incoming (38*p.Q+1+1)) (quiet _) (quiet _)
    (by simp [sampleInputs_pair,afterTail,pulseFinish])
    (by rw [sampleInputs_pc]; change (image p).program.fetch 7 = _; rw [source_fetch p 7 (by decide)]; rfl)
    (by rw [checkStop_matches,firstSample,stopHigh])
  rw [guardStep,guardExit_samples,← FrameData.sampleInputs_append]
  rfl

def completed (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8) : State a :=
  (afterStop p generation transfer payload).stop (image p).program false

def badStop (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8) : State a :=
  guardFault (image p).program (afterTail p generation transfer payload) ⟨0,0⟩ (checkStop p)

/-- All quarter periods 4..128, both input selectors, all bytes, and arbitrary
raw values away from the declared sample instants. No host data action is used. -/
theorem good_frame {a : Nat} (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopHigh : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = true) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 (38*p.Q+4)) =
      sampleInputs (completed p generation transfer payload) (clocks incoming 0 (38*p.Q+4)) := by
  have split : 38*p.Q+4 = (38*p.Q+3)+1 := by omega
  rw [split,clocks_add,run_append,stop_good p generation transfer payload incoming quiet falling startLow samples stopHigh]
  simp only [Nat.zero_add,clocks_one]
  change step (image p).program (incoming (38*p.Q+3))
    (sampleInputs (afterStop p generation transfer payload) (clocks incoming 0 (38*p.Q+3))) = _
  rw [halt_step _ _ _ (quiet _)
    (by simp [sampleInputs_pair,afterStop,guardExit])
    (by rw [sampleInputs_pc]; change (image p).program.fetch 8 = _; rw [source_fetch p 8 (by decide)]; rfl)]
  simp [sampleInputs_pair,completed,State.stop,State.sample]

theorem bad_stop {a : Nat} (p : Profile) (generation transfer : BitVec 16)
    (payload : BitVec 8) (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopLow : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = false) :
    run (image p).program (Arm.armed (a := a) p generation transfer) (clocks incoming 0 (38*p.Q+3)) =
      sampleInputs (badStop p generation transfer payload) (clocks incoming 0 (38*p.Q+3)) := by
  have split : 38*p.Q+3 = (38*p.Q+1)+2 := by omega
  rw [split,clocks_add,run_append,tail_run p generation transfer payload incoming quiet falling startLow samples]
  simp only [Nat.zero_add,clocks_two]
  have firstSample : (sampleInputs (afterTail (a := a) p generation transfer payload)
      (clocks incoming 0 (38*p.Q+1))).samplerFirst = (incoming (38*p.Q)).rawInputs := by
    change (sampled _ _).samplerFirst = _
    simpa only [Nat.zero_add] using sampled_last (afterTail (a := a) p generation transfer payload) incoming 0 (38*p.Q)
  have guardStep := guard_failure (image p).program
    (sampleInputs (afterTail (a := a) p generation transfer payload) (clocks incoming 0 (38*p.Q+1)))
    ⟨0,0⟩ (checkStop p) (incoming (38*p.Q+1)) (incoming (38*p.Q+1+1)) (quiet _) (quiet _)
    (by simp [sampleInputs_pair,afterTail,pulseFinish])
    (by rw [sampleInputs_pc]; change (image p).program.fetch 7 = _; rw [source_fetch p 7 (by decide)]; rfl)
    rfl (by rw [checkStop_matches,firstSample,stopLow])
    (by simp [sampleInputs_pair,afterTail,pulseFinish,afterData,bytePrefix])
  rw [guardStep,guardFault_samples,← FrameData.sampleInputs_append]
  rfl

theorem data_receipt {a : Nat} (p : Profile) (generation transfer : BitVec 16) (payload : BitVec 8) :
    (afterData (a := a) p generation transfer payload).rx.count.val = 1 ∧
      (afterData (a := a) p generation transfer payload).rx.peek =
        ⟨Streaming.Packing.rxWord (bits payload),⟨7,by decide⟩⟩ := by
  simp [afterData,bytePrefix,Streaming.Queue.empty,Streaming.Queue.tick,Streaming.Queue.willPush,
    Streaming.Queue.willPop,Streaming.Queue.writable,Streaming.queueDepth_positive,Streaming.Queue.peek]

end Pinwheel.Program.StreamingUART.Frame
