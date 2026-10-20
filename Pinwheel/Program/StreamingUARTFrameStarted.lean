import Pinwheel.Program.StreamingUARTFrameResults

namespace Pinwheel.Program.StreamingUART.Frame
open Pinwheel.Program.StreamingReady
open QuietTiming FrameSamples FrameCell FrameData FramePrelude FrameControl

theorem false_start_result {a : Nat} (p : Profile) (generation transfer : BitVec 16)
    (incoming : Nat → Input) (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startHigh : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = true) :
    let finalState := run (image p).program (Arm.armed (a := a) p generation transfer)
      (clocks incoming 0 (2*p.Q+3))
    finalState.phase = .fault ∧ finalState.rx.count.val = 0 ∧ finalState.rxProduced = 0#16 ∧
      finalState.txConsumed = 0#16 ∧ finalState.remaining = 8#16 ∧
      finalState.generation = generation ∧ finalState.transfer = transfer := by
  dsimp only
  rw [falseStart p generation transfer incoming quiet falling startHigh]
  simp [sampleInputs_pair,guardFault,afterA,pulseFinish,startExit,Arm.armed,Streaming.Queue.empty]

/-- The receiver is armed by clocks after the actual admitted source START.
The old state and both old synchronizer stages remain arbitrary. -/
theorem admitted_good_frame (p : Profile) (s : State a) (start : Input) (marks : List Input)
    (payload : BitVec 8) (incoming : Nat → Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks,Quiet i) (markRaw : ∀ i ∈ marks,i.rawInputs = 3) (long : 6 ≤ marks.length)
    (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopHigh : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = true) :
    let finalState := run (image p).program s (start :: (marks ++ clocks incoming 0 (38*p.Q+4)))
    finalState.phase = .completed ∧ Received s.generation (s.transfer+1) payload finalState := by
  dsimp only
  change (run (image p).program (step (image p).program start s)
    (marks ++ clocks incoming 0 (38*p.Q+4))).phase = .completed ∧
    Received s.generation (s.transfer+1) payload
      (run (image p).program (step (image p).program start s) (marks ++ clocks incoming 0 (38*p.Q+4)))
  rw [run_append,Arm.admitted_marks p s start marks runtime admitted count markQuiet markRaw long]
  exact good_frame_result p s.generation (s.transfer+1) payload incoming quiet falling startLow samples stopHigh

theorem admitted_stable_frame (p : Profile) (s : State a) (start : Input) (marks : List Input)
    (payload : BitVec 8) (incoming : Nat → Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks,Quiet i) (markRaw : ∀ i ∈ marks,i.rawInputs = 3) (long : 6 ≤ marks.length)
    (quiet : ∀ n,Quiet (incoming n)) (frame : StableFrame p incoming payload) :
    let finalState := run (image p).program s (start :: (marks ++ clocks incoming 0 (38*p.Q+4)))
    finalState.phase = .completed ∧ Received s.generation (s.transfer+1) payload finalState := by
  dsimp only
  change (run (image p).program (step (image p).program start s)
    (marks ++ clocks incoming 0 (38*p.Q+4))).phase = .completed ∧
    Received s.generation (s.transfer+1) payload
      (run (image p).program (step (image p).program start s) (marks ++ clocks incoming 0 (38*p.Q+4)))
  rw [run_append,Arm.admitted_marks p s start marks runtime admitted count markQuiet markRaw long]
  exact stable_frame_result p s.generation (s.transfer+1) payload incoming quiet frame

theorem admitted_bad_stop (p : Profile) (s : State a) (start : Input) (marks : List Input)
    (payload : BitVec 8) (incoming : Nat → Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks,Quiet i) (markRaw : ∀ i ∈ marks,i.rawInputs = 3) (long : 6 ≤ marks.length)
    (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startLow : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = false)
    (samples : DataSamples p incoming payload)
    (stopLow : (incoming (38*p.Q)).rawInputs[p.rxInput.val] = false) :
    let finalState := run (image p).program s (start :: (marks ++ clocks incoming 0 (38*p.Q+3)))
    finalState.phase = .fault ∧ Received s.generation (s.transfer+1) payload finalState := by
  dsimp only
  change (run (image p).program (step (image p).program start s)
    (marks ++ clocks incoming 0 (38*p.Q+3))).phase = .fault ∧
    Received s.generation (s.transfer+1) payload
      (run (image p).program (step (image p).program start s) (marks ++ clocks incoming 0 (38*p.Q+3)))
  rw [run_append,Arm.admitted_marks p s start marks runtime admitted count markQuiet markRaw long]
  exact bad_stop_result p s.generation (s.transfer+1) payload incoming quiet falling startLow samples stopLow

theorem admitted_prefix (p : Profile) (s : State a) (start : Input) (marks body : List Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks,Quiet i) (markRaw : ∀ i ∈ marks,i.rawInputs = 3) (long : 6 ≤ marks.length) :
    run (image p).program s (start :: (marks ++ body)) =
      run (image p).program (Arm.armed p s.generation (s.transfer+1)) body := by
  change run (image p).program (step (image p).program start s) (marks ++ body) = _
  rw [run_append,Arm.admitted_marks p s start marks runtime admitted count markQuiet markRaw long]

theorem admitted_false_start (p : Profile) (s : State a) (start : Input) (marks : List Input)
    (incoming : Nat → Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8)
    (markQuiet : ∀ i ∈ marks,Quiet i) (markRaw : ∀ i ∈ marks,i.rawInputs = 3) (long : 6 ≤ marks.length)
    (quiet : ∀ n,Quiet (incoming n))
    (falling : (incoming 0).rawInputs[p.rxInput.val] = false)
    (startHigh : (incoming (2*p.Q)).rawInputs[p.rxInput.val] = true) :
    let finalState := run (image p).program s (start :: (marks ++ clocks incoming 0 (2*p.Q+3)))
    finalState.phase = .fault ∧ finalState.rx.count.val = 0 ∧ finalState.rxProduced = 0#16 ∧
      finalState.txConsumed = 0#16 ∧ finalState.remaining = 8#16 ∧
      finalState.generation = s.generation ∧ finalState.transfer = s.transfer+1 := by
  dsimp only
  rw [admitted_prefix p s start marks _ runtime admitted count markQuiet markRaw long]
  exact false_start_result p s.generation (s.transfer+1) incoming quiet falling startHigh

end Pinwheel.Program.StreamingUART.Frame
