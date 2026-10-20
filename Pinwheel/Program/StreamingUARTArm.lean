import Pinwheel.Program.StreamingUARTFrameControl
import Pinwheel.Program.StreamingUARTHostQuiet

/-! Arming is reached from the actual START reset, with arbitrary old sampler
contents. No assumed prepared receiver or initial RX-space premise is used. -/
namespace Pinwheel.Program.StreamingUART.Arm
open Pinwheel.Program.StreamingReady
set_option linter.unusedSimpArgs false

def mark : Input := {rawInputs := 3}

def armed (p : Profile) (generation transfer : BitVec 16) : State a :=
  {phase := .waiting,pc := 1,current := .driveWait ⟨0,0⟩ (startGuard p),
   total := 8,remaining := 8,samplerFirst := 3,samplerSecond := 3,
   generation := generation,transfer := transfer}

private theorem mark_selected (channel : Fin 2) : (3#2)[channel.val] = true := by
  revert channel
  decide +kernel

private theorem queue_idle (q : Queue a) : q.tick none false = q := by cases q; rfl

theorem six_from_start (p : Profile) (s : State a) (start : Input) (count : start.startCount = 8) :
    run (image p).program (s.start (image p).program start) (List.replicate 6 mark) =
      armed p s.generation (s.transfer+1) := by
  have fetch0 : (image p).program.fetch 0 = some (.driveWait ⟨0,0⟩ (markGuard p)) := by
    simpa only [source,List.getElem?_cons_zero] using source_fetch p 0 (by decide)
  have fetch1 : (image p).program.fetch 1 = some (.driveWait ⟨0,0⟩ (startGuard p)) := by
    simpa only [source,List.getElem?_cons_succ,List.getElem?_cons_zero] using source_fetch p 1 (by decide)
  cases selected : start.rawInputs[p.rxInput.val]
  all_goals simp [run,List.replicate,step,State.start,count,mark,clock,engine,fetch0,fetch1,
    State.sample,State.hostPush,State.hostPop,State.enginePop,State.enginePush,
    State.emittingCapture,State.captures,State.timedOut,State.waitReady,
    Instruction.guard,Instruction.isStream,WaitLimit.initialCountdown,WaitLimit.expires,WaitLimit.poll,
    FrameControl.mark_matches,FrameControl.start_matches,mark_selected,selected,
    show (markGuard p).limit = .unbounded from rfl,
    show (startGuard p).limit = .unbounded from rfl,armed,queue_idle,Streaming.Queue.willPush,Streaming.Queue.willPop,
    Bool.beq_eq_decide_eq]

theorem admitted_six (p : Profile) (s : State a) (start : Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8) :
    run (image p).program (step (image p).program start s) (List.replicate 6 mark) =
      armed p s.generation (s.transfer+1) := by
  have accepted := admitted
  simp only [Bool.and_eq_true,beq_iff_eq] at accepted
  have started : step (image p).program start s = s.start (image p).program start := by
    simp [step,runtime.1,accepted.1,accepted.2]
  rw [started]
  exact six_from_start p s start count

theorem armed_mark (p : Profile) (generation transfer : BitVec 16) :
    step (image p).program mark (armed p generation transfer : State a) = armed p generation transfer := by
  rw [FrameControl.wait_unbounded_miss (image p).program _ mark ⟨0,0⟩ (startGuard p)
    (by exact ⟨rfl,by decide⟩) rfl rfl rfl rfl rfl
    (by simp [armed,FrameControl.start_matches,mark_selected])]
  rfl

theorem run_armed (p : Profile) (generation transfer : BitVec 16) (clocks : Nat) :
    run (image p).program (armed p generation transfer : State a) (List.replicate clocks mark) =
      armed p generation transfer := by
  induction clocks with
  | zero => rfl
  | succ clocks induction =>
    change run (image p).program (step (image p).program mark (armed p generation transfer : State a))
      (List.replicate clocks mark) = _
    rw [armed_mark,induction]

theorem quiet_marks (program : Program) (s : State a) (inputs : List Input)
    (quiet : ∀ i ∈ inputs, QuietTiming.Quiet i) (raw : ∀ i ∈ inputs, i.rawInputs = 3) :
    run program s inputs = run program s (List.replicate inputs.length mark) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest induction =>
    change run program (step program i s) rest =
      run program (step program mark s) (List.replicate rest.length mark)
    rw [HostQuiet.step_canonical program s i (quiet i (by simp)),raw i (by simp)]
    exact induction _ (fun j member => quiet j (by simp [member])) (fun j member => raw j (by simp [member]))

/-- Every actual quiet MARK prefix of at least six clocks reaches the same full
armed state, independent of the old synchronizers and START's raw sample. -/
theorem admitted_marks (p : Profile) (s : State a) (start : Input) (inputs : List Input)
    (runtime : start.Runtime) (admitted : (start.command == 3 && s.canStart start) = true)
    (count : start.startCount = 8) (quiet : ∀ i ∈ inputs, QuietTiming.Quiet i)
    (raw : ∀ i ∈ inputs, i.rawInputs = 3) (long : 6 ≤ inputs.length) :
    run (image p).program (step (image p).program start s) inputs =
      armed p s.generation (s.transfer+1) := by
  rw [quiet_marks _ _ inputs quiet raw]
  have length : inputs.length = 6+(inputs.length-6) := by omega
  rw [length,← List.replicate_append_replicate,QuietTiming.run_append,admitted_six p s start runtime admitted count]
  exact run_armed p _ _ _

end Pinwheel.Program.StreamingUART.Arm
