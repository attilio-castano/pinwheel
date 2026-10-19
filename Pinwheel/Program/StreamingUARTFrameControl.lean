import Pinwheel.Program.StreamingUARTQuiet
import Pinwheel.Program.StreamingUARTFrameSamples

namespace Pinwheel.Program.StreamingUART.FrameControl
open Pinwheel.Program.StreamingReady

private theorem selected_high (channel : Fin 2) (sample : BitVec 2) :
    ((sample &&& (1#2 <<< channel.val)) == (1#2 <<< channel.val)) = sample[channel.val] := by
  revert channel sample
  decide +kernel

private theorem selected_low (channel : Fin 2) (sample : BitVec 2) :
    ((sample &&& (1#2 <<< channel.val)) == 0#2) = !sample[channel.val] := by
  revert channel sample
  decide +kernel

theorem mark_matches (p : Profile) (sample : BitVec 2) :
    (markGuard p).matches sample = sample[p.rxInput.val] := selected_high _ _

theorem start_matches (p : Profile) (sample : BitVec 2) :
    (startGuard p).matches sample = !sample[p.rxInput.val] := selected_low _ _

theorem checkStart_matches (p : Profile) (sample : BitVec 2) :
    (checkStart p).matches sample = !sample[p.rxInput.val] := selected_low _ _

theorem checkStop_matches (p : Profile) (sample : BitVec 2) :
    (checkStop p).matches sample = sample[p.rxInput.val] := selected_high _ _

private theorem queue_idle (q : Queue a) : q.tick none false = q := by
  cases q
  rfl

/-- Fetching a standalone guard has no queue or sample side effect beyond its
one ordinary sampler clock. No phase/output conclusion is assumed. -/
theorem fetch_wait (program : Program) (s : State a) (i : Input) (pins : Pins) (guard : Guard)
    (runtime : i.Runtime) (noPush : i.txPush = false) (noPop : i.rxPop = false)
    (phase : s.phase = .fetch) (fetch : program.fetch s.pc.toNat = some (.driveWait pins guard)) :
    step program i s = {s.sample i.rawInputs with
      phase := .waiting
      current := .driveWait pins guard,pins := pins,countdown := guard.limit.initialCountdown} := by
  rw [step_busy_eq_clock program s i runtime (by simp [phase,Phase.busy])]
  simp [clock,engine,phase,fetch,State.sample,State.hostPush,State.hostPop,noPush,noPop,
    State.enginePop,State.enginePush,State.timedOut,State.emittingCapture,State.captures,queue_idle,Bool.beq_eq_decide_eq,Streaming.Queue.willPush,Streaming.Queue.willPop]


theorem wait_ready (program : Program) (s : State a) (i : Input) (pins : Pins) (guard : Guard)
    (runtime : i.Runtime) (noPush : i.txPush = false) (noPop : i.rxPop = false)
    (phase : s.phase = .waiting) (current : s.current = .driveWait pins guard)
    (ready : guard.matches s.samplerSecond = true) :
    step program i s = {s.sample i.rawInputs with phase := .fetch,pc := s.pc+1,countdown := 0} := by
  rw [step_busy_eq_clock program s i runtime (by simp [phase,Phase.busy])]
  simp [clock,engine,phase,current,State.waitReady,ready,Instruction.isStream,Instruction.guard,State.sample,
    State.hostPush,State.hostPop,noPush,noPop,State.enginePop,State.enginePush,State.timedOut,
    State.emittingCapture,State.captures,queue_idle,Bool.beq_eq_decide_eq,
    Streaming.Queue.willPush,Streaming.Queue.willPop]

theorem wait_unbounded_miss (program : Program) (s : State a) (i : Input) (pins : Pins) (guard : Guard)
    (runtime : i.Runtime) (noPush : i.txPush = false) (noPop : i.rxPop = false)
    (phase : s.phase = .waiting) (current : s.current = .driveWait pins guard)
    (limit : guard.limit = .unbounded) (ready : guard.matches s.samplerSecond = false) :
    step program i s = s.sample i.rawInputs := by
  rw [step_busy_eq_clock program s i runtime (by simp [phase,Phase.busy])]
  simp [clock,engine,phase,current,State.waitReady,ready,Instruction.isStream,Instruction.guard,
    State.sample,State.hostPush,State.hostPop,noPush,noPop,State.enginePop,State.enginePush,
    State.timedOut,State.emittingCapture,State.captures,queue_idle,Bool.beq_eq_decide_eq,
    Streaming.Queue.willPush,Streaming.Queue.willPop,limit,WaitLimit.expires,WaitLimit.poll]

theorem wait_one_fault (program : Program) (s : State a) (i : Input) (pins : Pins) (guard : Guard)
    (runtime : i.Runtime) (noPush : i.txPush = false) (noPop : i.rxPop = false)
    (phase : s.phase = .waiting) (current : s.current = .driveWait pins guard)
    (limit : guard.limit = .misses 0) (zero : s.countdown = 0#8)
    (ready : guard.matches s.samplerSecond = false) (noPartial : s.rxUsed = 0#6) :
    step program i s = {s.sample i.rawInputs with
      phase := .fault
      pins := program.idle
      rxPartial := 0
      rxUsed := 0} := by
  rw [step_busy_eq_clock program s i runtime (by simp [phase,Phase.busy])]
  simp [clock,engine,phase,current,State.waitReady,ready,Instruction.isStream,Instruction.guard,
    State.sample,State.hostPush,State.hostPop,noPush,noPop,State.enginePop,State.enginePush,
    State.timedOut,queue_idle,Bool.beq_eq_decide_eq,
    Streaming.Queue.willPush,Streaming.Queue.willPop,limit,WaitLimit.expires,zero,
    State.timeoutFault,State.timeoutChunk,noPartial]

open QuietTiming

def guardExit (s : State a) (pins : Pins) (guard : Guard) : State a :=
  {s with phase := .fetch,pc := s.pc+1,countdown := 0,current := .driveWait pins guard,pins := pins}

def guardFault (program : Program) (s : State a) (pins : Pins) (guard : Guard) : State a :=
  {s with
    phase := .fault,countdown := 0,current := .driveWait pins guard,
    pins := program.idle,rxPartial := 0,rxUsed := 0}

theorem guard_success (program : Program) (s : State a) (pins : Pins) (guard : Guard)
    (first second : Input) (quietFirst : Quiet first) (quietSecond : Quiet second)
    (phase : s.phase = .fetch) (fetch : program.fetch s.pc.toNat = some (.driveWait pins guard))
    (ready : guard.matches s.samplerFirst = true) :
    run program s [first,second] = sampleInputs (guardExit s pins guard) [first,second] := by
  have enter := fetch_wait program s first pins guard (quietFirst.runtime _) quietFirst.tx quietFirst.rx phase fetch
  have success := wait_ready program
    {s.sample first.rawInputs with
      phase := .waiting,current := .driveWait pins guard,pins := pins,
      countdown := guard.limit.initialCountdown}
    second pins guard (quietSecond.runtime _) quietSecond.tx quietSecond.rx rfl rfl ready
  change step program second (step program first s) = _
  rw [enter,success]
  rfl

theorem guard_failure (program : Program) (s : State a) (pins : Pins) (guard : Guard)
    (first second : Input) (quietFirst : Quiet first) (quietSecond : Quiet second)
    (phase : s.phase = .fetch) (fetch : program.fetch s.pc.toNat = some (.driveWait pins guard))
    (limit : guard.limit = .misses 0) (unready : guard.matches s.samplerFirst = false)
    (noPartial : s.rxUsed = 0#6) :
    run program s [first,second] = sampleInputs (guardFault program s pins guard) [first,second] := by
  have enter := fetch_wait program s first pins guard (quietFirst.runtime _) quietFirst.tx quietFirst.rx phase fetch
  have failure := wait_one_fault program
    {s.sample first.rawInputs with
      phase := .waiting,current := .driveWait pins guard,pins := pins,
      countdown := guard.limit.initialCountdown}
    second pins guard (quietSecond.runtime _) quietSecond.tx quietSecond.rx rfl rfl limit
    (by rw [limit]; rfl) unready noPartial
  change step program second (step program first s) = _
  rw [enter,failure]
  simp only [State.sample,guardFault,limit]
  rfl

theorem halt_step (program : Program) (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .fetch) (fetch : program.fetch s.pc.toNat = some .halt) :
    step program i s = (s.stop program false).sample i.rawInputs := by
  rw [step_busy_eq_clock program s i (quiet.runtime _) (by simp [phase,Phase.busy])]
  simp [clock,engine,phase,fetch,State.stop,State.sample,State.hostPush,State.hostPop,quiet.tx,quiet.rx,
    State.enginePop,State.enginePush,State.timedOut,State.emittingCapture,State.captures,queue_idle,
    Bool.beq_eq_decide_eq,Streaming.Queue.willPush,Streaming.Queue.willPop]

theorem stream_fetch (p : Profile) (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .fetch) (pc : s.pc = 5#7) (remaining : s.remaining ≠ 0#16) :
    step (image p).program i s = {s.sample i.rawInputs with
      phase := .boundary,current := .stream (cell p) none,pins := ⟨0,0⟩} := by
  have fetch : (image p).program.fetch s.pc.toNat = some (.stream (cell p) none) := by
    rw [pc]
    change (image p).program.fetch 5 = _
    rw [source_fetch p 5 (by decide)]
    rfl
  rw [step_busy_eq_clock (image p).program s i (quiet.runtime _) (by simp [phase,Phase.busy])]
  simp [clock,engine,phase,fetch,State.sample,State.hostPush,State.hostPop,quiet.tx,quiet.rx,
    State.enginePop,State.enginePush,State.timedOut,State.emittingCapture,State.captures,queue_idle,
    Bool.beq_eq_decide_eq,Streaming.Queue.willPush,Streaming.Queue.willPop,remaining,
    cell,Streaming.Cell.basePins]

end Pinwheel.Program.StreamingUART.FrameControl
