import Pinwheel.Program.StreamingUARTHostQuiet

/-! Source facts used to transport the checked START transaction through actual
host/core feedback. Acceptance and the rejection signal are derived from free
installed state, rather than assumed in a physical execution relation. -/
namespace Pinwheel.Program.StreamingUART.StartFacts
open Pinwheel.Program.StreamingReady

private theorem queue_idle (q : Streaming.Queue a) : q.tick none false = q := by
  cases q
  rfl

theorem free_quiet_step (p : Program) (s : State a) (i : Input)
    (phase : s.phase = .free) (quiet : QuietTiming.Quiet i) :
    step p i s = s.sample i.rawInputs := by
  simp [step,quiet.cold,quiet.command,clock,engine,phase,State.sample,
    State.hostPush,State.hostPop,quiet.tx,quiet.rx,State.enginePop,State.enginePush,
    State.emittingCapture,State.captures,State.timedOut,queue_idle,
    Streaming.Queue.willPush,Streaming.Queue.willPop,Bool.beq_eq_decide_eq]

theorem free_quiet_run (p : Program) (s : State a) (inputs : List Input)
    (phase : s.phase = .free) (quiet : ∀ i ∈ inputs, QuietTiming.Quiet i) :
    run p s inputs = QuietTiming.sampleInputs s inputs := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change run p (step p i s) rest = QuietTiming.sampleInputs (s.sample i.rawInputs) rest
    rw [free_quiet_step p s i phase (quiet i (by simp))]
    exact ih (s.sample i.rawInputs) phase (fun j member => quiet j (by simp [member]))

theorem can_start (s : State a) (i : Input) (phase : s.phase = .free)
    (generation : i.expectedGeneration = s.generation) (room : s.transfer ≠ 65535#16) :
    s.canStart i = true := by
  simp [State.canStart,phase,generation,room]

theorem quiet_rejected (s : State a) (i : Input) (pending : Bool)
    (quiet : QuietTiming.Quiet i) : (s.status pending i).rejected = false := by
  simp [State.status,quiet.command,quiet.tx,quiet.rx]

theorem start_rejected (s : State a) (i : Input) (pending : Bool)
    (command : i.command = 3) (admitted : s.canStart i = true)
    (tx : i.txPush = false) (rx : i.rxPop = false) :
    (s.status pending i).rejected = false := by
  simp [State.status,command,admitted,tx,rx]

theorem accepted_start (p : Program) (s : State a) (i : Input)
    (cold : i.initialize = false) (command : i.command = 3)
    (phase : s.phase = .free) (generation : i.expectedGeneration = s.generation)
    (room : s.transfer ≠ 65535#16) : step p i s = s.start p i := by
  simp [step,cold,command,can_start s i phase generation room]

end Pinwheel.Program.StreamingUART.StartFacts
