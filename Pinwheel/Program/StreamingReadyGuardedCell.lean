import Pinwheel.Program.StreamingReadyTiming
import Pinwheel.Program.StreamingReadyBitTrace

/-! The same bounded WAIT segment serves any guarded cell. The peer proof
identifies the first ready sample. This proof determines the cell's outcome
and accounts for the receive bits at that cut. -/
namespace Pinwheel.Program.StreamingReady.GuardedCell

structure WaitingPrefix (s cut : State a) (trace cutTrace : BitTrace) (misses : Nat) : Prop where
  phase : cut.phase = .waiting
  countdown : cut.countdown.toNat = s.countdown.toNat - misses
  pins : cut.pins = s.pins
  remaining : cut.remaining = s.remaining
  current : cut.current = s.current
  captured : cutTrace.captured = trace.captured

structure CaptureResult (s final : State a) (trace finalTrace : BitTrace) (bit : Bool) : Prop where
  phase : final.phase = .high
  pins : final.pins = s.pins
  remaining : final.remaining = s.remaining
  current : final.current = s.current
  captured : finalTrace.captured = trace.captured ++ [bit]

structure TimeoutResult (p : Program) (s final : State a) (trace finalTrace : BitTrace) : Prop where
  phase : final.phase = .fault
  pins : final.pins = p.idle
  remaining : final.remaining = s.remaining
  partialFlushed : final.rxUsed = 0#6
  partialCleared : final.rxPartial = 0#32
  captured : finalTrace.captured = trace.captured
  recoverable : trace.Related s → s.Structural →
    trace.captured = finalTrace.exported ++ finalTrace.rxQueued.flatMap Streaming.Chunk.rxBits

/-- Observe the poll after a bounded sequence of misses. A pre-edge ready
sample can capture on the last allowed poll. A miss expires at that poll. -/
structure PollResult (p : Program) (s : State a) (trace : BitTrace) (misses : List Input)
    (last : Input) : Prop where
  capture : (run p s misses).waitReady = true →
    s.current.isStream = true → s.current.cell.receive = true →
    CaptureResult s (run p s (misses ++ [last])) trace (traceRun p s trace (misses ++ [last]))
      (run p s misses).samplerSecond[s.current.cell.rxInput.val]
  timeout : (run p s misses).waitReady = false → misses.length = s.countdown.toNat →
    TimeoutResult p s (run p s (misses ++ [last])) trace (traceRun p s trace (misses ++ [last]))

private theorem wait_edge (s : State a) (trace : BitTrace) (i : Input)
    (waiting : s.phase = .waiting) (runtime : i.Runtime) :
    (trace.step s i).captured = trace.captured ++ s.rxEvent := by
  simp [BitTrace.step, runtime.1, (show i.command ≠ 15#4 from runtime.2), State.canStart, State.canRelease, waiting,
    Phase.retained, BitTrace.clock]

private theorem trace_append (p : Program) (s : State a) (trace : BitTrace) (before after : List Input) :
    traceRun p s trace (before ++ after) = traceRun p (run p s before) (traceRun p s trace before) after :=
  match before with
  | [] => rfl
  | i :: rest => trace_append p (step p i s) (trace.step s i) rest after

private theorem misses_preserve_captures (p : Program) (s : State a) (trace : BitTrace)
    (misses : List Input) (budget : Fin 255) (waiting : s.phase = .waiting)
    (limit : s.current.guard.limit = .misses budget) (history : MissHistory p s misses)
    (within : misses.length ≤ s.countdown.toNat) :
    (traceRun p s trace misses).captured = trace.captured := by
  induction misses generalizing s trace with
  | nil => rfl
  | cons i rest ih =>
    rcases history with ⟨runtime, miss, later⟩
    have one : [i].length ≤ s.countdown.toNat :=
      Nat.le_trans (Nat.succ_le_succ (Nat.zero_le rest.length)) within
    obtain ⟨phase, count, _, _, current⟩ :=
      bounded_wait_prefix p s [i] budget waiting limit ⟨runtime, miss, True.intro⟩ one
    have nextCount : (step p i s).countdown.toNat = s.countdown.toNat - 1 := count
    have nextWithin : rest.length ≤ (step p i s).countdown.toNat := by
      simp only [List.length_cons] at within
      omega
    have nextLimit : (step p i s).current.guard.limit = .misses budget := current.symm ▸ limit
    have first : (trace.step s i).captured = trace.captured := by
      simp [wait_edge s trace i waiting runtime, State.rxEvent, State.captures, waiting, miss]
    exact (ih (step p i s) (trace.step s i) phase nextLimit later nextWithin).trans first

/-- A prefix of bounded misses is safe to append before a terminal poll.
It consumes the budget while preserving the pad pose and captured bits. -/
theorem waiting_prefix (p : Program) (s : State a) (trace : BitTrace) (misses : List Input)
    (budget : Fin 255) (waiting : s.phase = .waiting)
    (limit : s.current.guard.limit = .misses budget) (history : MissHistory p s misses)
    (within : misses.length ≤ s.countdown.toNat) :
    WaitingPrefix s (run p s misses) trace (traceRun p s trace misses) misses.length := by
  obtain ⟨phase, countdown, pins, remaining, current⟩ :=
    bounded_wait_prefix p s misses budget waiting limit history within
  exact ⟨phase, countdown, pins, remaining, current,
    misses_preserve_captures p s trace misses budget waiting limit history within⟩

theorem bounded_poll (p : Program) (s : State a) (trace : BitTrace) (misses : List Input) (last : Input)
    (budget : Fin 255) (waiting : s.phase = .waiting)
    (limit : s.current.guard.limit = .misses budget) (history : MissHistory p s misses)
    (within : misses.length ≤ s.countdown.toNat) (lastRuntime : last.Runtime) :
    PollResult p s trace misses last := by
  have pre := waiting_prefix p s trace misses budget waiting limit history within
  have endState : run p s (misses ++ [last]) = step p last (run p s misses) := by
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have endTrace : traceRun p s trace (misses ++ [last]) =
      (traceRun p s trace misses).step (run p s misses) last :=
    trace_append p s trace misses [last]
  constructor
  · intro ready stream receive
    rw [endState, endTrace]
    have advance := step_wait_ready p (run p s misses) last lastRuntime pre.phase ready
    refine ⟨?_, advance.2.1.trans pre.pins, advance.2.2.1.trans pre.remaining,
      advance.2.2.2.trans pre.current, ?_⟩
    · simpa only [pre.current, stream, if_true] using advance.1
    · rw [wait_edge _ _ last pre.phase lastRuntime, pre.captured]
      simp [State.rxEvent, State.captures, pre.phase, ready, pre.current, stream, receive]
  · intro notReady deadline
    have zero : (run p s misses).countdown = 0#8 := by
      apply BitVec.eq_of_toNat_eq
      simp only [pre.countdown, deadline, Nat.sub_self, BitVec.toNat_zero]
    have timedOut : (run p s misses).timedOut = true := by
      simp [State.timedOut, pre.phase, notReady, pre.current, limit, zero, WaitLimit.expires]
    have busy : (run p s misses).phase.busy = true := by
      simp [pre.phase, Phase.busy]
    have captured : (traceRun p s trace (misses ++ [last])).captured = trace.captured := by
      simp only [endTrace, wait_edge _ _ last pre.phase lastRuntime, pre.captured, State.rxEvent,
        timedOut_captures_false _ timedOut, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    let final := run p s (misses ++ [last])
    have fields : final.phase = .fault ∧ final.pins = p.idle ∧ final.remaining = s.remaining ∧
        final.rxUsed = 0#6 ∧ final.rxPartial = 0#32 := by
      rw [show final = _ from endState.trans (step_busy_eq_clock p _ last lastRuntime busy),
        clock, engine_timedOut p _ timedOut]
      exact ⟨rfl, rfl, pre.remaining, rfl, rfl⟩
    obtain ⟨phase, idle, remaining, flushed, cleared⟩ := fields
    refine ⟨phase, idle, remaining, flushed, cleared, captured, ?_⟩
    intro related structural
    simpa [captured, State.pendingRx, show (run p s (misses ++ [last])).rxUsed = 0#6 from flushed]
      using (traceRun_related p s trace (misses ++ [last]) related structural).rxOrder

end Pinwheel.Program.StreamingReady.GuardedCell
