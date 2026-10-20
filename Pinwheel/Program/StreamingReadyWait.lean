import Pinwheel.Program.StreamingReadyExecution
import Pinwheel.Program.StreamingPacking

/-! Total WAIT laws, including odd but represented phase/instruction pairings. -/
namespace Pinwheel.Program.StreamingReady

theorem engine_wait_ready (p : Program) (s : State a)
    (waiting : s.phase = .waiting) (ready : s.waitReady = true) :
    engine p s = if s.current.isStream then s.enterHigh
      else {s with phase := .fetch, pc := s.pc + 1, countdown := 0} := by
  simp [engine,waiting,ready]

theorem engine_wait_timeout (p : Program) (s : State a)
    (waiting : s.phase = .waiting) (ready : s.waitReady = false)
    (expired : s.current.guard.limit.expires s.countdown = true) :
    engine p s = s.timeoutFault p := by
  simp [engine,waiting,ready,expired]

theorem engine_wait_unbounded (p : Program) (s : State a)
    (waiting : s.phase = .waiting) (ready : s.waitReady = false)
    (limit : s.current.guard.limit = .unbounded) : engine p s = s := by
  simp [engine,waiting,ready,limit,WaitLimit.expires,WaitLimit.poll]
  cases s
  simp_all

theorem timedOut_captures_false (s : State a) (timeout : s.timedOut = true) :
    s.captures = false := by
  simp only [State.timedOut,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at timeout
  simp [State.captures,timeout.1.1,timeout.1.2]

theorem engine_timedOut (p : Program) (s : State a) (timeout : s.timedOut = true) :
    engine p s = s.timeoutFault p := by
  simp only [State.timedOut,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at timeout
  exact engine_wait_timeout p s timeout.1.1 timeout.1.2 timeout.2

theorem timeoutChunk_fields (s : State a) (bound : s.rxUsed.toNat < 32)
    (nonzero : s.rxUsed ≠ 0#6) :
    ∃ chunk, s.timeoutChunk = some chunk ∧ chunk.data = s.rxPartial ∧
      chunk.validBits = s.rxUsed.toNat := by
  have positive : 0 < s.rxUsed.toNat := by
    have unequal := BitVec.toNat_ne_iff_ne.mpr nonzero
    simp only [BitVec.toNat_ofNat] at unequal
    omega
  refine ⟨⟨s.rxPartial,⟨(s.rxUsed.toNat-1)%32,Nat.mod_lt _ (by decide)⟩⟩,?_,rfl,?_⟩
  · simp [State.timeoutChunk,nonzero]
  · simp [Streaming.Chunk.validBits,Nat.mod_eq_of_lt (show s.rxUsed.toNat-1 < 32 by omega)]
    omega

theorem captures_fields (s : State a) (capture : s.captures = true) :
    s.current.isStream = true ∧ s.current.cell.receive = true ∧
      (s.phase = .low ∨ s.phase = .waiting) := by
  simp only [State.captures,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at capture
  rcases capture with ⟨⟨stream,receive⟩,⟨⟨low,_⟩,_⟩ | ⟨waiting,_⟩⟩
  · exact ⟨stream,receive,Or.inl low⟩
  · exact ⟨stream,receive,Or.inr waiting⟩

theorem enginePush_credit (s : State a) (invariant : s.Structural) :
    s.rx.willPush s.enginePush = s.enginePush.isSome := by
  by_cases timeout : s.timedOut = true
  · by_cases empty : s.rxUsed = 0#6
    · simp [State.enginePush,timeout,State.timeoutChunk,empty,Streaming.Queue.willPush]
    · have positive : 0 < s.rxUsed.toNat := by
        have unequal := BitVec.toNat_ne_iff_ne.mpr empty
        simp only [BitVec.toNat_ofNat] at unequal
        omega
      simp [State.enginePush,timeout,State.timeoutChunk,empty,Streaming.Queue.willPush,
        invariant.partialCredit positive]
  · by_cases emits : s.emittingCapture = true
    · have captured : s.captures = true := by
        have facts := emits
        simp only [State.emittingCapture,Bool.and_eq_true] at facts
        exact facts.1
      obtain ⟨stream,receive,place⟩ := captures_fields s captured
      have room := invariant.reservationCredit place stream receive
      simp [State.enginePush,timeout,emits,Streaming.Queue.willPush,room]
    · simp [State.enginePush,timeout,emits,Streaming.Queue.willPush]

end Pinwheel.Program.StreamingReady
