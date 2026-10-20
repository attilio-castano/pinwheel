import Pinwheel.Program.StreamingReadyProgress

namespace Pinwheel.Program.StreamingReady

theorem engine_count_fields (p : Program) (s : State a) :
    (engine p s).txConsumed = s.txConsumed + BitVec.ofNat 16 s.txEvent.length ∧
    (engine p s).rxProduced = s.rxProduced + BitVec.ofNat 16 s.rxEvent.length := by
  rw [(engine_tx_fields p s).2.2,(engine_rx_fields p s).2.2]
  cases consume : s.consumes <;> cases capture : s.captures <;>
    simp [State.txEvent,State.rxEvent,consume,capture]

theorem engine_count_nat (p : Program) (s : State a) (progress : s.Progress) :
    (engine p s).txConsumed.toNat = s.txConsumed.toNat + s.txEvent.length ∧
    (engine p s).rxProduced.toNat = s.rxProduced.toNat + s.rxEvent.length := by
  rw [(engine_count_fields p s).1, (engine_count_fields p s).2]
  constructor
  · by_cases consume : s.consumes = true
    · have room := progress.tx_before_last s consume
      have bound := s.total.isLt
      simp only [State.txEvent, consume, ↓reduceIte, List.length_cons, List.length_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp [State.txEvent, consume]
  · by_cases capture : s.captures = true
    · have room := progress.rx_before_last s capture
      have bound := s.total.isLt
      simp only [State.rxEvent, capture, ↓reduceIte, List.length_cons, List.length_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · simp [State.rxEvent, capture]

/-- Counter values equal natural lengths, rather than only modular residues. -/
structure BitTrace.NaturalCounts (trace : BitTrace) (s : State a) : Prop where
  accepted : trace.accepted.length = s.txAccepted.toNat
  consumed : trace.consumed.length = s.txConsumed.toNat
  captured : trace.captured.length = s.rxProduced.toNat
  exported : trace.exported.length = s.rxPopped.toNat

theorem BitTrace.NaturalCounts.clock (p : Program) (s : State a) (i : Input) (trace : BitTrace)
    (counts : trace.NaturalCounts s) (related : trace.Related s) (structural : s.Structural)
    (progress : s.Progress) : (trace.clock s i).NaturalCounts (StreamingReady.clock p i s) := by
  constructor
  · cases offered : s.hostPush i with
    | none => simp [BitTrace.clock, StreamingReady.clock, offered, State.acceptedBits,
        Streaming.Queue.willPush, counts.accepted]
    | some chunk =>
      by_cases accepted : s.tx.willPush (some chunk) = true
      · have bound := hostPush_bound s i chunk offered
        have totalBound := s.total.isLt
        simp [BitTrace.clock, StreamingReady.clock, offered, State.acceptedBits, accepted,
          counts.accepted, Streaming.Chunk.txBits, BitVec.toNat_add]
        omega
      · simp [BitTrace.clock, StreamingReady.clock, offered, State.acceptedBits, accepted,
          counts.accepted]
  · simpa [BitTrace.clock, StreamingReady.clock, List.length_append, counts.consumed] using
      (engine_count_nat p s progress).1.symm
  · simpa [BitTrace.clock, StreamingReady.clock, List.length_append, counts.captured] using
      (engine_count_nat p s progress).2.symm
  · have nextRelated := related.clock p s i trace structural
    have capturedCount : (trace.clock s i).captured.length = (StreamingReady.clock p i s).rxProduced.toNat := by
      simpa [BitTrace.clock, StreamingReady.clock, List.length_append, counts.captured] using
        (engine_count_nat p s progress).2.symm
    have noWrap : s.rxPopped.toNat + (s.exportedBits i).length < 65536 := by
      have order := congrArg List.length nextRelated.rxOrder
      rw [capturedCount] at order
      have produced := (clock_progress p s i progress).rx_le (StreamingReady.clock p i s)
      have totalBound := s.total.isLt
      simp only [List.length_append, BitTrace.clock, counts.exported, StreamingReady.clock,
        engine_total] at order produced
      omega
    by_cases pop : s.rx.willPop (s.hostPop i) = true
    · simp [BitTrace.clock, StreamingReady.clock, State.exportedBits, pop, counts.exported,
        Streaming.Chunk.rxBits, BitVec.toNat_add] at noWrap ⊢
      omega
    · simp [BitTrace.clock, StreamingReady.clock, State.exportedBits, pop, counts.exported]

theorem BitTrace.NaturalCounts.reset (p : Program) (s : State a) (cold : Bool) :
    BitTrace.NaturalCounts ({} : BitTrace) (s.reset p cold) := by
  constructor <;> rfl

theorem BitTrace.NaturalCounts.start (p : Program) (s : State a) (i : Input) :
    BitTrace.NaturalCounts ({} : BitTrace) (s.start p i) := by
  constructor <;> rfl

theorem BitTrace.NaturalCounts.release (p : Program) (s : State a) (i : Input) :
    BitTrace.NaturalCounts ({} : BitTrace) (s.release p i) := by
  constructor <;> rfl

theorem BitTrace.NaturalCounts.step (p : Program) (s : State a) (i : Input) (trace : BitTrace)
    (counts : trace.NaturalCounts s) (related : trace.Related s) (structural : s.Structural)
    (progress : s.Progress) : (trace.step s i).NaturalCounts (StreamingReady.step p i s) := by
  simp only [BitTrace.step, StreamingReady.step]
  split
  · exact BitTrace.NaturalCounts.reset p s true
  · split
    · exact BitTrace.NaturalCounts.reset p s false
    · split
      · exact BitTrace.NaturalCounts.start p s i
      · split
        · exact BitTrace.NaturalCounts.release p s i
        · exact counts.clock p s i trace related structural progress

theorem traceRun_natural (p : Program) (s : State a) (trace : BitTrace) (inputs : List Input)
    (counts : trace.NaturalCounts s) (related : trace.Related s) (structural : s.Structural)
    (progress : s.Progress) : (traceRun p s trace inputs).NaturalCounts (run p s inputs) := by
  induction inputs generalizing s trace with
  | nil => exact counts
  | cons i inputs induction =>
    exact induction (step p i s) (trace.step s i)
      (counts.step p s i trace related structural progress) (related.step p s i trace structural)
      (step_structural p s i structural) (step_progress p s i progress)

theorem BitTrace.NaturalCounts.order (s : State a) (trace : BitTrace)
    (counts : trace.NaturalCounts s) (related : trace.Related s) :
    s.txConsumed.toNat ≤ s.txAccepted.toNat ∧ s.rxPopped.toNat ≤ s.rxProduced.toNat := by
  have tx := congrArg List.length related.txOrder
  have rx := congrArg List.length related.rxOrder
  simp only [List.length_append, counts.accepted, counts.consumed, counts.captured,
    counts.exported] at tx rx
  omega

/-- Arbitrary finite histories preserve ordered bit traces and exact nonwrapping counters. -/
theorem started_trace (p : Program) (before : State a) (start : Input) (inputs : List Input) :
    let first := before.start p start
    let final := run p first inputs
    let trace := traceRun p first {} inputs
    trace.Related final ∧ trace.NaturalCounts final ∧ final.Structural ∧ final.Progress := by
  refine ⟨traceRun_related p _ {} inputs (BitTrace.Related.start p before start)
    (before.start_structural p start), ?_, run_structural p _ inputs (before.start_structural p start),
    run_progress p _ inputs (before.start_progress p start)⟩
  exact traceRun_natural p _ {} inputs (BitTrace.NaturalCounts.start p before start)
    (BitTrace.Related.start p before start) (before.start_structural p start) (before.start_progress p start)

end Pinwheel.Program.StreamingReady
