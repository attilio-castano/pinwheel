import Pinwheel.Program.StreamingExecution
import Pinwheel.Program.StreamingQueueProofs

namespace Pinwheel.Program.Streaming

def Input.Runtime (i : Input) : Prop := i.initialize = false ∧ i.command ≠ 15

/-- Neither engine stalls nor rejected host commands freeze the synchronizer. -/
theorem step_samples (p : Program) (s : State addrBits) (i : Input) (runtime : i.Runtime) :
    (step p i s).samplerFirst = i.rawInputs ∧
      (step p i s).samplerSecond = s.samplerFirst := by
  rcases runtime with ⟨cold, warm⟩
  change i.command ≠ 15#4 at warm
  simp [step, cold, warm, State.start, State.release, clock]
  split <;> simp_all
  split <;> simp_all

theorem Queue.tick_no_push_le (q : Queue addrBits) (outgoing : Bool) :
    (q.tick none outgoing).count.val ≤ q.count.val := by
  simp [tick_count, willPush]

/-- A receive cell reserves a free word before entering LOW. -/
def State.LowCredit (s : State addrBits) : Prop :=
  s.phase = .low → s.current.isStream = true → s.current.cell.receive = true →
    s.rx.count.val < queueDepth addrBits

theorem engine_low_origin (p : Program) (s : State addrBits)
    (low : (engine p s).phase = .low) :
    (s.phase = .boundary ∧ s.canReserve = true) ∨
      (s.phase = .low ∧ s.countdown ≠ 0#8) := by
  cases phase : s.phase <;> simp [engine, phase] at low
  case fetch =>
    split at low <;> simp_all [State.stop]
    split at low <;> simp_all
  case boundary => split at low <;> simp_all
  case low => split at low <;> simp_all
  case high =>
    split at low <;> simp_all
    split at low <;> simp_all

theorem engine_low_current (p : Program) (s : State addrBits)
    (low : (engine p s).phase = .low) : (engine p s).current = s.current := by
  rcases engine_low_origin p s low with ⟨phase, credit⟩ | ⟨phase, countdown⟩
  all_goals simp [engine, *]

theorem engine_low_no_push (p : Program) (s : State addrBits)
    (low : (engine p s).phase = .low) : s.enginePush = none := by
  rcases engine_low_origin p s low with ⟨phase, credit⟩ | ⟨phase, countdown⟩
  all_goals simp [State.enginePush, State.captures, *]

theorem clock_low_credit (p : Program) (s : State addrBits) (i : Input)
    (credit : s.LowCredit) : (clock p i s).LowCredit := by
  intro low stream receive
  have current := engine_low_current p s low
  simp only [clock, current] at stream receive
  simp only [clock, engine_low_no_push p s low]
  apply Nat.lt_of_le_of_lt (Queue.tick_no_push_le s.rx (s.hostPop i))
  rcases engine_low_origin p s low with ⟨phase, reserve⟩ | ⟨phase, countdown⟩
  · simp [State.canReserve, stream, State.rxReady, receive, Queue.writable] at reserve
    exact reserve.2
  · exact credit phase stream receive

theorem step_low_credit (p : Program) (s : State addrBits) (i : Input)
    (credit : s.LowCredit) : (step p i s).LowCredit := by
  simp only [step]
  split <;> simp [State.LowCredit, State.reset, State.start, State.release]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  exact clock_low_credit p s i credit

theorem run_low_credit (p : Program) (s : State addrBits) (inputs : List Input)
    (credit : s.LowCredit) : (run p s inputs).LowCredit := by
  induction inputs generalizing s with
  | nil => exact credit
  | cons i inputs induction => exact induction (step p i s) (step_low_credit p s i credit)

theorem hostPush_bound (s : State addrBits) (i : Input) (chunk : Chunk)
    (accepted : s.hostPush i = some chunk) :
    s.txAccepted.toNat + chunk.validBits ≤ s.total.toNat := by
  unfold State.hostPush at accepted
  split at accepted
  all_goals cases accepted
  simp only [Chunk.validBits]
  omega

theorem engine_total (p : Program) (s : State addrBits) : (engine p s).total = s.total := by
  unfold engine
  split <;> first | rfl | (split <;> first | rfl | (split <;> rfl))

private theorem add16_bounded (current total : BitVec 16) (n : Nat)
    (bound : current.toNat + n ≤ total.toNat) :
    (current + BitVec.ofNat 16 n).toNat ≤ total.toNat := by
  have totalBound := total.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem clock_tx_accepted_le (p : Program) (s : State addrBits) (i : Input)
    (bound : s.txAccepted.toNat ≤ s.total.toNat) :
    (clock p i s).txAccepted.toNat ≤ (clock p i s).total.toNat := by
  simp only [clock, engine_total]
  cases offered : s.hostPush i with
  | none => simpa [offered, Queue.willPush] using bound
  | some chunk =>
    split
    · exact add16_bounded s.txAccepted s.total chunk.validBits (hostPush_bound s i chunk offered)
    · simpa using bound

theorem step_preserves (p : Program) (s : State addrBits) (i : Input)
    (P : State addrBits → Prop) (cold : P (s.reset p true))
    (warm : P (s.reset p false)) (start : P (s.start p i))
    (release : P (s.release p i)) (clock : P (Streaming.clock p i s)) :
    P (step p i s) := by
  unfold step
  split
  · exact cold
  · split
    · exact warm
    · split
      · exact start
      · split
        · exact release
        · exact clock

private theorem chunk_remaining_bound (chunk : Chunk) :
    (BitVec.ofNat 6 (chunk.validBits - 1)).toNat ≤ 32 := by
  simp [Chunk.validBits, BitVec.toNat_ofNat]
  have := chunk.validMinusOne.isLt
  omega

theorem engine_tx_valid_le (p : Program) (s : State addrBits) (bound : s.txValid.toNat ≤ 32) :
    (engine p s).txValid.toNat ≤ 32 := by
  unfold engine
  split <;> first
    | exact bound
    | (split <;> first
      | exact bound
      | (dsimp only; split <;> first | exact bound | exact chunk_remaining_bound s.selectedTx))

private theorem partial_increment_bound (s : State addrBits) (bound : s.rxUsed.toNat < 32)
    (capture : s.captures = true) (noFlush : s.enginePush.isSome ≠ true) :
    (s.rxUsed + 1#6).toNat < 32 := by
  have notFull : s.rxUsed.toNat ≠ 31 := by
    intro same
    have sameBits : s.rxUsed = 31#6 := BitVec.eq_of_toNat_eq same
    simp [State.enginePush, capture, sameBits] at noFlush
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem partial_update_bound (s : State addrBits) (bound : s.rxUsed.toNat < 32) :
    (if s.captures then (if s.enginePush.isSome then 0 else s.rxUsed + 1) else s.rxUsed).toNat < 32 := by
  split
  · split
    · decide
    · exact partial_increment_bound s bound ‹s.captures = true› ‹s.enginePush.isSome ≠ true›
  · exact bound

theorem engine_rx_used_lt (p : Program) (s : State addrBits) (bound : s.rxUsed.toNat < 32) :
    (engine p s).rxUsed.toNat < 32 := by
  unfold engine
  split <;> first
    | exact bound
    | (split <;> first
      | exact bound
      | exact partial_update_bound s bound
      | (dsimp only; split <;> exact bound))

/-- Representability and the outstanding receive reservation are reachable invariants. -/
structure State.Structural (s : State addrBits) : Prop where
  accepted : s.txAccepted.toNat ≤ s.total.toNat
  txValid : s.txValid.toNat ≤ 32
  rxUsed : s.rxUsed.toNat < 32
  lowCredit : s.LowCredit

theorem clock_structural (p : Program) (s : State addrBits) (i : Input)
    (invariant : s.Structural) : (clock p i s).Structural := by
  constructor
  · exact clock_tx_accepted_le p s i invariant.accepted
  · exact engine_tx_valid_le p s invariant.txValid
  · exact engine_rx_used_lt p s invariant.rxUsed
  · exact clock_low_credit p s i invariant.lowCredit

theorem State.reset_structural (p : Program) (s : State addrBits) (cold : Bool) :
    (s.reset p cold).Structural := by
  constructor <;> simp [State.reset, State.LowCredit]

theorem State.start_structural (p : Program) (s : State addrBits) (i : Input) :
    (s.start p i).Structural := by
  constructor <;> simp [State.start, State.LowCredit]

theorem State.release_structural (p : Program) (s : State addrBits) (i : Input) :
    (s.release p i).Structural := by
  constructor <;> simp [State.release, State.LowCredit]

theorem step_structural (p : Program) (s : State addrBits) (i : Input)
    (invariant : s.Structural) : (step p i s).Structural :=
  step_preserves p s i State.Structural (s.reset_structural p true)
    (s.reset_structural p false) (s.start_structural p i) (s.release_structural p i)
    (clock_structural p s i invariant)

theorem run_structural (p : Program) (s : State addrBits) (inputs : List Input)
    (invariant : s.Structural) : (run p s inputs).Structural := by
  induction inputs generalizing s with
  | nil => exact invariant
  | cons i inputs induction => exact induction (step p i s) (step_structural p s i invariant)

theorem State.Structural.rx_writable (s : State addrBits) (invariant : s.Structural)
    (low : s.phase = .low) (stream : s.current.isStream = true)
    (receive : s.current.cell.receive = true) : s.rx.writable = true := by
  simpa [Queue.writable] using invariant.lowCredit low stream receive

theorem step_busy_eq_clock (p : Program) (s : State addrBits) (i : Input)
    (runtime : i.Runtime) (busy : s.phase.busy = true) : step p i s = clock p i s := by
  rcases runtime with ⟨cold, warm⟩
  change i.command ≠ 15#4 at warm
  cases phase : s.phase <;> simp [phase, Phase.busy] at busy
  all_goals simp [step, cold, warm, State.canStart, State.canRelease, phase, Phase.retained]

/-- A full RX queue prevents TX consumption even when the host pops on this edge. -/
theorem clock_full_rx_stalls (p : Program) (s : State addrBits) (i : Input)
    (boundary : s.phase = .boundary) (stream : s.current.isStream = true)
    (receive : s.current.cell.receive = true) (full : s.rx.count.val = queueDepth addrBits) :
    (clock p i s).phase = .boundary ∧ (clock p i s).pins = s.pins ∧
      (clock p i s).txConsumed = s.txConsumed ∧ (clock p i s).rxProduced = s.rxProduced ∧
      (clock p i s).remaining = s.remaining := by
  have credit : s.canReserve = false := by
    simp [State.canReserve, stream, State.rxReady, receive, Queue.writable, full]
  simp [clock, engine, boundary, credit]

/-- HIGH ignores queue credits and all ordinary host traffic. -/
theorem step_high_wait (p : Program) (s : State addrBits) (i : Input)
    (runtime : i.Runtime) (high : s.phase = .high) (countdown : s.countdown ≠ 0#8) :
    (step p i s).phase = .high ∧ (step p i s).countdown = s.countdown - 1#8 ∧
      (step p i s).pins = s.pins ∧ (step p i s).remaining = s.remaining := by
  rw [step_busy_eq_clock p s i runtime (by simp [high, Phase.busy])]
  simp [clock, engine, high, countdown]

theorem step_high_terminal (p : Program) (s : State addrBits) (i : Input)
    (runtime : i.Runtime) (high : s.phase = .high) (countdown : s.countdown = 0#8) :
    (step p i s).phase = (if s.current.isStream && s.remaining.toNat > 1 then .boundary else .fetch) ∧
      (step p i s).remaining = s.remaining - (if s.current.isStream then 1#16 else 0#16) := by
  rw [step_busy_eq_clock p s i runtime (by simp [high, Phase.busy])]
  simp [clock, engine, high, countdown]

end Pinwheel.Program.Streaming
