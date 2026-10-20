import Pinwheel.Program.StreamingReadyFields
import Pinwheel.Program.StreamingQueueProofs

namespace Pinwheel.Program.StreamingReady
set_option linter.unusedSimpArgs false

theorem step_samples (p : Program) (s : State a) (i : Input) (runtime : i.Runtime) :
    (step p i s).samplerFirst = i.rawInputs ∧ (step p i s).samplerSecond = s.samplerFirst := by
  rcases runtime with ⟨cold,warm⟩
  change i.command ≠ 15#4 at warm
  simp [step,cold,warm,State.start,State.release,clock]
  split <;> simp_all
  split <;> simp_all

theorem step_preserves (p : Program) (s : State a) (i : Input) (P : State a → Prop)
    (cold : P (s.reset p true)) (warm : P (s.reset p false)) (start : P (s.start p i))
    (release : P (s.release p i)) (clock : P (StreamingReady.clock p i s)) : P (step p i s) := by
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

theorem hostPush_bound (s : State a) (i : Input) (chunk : Chunk)
    (accepted : s.hostPush i = some chunk) :
    s.txAccepted.toNat + chunk.validBits ≤ s.total.toNat := by
  unfold State.hostPush at accepted
  split at accepted
  all_goals cases accepted
  simp only [Streaming.Chunk.validBits]
  omega

private theorem add16_bounded (current total : BitVec 16) (n : Nat)
    (bound : current.toNat + n ≤ total.toNat) :
    (current + BitVec.ofNat 16 n).toNat ≤ total.toNat := by
  have totalBound := total.isLt
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

theorem clock_tx_accepted_le (p : Program) (s : State a) (i : Input)
    (bound : s.txAccepted.toNat ≤ s.total.toNat) :
    (clock p i s).txAccepted.toNat ≤ (clock p i s).total.toNat := by
  simp only [clock,engine_total]
  cases offered : s.hostPush i with
  | none => simpa [offered,Streaming.Queue.willPush] using bound
  | some chunk =>
    split
    · exact add16_bounded s.txAccepted s.total chunk.validBits (hostPush_bound s i chunk offered)
    · simpa using bound

theorem engine_tx_valid_le (p : Program) (s : State a) (bound : s.txValid.toNat ≤ 32) :
    (engine p s).txValid.toNat ≤ 32 := by
  rw [(engine_tx_fields p s).2.1]
  split
  · have chunkBound := s.selectedTx.validMinusOne.isLt
    simp [Streaming.Chunk.validBits,BitVec.toNat_ofNat]
    omega
  · exact bound

theorem engine_rx_used_lt (p : Program) (s : State a) (bound : s.rxUsed.toNat < 32) :
    (engine p s).rxUsed.toNat < 32 := by
  rw [(engine_rx_fields p s).2.1]
  split
  · decide
  · split
    · split
      · decide
      · have notFull : s.rxUsed.toNat ≠ 31 := by
          intro same
          have sameBits : s.rxUsed = 31#6 := BitVec.eq_of_toNat_eq same
          simp [State.emittingCapture,‹s.captures = true›,sameBits] at ‹¬s.emittingCapture = true›
        change (s.rxUsed + 1#6).toNat < 32
        simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
        omega
    · exact bound

theorem engine_reservation_origin (p : Program) (s : State a)
    (place : (engine p s).phase = .low ∨ (engine p s).phase = .waiting)
    (stream : (engine p s).current.isStream = true) :
    (engine p s).current = s.current ∧ s.enginePush = none ∧
      ((s.phase = .boundary ∧ s.canReserve = true) ∨ s.phase = .low ∨ s.phase = .waiting) := by
  cases phase : s.phase
  case waiting =>
    cases ready : s.waitReady <;> cases isStream : s.current.isStream <;>
      cases expired : s.current.guard.limit.expires s.countdown <;>
      simp [engine,phase,ready,isStream,expired,State.enterHigh,State.captureData,State.timeoutFault] at place
    all_goals simp [engine,phase,ready,isStream,expired,State.enginePush,State.emittingCapture,
      State.captures,State.timedOut]
  case fetch =>
    cases fetched : p.fetch s.pc.toNat with
    | none => simp [engine,phase,fetched,State.stop] at place
    | some instruction =>
      cases instruction <;> simp [engine,phase,fetched,State.stop,Instruction.isStream] at place stream
      split at place <;> simp_all
  case boundary =>
    cases credit : s.canReserve
    · simp [engine,phase,credit] at place
    · simp [engine,phase,credit,State.enginePush,State.timedOut,State.captures,State.emittingCapture]
  case low =>
    by_cases zero : s.countdown = 0#8 <;> cases guarded : s.current.hasHighGuard <;>
      simp [engine,phase,zero,guarded,State.enterHigh,State.captureData] at place
    all_goals simp [engine,phase,zero,guarded,State.enginePush,State.timedOut,State.captures,State.emittingCapture]
  case high =>
    by_cases zero : s.countdown = 0#8 <;> simp [engine,phase,zero] at place
    split at place <;> simp_all
  all_goals simp [engine,phase] at place

theorem clock_reservation_credit (p : Program) (s : State a) (i : Input)
    (credit : s.ReservationCredit) : (clock p i s).ReservationCredit := by
  intro place stream receive
  obtain ⟨current,noPush,origin⟩ := engine_reservation_origin p s place stream
  have oldStream : s.current.isStream = true := current ▸ stream
  have oldReceive : s.current.cell.receive = true := current ▸ receive
  have room : s.rx.writable = true := by
    rcases origin with ⟨_,reserved⟩ | low | waiting
    · simp [State.canReserve,oldStream,State.rxReady,oldReceive] at reserved
      exact reserved.2
    · exact credit (Or.inl low) oldStream oldReceive
    · exact credit (Or.inr waiting) oldStream oldReceive
  change (s.rx.tick s.enginePush (s.hostPop i)).writable = true
  rw [noPush]
  have monotone := Streaming.Queue.tick_no_push_le s.rx (s.hostPop i)
  simp only [Streaming.Queue.writable,decide_eq_true_eq] at room ⊢
  omega

private theorem queue_none_writable (q : Queue a) (pop : Bool) (room : q.writable = true) :
    (q.tick none pop).writable = true := by
  have monotone := Streaming.Queue.tick_no_push_le q pop
  simp only [Streaming.Queue.writable,decide_eq_true_eq] at room ⊢
  omega

theorem clock_partial_credit (p : Program) (s : State a) (i : Input)
    (reservation : s.ReservationCredit) (partialCredit : s.PartialCredit) :
    (clock p i s).PartialCredit := by
  intro positive
  change 0 < (engine p s).rxUsed.toNat at positive
  rw [(engine_rx_fields p s).2.1] at positive
  by_cases timeout : s.timedOut = true
  · simp [timeout] at positive
  · by_cases emits : s.emittingCapture = true
    · have capture : s.captures = true := by
        have facts := emits
        simp only [State.emittingCapture,Bool.and_eq_true] at facts
        exact facts.1
      simp [timeout,emits,capture] at positive
    · have room : s.rx.writable = true := by
        by_cases capture : s.captures = true
        · obtain ⟨stream,receive,place⟩ := captures_fields s capture
          exact reservation place stream receive
        · simp [timeout,capture] at positive
          exact partialCredit positive
      change (s.rx.tick s.enginePush (s.hostPop i)).writable = true
      have noPush : s.enginePush = none := by simp [State.enginePush,timeout,emits]
      rw [noPush]
      exact queue_none_writable s.rx (s.hostPop i) room

theorem clock_structural (p : Program) (s : State a) (i : Input) (invariant : s.Structural) :
    (clock p i s).Structural := by
  constructor
  · exact clock_tx_accepted_le p s i invariant.accepted
  · exact engine_tx_valid_le p s invariant.txValid
  · exact engine_rx_used_lt p s invariant.rxUsed
  · exact clock_reservation_credit p s i invariant.reservationCredit
  · exact clock_partial_credit p s i invariant.reservationCredit invariant.partialCredit

theorem State.reset_structural (p : Program) (s : State a) (cold : Bool) :
    (s.reset p cold).Structural := by
  constructor <;> simp [State.reset,State.ReservationCredit,State.PartialCredit]

theorem State.start_structural (p : Program) (s : State a) (i : Input) :
    (s.start p i).Structural := by
  constructor <;> simp [State.start,State.ReservationCredit,State.PartialCredit]

theorem State.release_structural (p : Program) (s : State a) (i : Input) :
    (s.release p i).Structural := by
  constructor <;> simp [State.release,State.ReservationCredit,State.PartialCredit]

theorem step_structural (p : Program) (s : State a) (i : Input) (invariant : s.Structural) :
    (step p i s).Structural :=
  step_preserves p s i State.Structural (s.reset_structural p true) (s.reset_structural p false)
    (s.start_structural p i) (s.release_structural p i) (clock_structural p s i invariant)

theorem run_structural (p : Program) (s : State a) (inputs : List Input) (invariant : s.Structural) :
    (run p s inputs).Structural := by
  induction inputs generalizing s with
  | nil => exact invariant
  | cons i inputs induction => exact induction (step p i s) (step_structural p s i invariant)

theorem initial_structural (a : Nat) : ({} : State a).Structural := by
  constructor <;> simp [State.ReservationCredit,State.PartialCredit]

end Pinwheel.Program.StreamingReady
