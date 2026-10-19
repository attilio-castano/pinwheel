import Pinwheel.Program.StreamingBitTrace

namespace Pinwheel.Program.Streaming

def State.txFlight (s : State addrBits) : Nat :=
  if s.current.isStream && (s.phase == .low || s.phase == .high) then 1 else 0

def State.rxFlight (s : State addrBits) : Nat :=
  if s.current.isStream && s.phase == .high then 1 else 0

/-- The stream count includes the current cell until its HIGH interval finishes. -/
structure State.Progress (s : State addrBits) : Prop where
  remaining : s.remaining.toNat ≤ s.total.toNat
  active : s.current.isStream = true →
    (s.phase = .boundary ∨ s.phase = .low ∨ s.phase = .high) → 0 < s.remaining.toNat
  tx : s.txConsumed.toNat + s.remaining.toNat ≤ s.total.toNat + s.txFlight
  rx : s.rxProduced.toNat + s.remaining.toNat ≤ s.total.toNat + s.rxFlight

theorem State.Progress.tx_le (s : State addrBits) (progress : s.Progress) :
    s.txConsumed.toNat ≤ s.total.toNat := by
  by_cases stream : s.current.isStream = true
  · by_cases phase : s.phase = .low ∨ s.phase = .high
    · have positive := progress.active stream (Or.inr phase)
      have bound := progress.tx
      simp [State.txFlight, stream, phase] at bound
      omega
    · have bound := progress.tx
      simp [State.txFlight, stream, phase] at bound
      omega
  · have bound := progress.tx
    simp [State.txFlight, stream] at bound
    omega

theorem State.Progress.rx_le (s : State addrBits) (progress : s.Progress) :
    s.rxProduced.toNat ≤ s.total.toNat := by
  by_cases stream : s.current.isStream = true
  · by_cases phase : s.phase = .high
    · have positive := progress.active stream (Or.inr (Or.inr phase))
      have bound := progress.rx
      simp [State.rxFlight, stream, phase] at bound
      omega
    · have bound := progress.rx
      simp [State.rxFlight, stream, phase] at bound
      omega
  · have bound := progress.rx
    simp [State.rxFlight, stream] at bound
    omega

theorem engine_progress (p : Program) (s : State addrBits) (progress : s.Progress) :
    (engine p s).Progress := by
  cases phase : s.phase
  case high =>
    have remaining := progress.remaining
    have active := progress.active
    have tx := progress.tx
    have rx := progress.rx
    simp only [engine, phase]
    split
    · by_cases stream : s.current.isStream = true
      · have positive := active stream (Or.inr (Or.inr phase))
        have minus : (s.remaining - 1#16).toNat = s.remaining.toNat - 1 := by
          apply BitVec.toNat_sub_of_le
          change 1 ≤ s.remaining.toNat
          omega
        simp [State.txFlight, State.rxFlight, phase, stream] at tx rx
        by_cases more : 1 < s.remaining.toNat
        all_goals constructor <;> simp [State.txFlight, State.rxFlight, stream, more, minus] <;> omega
      · constructor <;> simp_all [State.txFlight, State.rxFlight] <;> omega
    · constructor
      · exact progress.remaining
      · intro stream _
        exact active stream (Or.inr (Or.inr phase))
      · simpa [State.txFlight, phase] using tx
      · simpa [State.rxFlight, phase] using rx
  case boundary =>
    have remaining := progress.remaining
    have active := progress.active
    have tx := progress.tx
    have rx := progress.rx
    simp [State.txFlight, State.rxFlight, phase] at tx rx
    simp only [engine, phase]
    split
    · by_cases stream : s.current.isStream = true
      · have positive := active stream (Or.inl phase)
        have addition : (s.txConsumed + 1#16).toNat = s.txConsumed.toNat + 1 := by
          have totalBound := s.total.isLt
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        cases transmit : s.current.cell.transmit
        all_goals constructor <;> simp_all [State.txFlight, State.rxFlight] <;> omega
      · constructor <;> simp_all [State.txFlight, State.rxFlight] <;> omega
    · exact progress
  case low =>
    have remaining := progress.remaining
    have active := progress.active
    have tx := progress.tx
    have rx := progress.rx
    simp [State.txFlight, State.rxFlight, phase] at tx rx
    simp only [engine, phase]
    split
    · by_cases stream : s.current.isStream = true
      · have positive := active stream (Or.inr (Or.inl phase))
        have addition : (s.rxProduced + 1#16).toNat = s.rxProduced.toNat + 1 := by
          have totalBound := s.total.isLt
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        cases receive : s.current.cell.receive
        all_goals constructor <;> simp_all [State.txFlight, State.rxFlight, State.captures] <;> omega
      · constructor <;> simp_all [State.txFlight, State.rxFlight, State.captures] <;> omega
    · constructor
      · exact remaining
      · intro stream _
        exact active stream (Or.inr (Or.inl phase))
      · simpa [State.txFlight] using tx
      · simpa [State.rxFlight] using rx
  case fetch =>
    have remaining := progress.remaining
    have tx := progress.tx
    have rx := progress.rx
    simp [State.txFlight, State.rxFlight, phase] at tx rx
    simp only [engine, phase]
    cases p.fetch s.pc.toNat with
    | none => constructor <;> simp_all [State.stop, State.txFlight, State.rxFlight] <;> omega
    | some instruction =>
      cases instruction
      case pulse cell =>
        constructor <;> simp_all [Instruction.isStream, State.txFlight, State.rxFlight] <;> omega
      case halt => constructor <;> simp_all [State.stop, State.txFlight, State.rxFlight] <;> omega
      case fault => constructor <;> simp_all [State.stop, State.txFlight, State.rxFlight] <;> omega
      case stream cell =>
        simp only
        split
        · constructor <;> simp_all [State.txFlight, State.rxFlight]
        · have positive : 0 < s.remaining.toNat := by
            have bitNonzero : s.remaining ≠ 0#16 := by
              simpa using (show ¬(s.remaining == 0) = true by assumption)
            have nonzero := BitVec.toNat_ne_iff_ne.mpr bitNonzero
            simp only [BitVec.toNat_ofNat] at nonzero
            omega
          constructor <;> simp_all [Instruction.isStream, State.txFlight, State.rxFlight] <;> omega
  case free => simpa [engine, phase] using progress
  case completed => simpa [engine, phase] using progress
  case fault => simpa [engine, phase] using progress

theorem clock_progress (p : Program) (s : State addrBits) (i : Input) (progress : s.Progress) :
    (clock p i s).Progress := by
  have next := engine_progress p s progress
  exact ⟨next.remaining, next.active, next.tx, next.rx⟩

theorem State.reset_progress (p : Program) (s : State addrBits) (cold : Bool) :
    (s.reset p cold).Progress := by
  constructor <;> simp [reset, State.txFlight, State.rxFlight]

theorem State.start_progress (p : Program) (s : State addrBits) (i : Input) :
    (s.start p i).Progress := by
  constructor <;> simp [start, State.txFlight, State.rxFlight, Instruction.isStream]

theorem State.release_progress (p : Program) (s : State addrBits) (i : Input) :
    (s.release p i).Progress := by
  constructor <;> simp [release, State.txFlight, State.rxFlight]

theorem step_progress (p : Program) (s : State addrBits) (i : Input) (progress : s.Progress) :
    (step p i s).Progress := by
  exact step_preserves p s i State.Progress (s.reset_progress p true) (s.reset_progress p false)
    (s.start_progress p i) (s.release_progress p i) (clock_progress p s i progress)

theorem run_progress (p : Program) (s : State addrBits) (inputs : List Input) (progress : s.Progress) :
    (run p s inputs).Progress := by
  induction inputs generalizing s with
  | nil => exact progress
  | cons i inputs induction => exact induction (step p i s) (step_progress p s i progress)

theorem State.Progress.tx_before_last (s : State addrBits) (progress : s.Progress)
    (consume : s.consumes = true) : s.txConsumed.toNat < s.total.toNat := by
  simp only [State.consumes, Bool.and_eq_true, beq_iff_eq] at consume
  have positive := progress.active consume.1.2 (Or.inl consume.1.1.1)
  have bound := progress.tx
  simp [State.txFlight, consume.1.1.1] at bound
  omega

theorem State.Progress.rx_before_last (s : State addrBits) (progress : s.Progress)
    (capture : s.captures = true) : s.rxProduced.toNat < s.total.toNat := by
  simp only [State.captures, Bool.and_eq_true, beq_iff_eq] at capture
  have positive := progress.active capture.1.2 (Or.inr (Or.inl capture.1.1.1))
  have bound := progress.rx
  simp [State.rxFlight, capture.1.1.1] at bound
  omega

end Pinwheel.Program.Streaming
