import Pinwheel.Program.StreamingReadyControl

namespace Pinwheel.Program.StreamingReady
set_option linter.unusedSimpArgs false

def Phase.activeCell (phase : Phase) : Prop :=
  phase = .boundary ∨ phase = .low ∨ phase = .high ∨ phase = .waiting

structure State.Cursor (s : State a) : Prop where
  bound : s.pc.toNat ≤ 64
  active : s.phase.activeCell → s.pc.toNat < 64

private theorem fetch_bound (p : Program) (pc : Nat) (instruction : Instruction)
    (fetch : p.fetch pc = some instruction) : pc < 64 := by
  unfold Program.fetch at fetch
  split at fetch
  · have := p.lengthMinusOne.isLt
    unfold Program.length at *
    omega
  · contradiction

private theorem pc_increment (pc : BitVec 7) (bound : pc.toNat < 64) :
    (pc + 1#7).toNat = pc.toNat + 1 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem engine_cursor (p : Program) (s : State a) (cursor : s.Cursor) :
    (engine p s).Cursor := by
  cases phase : s.phase
  case free => simpa [engine, phase] using cursor
  case completed => simpa [engine, phase] using cursor
  case fault => simpa [engine, phase] using cursor
  case boundary =>
    have active := cursor.active (Or.inl phase)
    simp only [engine, phase]
    split
    · exact ⟨cursor.bound, fun _ => active⟩
    · exact cursor
  case low =>
    have active := cursor.active (Or.inr (Or.inl phase))
    by_cases zero : s.countdown = 0#8 <;> cases guarded : s.current.hasHighGuard
    all_goals constructor <;> simp_all [engine,State.enterHigh,State.captureData,Phase.activeCell] <;> omega
  case waiting =>
    have active := cursor.active (Or.inr (Or.inr (Or.inr phase)))
    cases ready : s.waitReady <;> cases stream : s.current.isStream <;>
      cases expired : s.current.guard.limit.expires s.countdown
    all_goals constructor <;> simp_all [engine,State.enterHigh,State.captureData,State.timeoutFault,
      Phase.activeCell,pc_increment s.pc active] <;> omega
  case high =>
    have active := cursor.active (Or.inr (Or.inr (Or.inl phase)))
    simp only [engine, phase]
    split
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      by_cases again : s.current.isStream = true ∧ 1 < s.remaining.toNat
      · constructor <;> simp_all
        omega
      · constructor <;> simp [again, Phase.activeCell, pc_increment s.pc active]
        omega
    · exact ⟨cursor.bound, fun _ => active⟩
  case fetch =>
    simp only [engine, phase]
    cases fetched : p.fetch s.pc.toNat with
    | none =>
      constructor
      · exact cursor.bound
      · simp [State.stop, Phase.activeCell]
    | some instruction =>
      have bound := fetch_bound p s.pc.toNat instruction fetched
      cases instruction
      case halt =>
        constructor
        · exact cursor.bound
        · simp [State.stop, Phase.activeCell]
      case fault =>
        constructor
        · exact cursor.bound
        · simp [State.stop, Phase.activeCell]
      case driveWait pins guard =>
        exact ⟨Nat.le_of_lt bound,fun _ => bound⟩
      case pulse cell => exact ⟨Nat.le_of_lt bound, fun _ => bound⟩
      case stream cell guard =>
        simp only
        split
        · constructor
          · simpa [pc_increment s.pc bound] using (show s.pc.toNat + 1 ≤ 64 by omega)
          · simp [Phase.activeCell]
        · exact ⟨Nat.le_of_lt bound, fun _ => bound⟩

def Phase.work (phase : Phase) (countdown : Nat) : Nat :=
  match phase with
  | .fetch => 770
  | .boundary => 769
  | .low => 513 + countdown
  | .waiting => 257 + countdown
  | .high => 1 + countdown
  | _ => 0

def State.work (s : State a) : Nat :=
  (64 - s.pc.toNat + s.remaining.toNat) * 1024 + s.phase.work s.countdown.toNat

/-- Service supplies the credits before a LOW reservation; there is no same-edge bypass. -/
def State.Serviced (s : State a) : Prop := s.phase = .boundary → s.canReserve = true


def State.Advancing (s : State a) : Prop := s.Serviced ∧
  (s.phase = .waiting → s.current.guard.limit = .unbounded → s.waitReady = true)

theorem WaitLimit.initialCountdown_le (limit : WaitLimit) : limit.initialCountdown.toNat ≤ 254 := by
  cases limit with
  | unbounded => decide
  | misses n =>
    have bound := n.isLt
    simp [WaitLimit.initialCountdown,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show n.val < 256 by omega)]
    omega

theorem engine_work_decreases (p : Program) (s : State a) (progress : s.Progress)
    (cursor : s.Cursor) (busy : s.phase.busy = true) (advancing : s.Advancing) :
    (engine p s).work < s.work := by
  have service := advancing.1
  cases phase : s.phase
  case high =>
    have pc := cursor.active (Or.inr (Or.inr (Or.inl phase)))
    simp only [engine, phase]
    split
    · by_cases stream : s.current.isStream = true
      · have positive := progress.active stream (Or.inr (Or.inr (Or.inl phase)))
        have minus : (s.remaining - 1#16).toNat = s.remaining.toNat - 1 := by
          apply BitVec.toNat_sub_of_le
          change 1 ≤ s.remaining.toNat
          omega
        by_cases again : 1 < s.remaining.toNat
        all_goals simp [State.work, Phase.work, stream, again, minus, pc_increment s.pc pc, phase]
        all_goals omega
      · simp [State.work, Phase.work, stream, pc_increment s.pc pc, phase]
        omega
    · have nonzero : 0 < s.countdown.toNat := by
        have bv : s.countdown ≠ 0#8 := by simpa using (show ¬(s.countdown == 0) = true by assumption)
        have := BitVec.toNat_ne_iff_ne.mpr bv
        simp only [BitVec.toNat_ofNat] at this
        omega
      have minus : (s.countdown - 1#8).toNat = s.countdown.toNat - 1 := by
        apply BitVec.toNat_sub_of_le
        change 1 ≤ s.countdown.toNat
        omega
      simp [State.work, Phase.work, phase, minus]
      omega
  case boundary =>
    have ready := service phase
    have duration := s.current.cell.lowDuration.isLt
    simp [engine, phase, ready, State.work, Phase.work]
    omega
  case low =>
    by_cases zero : s.countdown = 0#8
    · by_cases guarded : s.current.hasHighGuard = true
      · have duration := s.current.guard.limit.initialCountdown_le
        simp [engine,phase,zero,guarded,State.work,Phase.work]
        omega
      · have duration := s.current.cell.highDuration.isLt
        simp [engine,phase,zero,guarded,State.enterHigh,State.captureData,State.work,Phase.work]
        omega
    · have nonzero : 0 < s.countdown.toNat := by
        have unequal := BitVec.toNat_ne_iff_ne.mpr zero
        simp only [BitVec.toNat_ofNat] at unequal
        omega
      have minus : (s.countdown-1#8).toNat = s.countdown.toNat-1 := by
        apply BitVec.toNat_sub_of_le
        change 1 ≤ s.countdown.toNat
        omega
      simp [engine,phase,zero,State.work,Phase.work,minus]
      omega
  case waiting =>
    by_cases ready : s.waitReady = true
    · rw [engine_wait_ready p s phase ready]
      by_cases stream : s.current.isStream = true
      · have duration := s.current.cell.highDuration.isLt
        simp [stream,State.enterHigh,State.captureData,State.work,Phase.work,phase]
        omega
      · have pc := cursor.active (Or.inr (Or.inr (Or.inr phase)))
        simp [stream,State.work,Phase.work,phase,pc_increment s.pc pc]
        omega
    · cases limit : s.current.guard.limit with
      | unbounded => exact False.elim (ready (advancing.2 phase limit))
      | misses n =>
        by_cases zero : s.countdown = 0#8
        · rw [engine_wait_timeout p s phase (Bool.eq_false_iff.mpr ready)
            (by simp [limit,WaitLimit.expires,zero])]
          simp [State.timeoutFault,State.work,Phase.work,phase]
          omega
        · have nonzero : 0 < s.countdown.toNat := by
            have unequal := BitVec.toNat_ne_iff_ne.mpr zero
            simp only [BitVec.toNat_ofNat] at unequal
            omega
          have minus : (s.countdown-1#8).toNat = s.countdown.toNat-1 := by
            apply BitVec.toNat_sub_of_le
            change 1 ≤ s.countdown.toNat
            omega
          simp [engine,phase,ready,limit,WaitLimit.expires,zero,WaitLimit.poll,State.work,Phase.work,minus]
          omega
  case fetch =>
    simp only [engine, phase]
    cases fetched : p.fetch s.pc.toNat with
    | none => simp [State.stop, State.work, Phase.work, phase]
    | some instruction =>
      have pc := fetch_bound p s.pc.toNat instruction fetched
      cases instruction
      case halt => simp [State.stop, State.work, Phase.work, phase]
      case fault => simp [State.stop, State.work, Phase.work, phase]
      case driveWait pins guard =>
        have duration := guard.limit.initialCountdown_le
        simp [State.work,Phase.work,phase]
        omega
      case pulse cell => simp [State.work, Phase.work, phase]
      case stream cell guard =>
        simp only
        split
        · simp [State.work, Phase.work, phase, pc_increment s.pc pc]
          omega
        · simp [State.work, Phase.work, phase]
  case free => simp [phase, Phase.busy] at busy
  case completed => simp [phase, Phase.busy] at busy
  case fault => simp [phase, Phase.busy] at busy


theorem clock_cursor (p : Program) (s : State a) (i : Input) (cursor : s.Cursor) :
    (clock p i s).Cursor := by
  have next := engine_cursor p s cursor
  exact ⟨next.bound, next.active⟩

theorem step_cursor (p : Program) (s : State a) (i : Input) (cursor : s.Cursor) :
    (step p i s).Cursor := by
  apply step_preserves p s i State.Cursor
  · constructor <;> simp [State.reset, Phase.activeCell]
  · constructor <;> simp [State.reset, Phase.activeCell]
  · constructor <;> simp [State.start, Phase.activeCell]
  · constructor <;> simp [State.release, Phase.activeCell]
  · exact clock_cursor p s i cursor

theorem step_work_decreases (p : Program) (s : State a) (i : Input) (progress : s.Progress)
    (cursor : s.Cursor) (busy : s.phase.busy = true) (advancing : s.Advancing) (runtime : i.Runtime) :
    (step p i s).work < s.work := by
  rw [step_busy_eq_clock p s i runtime busy]
  exact engine_work_decreases p s progress cursor busy advancing

/-- Every nonadvancing state is parked on pre-edge credit or an unbounded guard. -/
theorem not_advancing (s : State a) (blocked : ¬s.Advancing) :
    (s.phase = .boundary ∧ s.canReserve = false) ∨
    (s.phase = .waiting ∧ s.current.guard.limit = .unbounded ∧ s.waitReady = false) := by
  classical
  by_cases service : s.Serviced
  · right
    have notWait : ¬(s.phase = .waiting → s.current.guard.limit = .unbounded → s.waitReady = true) :=
      fun ready => blocked ⟨service,ready⟩
    by_cases phase : s.phase = .waiting
    · by_cases limit : s.current.guard.limit = .unbounded
      · exact ⟨phase,limit,Bool.eq_false_iff.mpr (fun ready => notWait (fun _ _ => ready))⟩
      · exact False.elim (notWait (fun _ same => False.elim (limit same)))
    · exact False.elim (notWait (fun same _ => False.elim (phase same)))
  · left
    have phase : s.phase = .boundary := by
      by_cases phase : s.phase = .boundary
      · exact phase
      · exact False.elim (service (fun same => False.elim (phase same)))
    exact ⟨phase,Bool.eq_false_iff.mpr (fun ready => service (fun _ => ready))⟩

/-- Host traffic and samplers may move during a park; engine control cannot move. -/
theorem step_parked (p : Program) (s : State a) (i : Input) (busy : s.phase.busy = true)
    (runtime : i.Runtime) (blocked : ¬s.Advancing) :
    (step p i s).phase = s.phase ∧ (step p i s).current = s.current ∧
      (step p i s).work = s.work := by
  rw [step_busy_eq_clock p s i runtime busy]
  rcases not_advancing s blocked with ⟨phase,credit⟩ | ⟨phase,limit,ready⟩
  · simp [clock,engine,phase,credit,State.work]
  · simp [clock,engine,phase,limit,ready,WaitLimit.expires,WaitLimit.poll,State.work]

theorem step_work_le (p : Program) (s : State a) (i : Input) (progress : s.Progress)
    (cursor : s.Cursor) (busy : s.phase.busy = true) (runtime : i.Runtime) :
    (step p i s).work ≤ s.work := by
  by_cases advancing : s.Advancing
  · exact Nat.le_of_lt (step_work_decreases p s i progress cursor busy advancing runtime)
  · exact Nat.le_of_eq (step_parked p s i busy runtime advancing).2.2


end Pinwheel.Program.StreamingReady
