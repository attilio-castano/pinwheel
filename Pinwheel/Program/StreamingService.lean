import Pinwheel.Program.StreamingCounting

namespace Pinwheel.Program.Streaming

def Phase.activeCell (phase : Phase) : Prop :=
  phase = .boundary ∨ phase = .low ∨ phase = .high

structure State.Cursor (s : State addrBits) : Prop where
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

theorem engine_cursor (p : Program) (s : State addrBits) (cursor : s.Cursor) :
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
    simp only [engine, phase]
    split <;> exact ⟨cursor.bound, fun _ => active⟩
  case high =>
    have active := cursor.active (Or.inr (Or.inr phase))
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
      case pulse cell => exact ⟨Nat.le_of_lt bound, fun _ => bound⟩
      case stream cell =>
        simp only
        split
        · constructor
          · simpa [pc_increment s.pc bound] using (show s.pc.toNat + 1 ≤ 64 by omega)
          · simp [Phase.activeCell]
        · exact ⟨Nat.le_of_lt bound, fun _ => bound⟩

def Phase.work (phase : Phase) (countdown : Nat) : Nat :=
  match phase with
  | .fetch => 515
  | .boundary => 514
  | .low => 258 + countdown
  | .high => 1 + countdown
  | _ => 0

def State.work (s : State addrBits) : Nat :=
  (64 - s.pc.toNat + s.remaining.toNat) * 515 + s.phase.work s.countdown.toNat

/-- Service supplies the credits before a LOW reservation; there is no same-edge bypass. -/
def State.Serviced (s : State addrBits) : Prop := s.phase = .boundary → s.canReserve = true

theorem engine_work_decreases (p : Program) (s : State addrBits) (progress : s.Progress)
    (cursor : s.Cursor) (busy : s.phase.busy = true) (service : s.Serviced) :
    (engine p s).work < s.work := by
  cases phase : s.phase
  case high =>
    have pc := cursor.active (Or.inr (Or.inr phase))
    simp only [engine, phase]
    split
    · by_cases stream : s.current.isStream = true
      · have positive := progress.active stream (Or.inr (Or.inr phase))
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
    simp only [engine, phase]
    split
    · have duration := s.current.cell.highDuration.isLt
      have zero : s.countdown.toNat = 0 := by
        have bv : s.countdown = 0#8 := by simpa using (show (s.countdown == 0) = true by assumption)
        simp [bv]
      simp [State.work, Phase.work, phase, zero]
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
  case fetch =>
    simp only [engine, phase]
    cases fetched : p.fetch s.pc.toNat with
    | none => simp [State.stop, State.work, Phase.work, phase]
    | some instruction =>
      have pc := fetch_bound p s.pc.toNat instruction fetched
      cases instruction
      case halt => simp [State.stop, State.work, Phase.work, phase]
      case fault => simp [State.stop, State.work, Phase.work, phase]
      case pulse cell => simp [State.work, Phase.work, phase]
      case stream cell =>
        simp only
        split
        · simp [State.work, Phase.work, phase, pc_increment s.pc pc]
          omega
        · simp [State.work, Phase.work, phase]
  case free => simp [phase, Phase.busy] at busy
  case completed => simp [phase, Phase.busy] at busy
  case fault => simp [phase, Phase.busy] at busy

theorem clock_cursor (p : Program) (s : State addrBits) (i : Input) (cursor : s.Cursor) :
    (clock p i s).Cursor := by
  have next := engine_cursor p s cursor
  exact ⟨next.bound, next.active⟩

theorem step_cursor (p : Program) (s : State addrBits) (i : Input) (cursor : s.Cursor) :
    (step p i s).Cursor := by
  apply step_preserves p s i State.Cursor
  · constructor <;> simp [State.reset, Phase.activeCell]
  · constructor <;> simp [State.reset, Phase.activeCell]
  · constructor <;> simp [State.start, Phase.activeCell]
  · constructor <;> simp [State.release, Phase.activeCell]
  · exact clock_cursor p s i cursor

theorem step_work_decreases (p : Program) (s : State addrBits) (i : Input) (progress : s.Progress)
    (cursor : s.Cursor) (busy : s.phase.busy = true) (service : s.Serviced) (runtime : i.Runtime) :
    (step p i s).work < s.work := by
  rw [step_busy_eq_clock p s i runtime busy]
  exact engine_work_decreases p s progress cursor busy service

theorem engine_live (p : Program) (s : State addrBits) (busy : s.phase.busy = true) :
    (engine p s).phase.busy = true ∨ (engine p s).phase.retained = true := by
  cases phase : s.phase
  case fetch =>
    simp only [engine, phase]
    cases p.fetch s.pc.toNat with
    | none => right; rfl
    | some instruction =>
      cases instruction
      case halt => right; rfl
      case fault => right; rfl
      case pulse cell => left; rfl
      case stream cell => simp only; split <;> left <;> rfl
  case boundary =>
    simp only [engine, phase]
    split
    · left; rfl
    · left; exact busy
  case low => simp only [engine, phase]; split <;> left <;> rfl
  case high =>
    simp only [engine, phase]
    split
    · split <;> left <;> rfl
    · left; rfl
  case free => simp [phase, Phase.busy] at busy
  case completed => simp [phase, Phase.busy] at busy
  case fault => simp [phase, Phase.busy] at busy

def ServiceHistory (p : Program) (s : State addrBits) : List Input → Prop
  | [] => True
  | i :: inputs => i.Runtime ∧ s.Serviced ∧ ServiceHistory p (step p i s) inputs

theorem service_reaches_retained (p : Program) (s : State addrBits) (inputs : List Input)
    (progress : s.Progress) (cursor : s.Cursor) (busy : s.phase.busy = true)
    (service : ServiceHistory p s inputs) (enough : s.work ≤ inputs.length) :
    ∃ edges, edges ≤ inputs.length ∧ edges ≤ s.work ∧
      (run p s (inputs.take edges)).phase.retained = true := by
  induction inputs generalizing s with
  | nil =>
    have positive : 0 < s.work := by
      cases phase : s.phase <;> simp_all [Phase.busy, State.work, Phase.work] <;> omega
    simp only [List.length_nil] at enough
    omega
  | cons i inputs induction =>
    rcases service with ⟨runtime, supplied, later⟩
    have decrease := step_work_decreases p s i progress cursor busy supplied runtime
    have live : (step p i s).phase.busy = true ∨ (step p i s).phase.retained = true := by
      rw [step_busy_eq_clock p s i runtime busy]
      exact engine_live p s busy
    rcases live with nextBusy | retained
    · have enoughNext : (step p i s).work ≤ inputs.length := by
        simp only [List.length_cons] at enough
        omega
      obtain ⟨edges, within, bounded, final⟩ := induction (step p i s)
        (step_progress p s i progress) (step_cursor p s i cursor) nextBusy later enoughNext
      refine ⟨edges + 1, by simp; omega, by omega, ?_⟩
      simpa [run] using final
    · refine ⟨1, by simp, by omega, ?_⟩
      simpa [run] using retained

theorem started_service (p : Program) (before : State addrBits) (start : Input) (inputs : List Input)
    (service : ServiceHistory p (before.start p start) inputs)
    (enough : (start.startCount.toNat + 65) * 515 ≤ inputs.length) :
    ∃ edges, edges ≤ inputs.length ∧ edges ≤ (start.startCount.toNat + 65) * 515 ∧
      (run p (before.start p start) (inputs.take edges)).phase.retained = true := by
  have budget : (before.start p start).work = (start.startCount.toNat + 65) * 515 := by
    simp [State.work, State.start, Phase.work]
    omega
  have cursor : (before.start p start).Cursor := by
    constructor <;> simp [State.start, Phase.activeCell]
  simpa only [budget] using service_reaches_retained p (before.start p start) inputs
    (before.start_progress p start) cursor rfl service (budget ▸ enough)

end Pinwheel.Program.Streaming
