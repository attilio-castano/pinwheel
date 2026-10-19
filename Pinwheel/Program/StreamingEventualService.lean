import Pinwheel.Program.StreamingTiming

/-! Weak host-service fairness permits arbitrary finite parked intervals.
It gives termination, without a real-time bound on those intervals. -/
namespace Pinwheel.Program.Streaming

theorem step_work_le (p : Program) (s : State a) (i : Input) (progress : s.Progress)
    (cursor : s.Cursor) (busy : s.phase.busy = true) (runtime : i.Runtime) :
    (step p i s).work ≤ s.work := by
  by_cases supplied : s.Serviced
  · exact Nat.le_of_lt (step_work_decreases p s i progress cursor busy supplied runtime)
  · have boundary : s.phase = .boundary := by
      by_cases boundary : s.phase = .boundary
      · exact boundary
      · exact False.elim (supplied (fun phase => False.elim (boundary phase)))
    have blocked : s.canReserve = false := by
      cases credit : s.canReserve
      · rfl
      · exact False.elim (supplied (fun _ => credit))
    rw [step_busy_eq_clock p s i runtime busy]
    simp [clock, engine, boundary, blocked, State.work]

namespace EventualService

def clocks (incoming : Nat → Input) (edges : Nat) : List Input :=
  (List.range edges).map incoming

def state (p : Program) (initial : State a) (incoming : Nat → Input) : Nat → State a
  | 0 => initial
  | n+1 => step p (incoming n) (state p initial incoming n)

theorem state_eq_run (p : Program) (initial : State a) (incoming : Nat → Input) (edges : Nat) :
    state p initial incoming edges = run p initial (clocks incoming edges) := by
  induction edges with
  | zero => rfl
  | succ edges induction =>
    simp [state,clocks,List.range_succ,run,List.foldl_append,induction]

/-- Weak fairness is about actual reached states, without an outcome premise. -/
def Fair (p : Program) (initial : State a) (incoming : Nat → Input) : Prop :=
  ∀ n, (state p initial incoming n).phase = .boundary →
    ∃ m, n ≤ m ∧ (state p initial incoming m).canReserve = true

theorem progress (p : Program) (initial : State a) (incoming : Nat → Input)
    (initialProgress : initial.Progress) (n : Nat) :
    (state p initial incoming n).Progress := by
  induction n with
  | zero => exact initialProgress
  | succ n induction => exact step_progress p _ _ induction

theorem cursor (p : Program) (initial : State a) (incoming : Nat → Input)
    (initialCursor : initial.Cursor) (n : Nat) :
    (state p initial incoming n).Cursor := by
  induction n with
  | zero => exact initialCursor
  | succ n induction => exact step_cursor p _ _ induction

theorem busy_if_not_retained (p : Program) (initial : State a) (incoming : Nat → Input)
    (runtime : ∀ n, (incoming n).Runtime) (initialBusy : initial.phase.busy = true)
    (notRetained : ∀ n, (state p initial incoming n).phase.retained ≠ true) (n : Nat) :
    (state p initial incoming n).phase.busy = true := by
  induction n with
  | zero => exact initialBusy
  | succ n induction =>
    have live := engine_live p (state p initial incoming n) induction
    change (clock p (incoming n) (state p initial incoming n)).phase.busy = true ∨
      (clock p (incoming n) (state p initial incoming n)).phase.retained = true at live
    rw [← step_busy_eq_clock p _ _ (runtime n) induction] at live
    rcases live with busy | retained
    · exact busy
    · exact False.elim (notRetained (n+1) retained)

theorem work_add_le (p : Program) (initial : State a) (incoming : Nat → Input)
    (runtime : ∀ n, (incoming n).Runtime) (initialProgress : initial.Progress)
    (initialCursor : initial.Cursor) (busy : ∀ n, (state p initial incoming n).phase.busy = true)
    (n distance : Nat) :
    (state p initial incoming (n+distance)).work ≤ (state p initial incoming n).work := by
  induction distance with
  | zero => exact Nat.le_refl _
  | succ distance induction =>
    exact Nat.le_trans (step_work_le p _ _ (progress p initial incoming initialProgress (n+distance))
      (cursor p initial incoming initialCursor (n+distance)) (busy (n+distance)) (runtime (n+distance))) induction

theorem later_decrease (p : Program) (initial : State a) (incoming : Nat → Input)
    (runtime : ∀ n, (incoming n).Runtime) (initialProgress : initial.Progress)
    (initialCursor : initial.Cursor) (busy : ∀ n, (state p initial incoming n).phase.busy = true)
    (fair : Fair p initial incoming) (n : Nat) :
    ∃ m, n ≤ m ∧ (state p initial incoming (m+1)).work < (state p initial incoming n).work := by
  have supplied : ∃ m, n ≤ m ∧ (state p initial incoming m).Serviced := by
    by_cases boundary : (state p initial incoming n).phase = .boundary
    · obtain ⟨m, later, ready⟩ := fair n boundary
      exact ⟨m, later, fun _ => ready⟩
    · exact ⟨n, Nat.le_refl _, fun same => False.elim (boundary same)⟩
  obtain ⟨m, later, ready⟩ := supplied
  obtain ⟨distance, equals⟩ := Nat.le.dest later
  have before := work_add_le p initial incoming runtime initialProgress initialCursor busy n distance
  rw [equals] at before
  exact ⟨m, later, Nat.lt_of_lt_of_le
    (step_work_decreases p _ _ (progress p initial incoming initialProgress m)
      (cursor p initial incoming initialCursor m) (busy m) ready (runtime m)) before⟩

/-- Every finite stall is allowed; fairness excludes an infinite unsupplied boundary. -/
theorem reaches_retained (p : Program) (initial : State a) (incoming : Nat → Input)
    (runtime : ∀ n, (incoming n).Runtime) (initialProgress : initial.Progress)
    (initialCursor : initial.Cursor) (initialBusy : initial.phase.busy = true)
    (fair : Fair p initial incoming) :
    ∃ n, (state p initial incoming n).phase.retained = true := by
  classical
  by_cases reached : ∃ n, (state p initial incoming n).phase.retained = true
  · exact reached
  · have notRetained : ∀ n, (state p initial incoming n).phase.retained ≠ true :=
      fun n retained => reached ⟨n,retained⟩
    have busy := busy_if_not_retained p initial incoming runtime initialBusy notRetained
    have impossible : ∀ k, ∀ n, (state p initial incoming n).work = k → False := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k induction =>
        intro n equal
        obtain ⟨m, _, smaller⟩ := later_decrease p initial incoming runtime initialProgress initialCursor busy fair n
        exact induction _ (equal ▸ smaller) (m+1) rfl
    exact False.elim (impossible initial.work 0 rfl)

/-- START establishes every progress premise; fairness does not assume success. -/
theorem started (p : Program) (before : State a) (start : Input) (incoming : Nat → Input)
    (runtime : ∀ n, (incoming n).Runtime)
    (fair : Fair p (before.start p start) incoming) :
    ∃ edges, (run p (before.start p start) (clocks incoming edges)).phase.retained = true := by
  have initialCursor : (before.start p start).Cursor := by
    constructor <;> simp [State.start, Phase.activeCell]
  obtain ⟨edges, retained⟩ := reaches_retained p (before.start p start) incoming runtime
    (before.start_progress p start) initialCursor rfl fair
  exact ⟨edges, (state_eq_run p _ incoming edges) ▸ retained⟩

/-- The same finite-prefix conclusion begins at an actually admitted START edge. -/
theorem admitted_start (p : Program) (before : State a) (start : Input) (incoming : Nat → Input)
    (startRuntime : start.Runtime)
    (admitted : (start.command == 3 && before.canStart start) = true)
    (runtime : ∀ n, (incoming n).Runtime)
    (fair : Fair p (step p start before) incoming) :
    ∃ edges, (run p (step p start before) (clocks incoming edges)).phase.retained = true := by
  have actual : step p start before = before.start p start := by
    rcases startRuntime with ⟨cold, _⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at admitted
    simp [step, cold, admitted.1, admitted.2]
  rw [actual] at fair ⊢
  exact started p before start incoming runtime fair

end EventualService

end Pinwheel.Program.Streaming
