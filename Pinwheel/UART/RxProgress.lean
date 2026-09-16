import Pinwheel.UART.RxProofs

namespace Pinwheel.UART.Rx

/-- A lower bound on edges until completion, independent of future pin values. -/
def progress (cfg : Config) (s : State) : Nat :=
  match s.phase with
  | .ready | .finished => 0
  | .idle => cfg.half + 9 * cfg.bitCycles + 2
  | .falling => cfg.half + 9 * cfg.bitCycles + 1
  | .timed symbol => s.remaining.val + 1 + (9 - symbol.val) * cfg.bitCycles

theorem progress_advance (cfg : Config) (s : State) (input : Bool) :
    progress cfg s ≤ progress cfg (advance cfg s input) + 1 := by
  rcases s with ⟨phase, remaining, samples⟩
  cases phase
  case timed symbol =>
    have cases : symbol.val = 0 ∨ symbol.val = 1 ∨ symbol.val = 2 ∨ symbol.val = 3 ∨
      symbol.val = 4 ∨ symbol.val = 5 ∨ symbol.val = 6 ∨ symbol.val = 7 ∨
      symbol.val = 8 ∨ symbol.val = 9 := by omega
    have minimum := cfg.minimum
    rcases cases with h | h | h | h | h | h | h | h | h | h
    all_goals grind [progress, advance, finishSymbol, enterSymbol, observe, duration, Config.half]
  all_goals have minimum := cfg.minimum
  all_goals grind [progress, advance, enterSymbol, observe, duration, Config.half]

theorem progress_run (cfg : Config) (s : State) (incoming : Nat → Bool) (n : Nat) :
    progress cfg s ≤ progress cfg (run cfg s incoming n) + n := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    exact Nat.le_trans ih (by
      simpa only [run, Nat.add_assoc, Nat.add_comm 1 n] using
        Nat.add_le_add_right (progress_advance cfg (run cfg s incoming n) (incoming (n + 1))) n)

theorem busy_of_progress (cfg : Config) (s : State) (positive : 0 < progress cfg s) : busy s = true := by
  cases h : s.phase <;> simp_all [progress, busy]

theorem result_none_of_busy (s : State) (active : busy s = true) : result s = none := by
  cases h : s.phase <;> simp_all [busy, result]

theorem progress_start (cfg : Config) (slots : Vector Bool 16) :
    progress cfg (enterSymbol cfg ⟨.ready, 0, slots⟩ 0) = cfg.half + 9 * cfg.bitCycles := by
  have minimum := cfg.minimum
  simp [progress, enterSymbol, duration, Config.half]
  omega

theorem armed_busy_before (cfg : Config) (incoming : Nat → Bool) (detected n : Nat)
    (later : 2 ≤ detected) (high : ∀ t, 1 ≤ t → t < detected → incoming t = true)
    (low : incoming detected = false) (before : n < detected + (cfg.half + 9 * cfg.bitCycles)) :
    busy (run cfg initial incoming n) = true := by
  by_cases earlier : n < detected
  case neg =>
    rw [show n = detected + (n - detected) by omega, run_add,
      detect_start cfg incoming detected later high low]
    apply busy_of_progress cfg
    have bound := progress_run cfg (enterSymbol cfg ⟨.ready, 0, Vector.replicate 16 false⟩ 0)
      (fun t => incoming (detected + t)) (n - detected)
    rw [progress_start] at bound
    omega
  case pos =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [waiting_high cfg incoming n (fun t ht hb => high t ht (by omega))]
      rfl

end Pinwheel.UART.Rx
