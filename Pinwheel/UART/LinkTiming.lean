import Pinwheel.UART.Link

namespace Pinwheel.UART.Link

/-- The affine timing error stays between its start/stop endpoint bounds. -/
theorem sample_windows (t : Timing) (b : Latency) (safe : Safe t b) (symbol : Fin 10) :
    symbol.val * t.txBit + b.spread ≤ t.center + symbol.val * t.rxBit ∧
    t.center + symbol.val * t.rxBit + b.spread + t.rxTick ≤ (symbol.val + 1) * t.txBit := by
  have cases : symbol.val = 0 ∨ symbol.val = 1 ∨ symbol.val = 2 ∨ symbol.val = 3 ∨
      symbol.val = 4 ∨ symbol.val = 5 ∨ symbol.val = 6 ∨ symbol.val = 7 ∨
      symbol.val = 8 ∨ symbol.val = 9 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h
  all_goals simp only [h, Safe] at safe ⊢
  all_goals omega
  done

theorem edge_monotone (t : Timing) (a b : Nat) (h : a ≤ b) : t.edge a ≤ t.edge b :=
  Nat.add_le_add_left (Nat.mul_le_mul_right t.rxTick h) t.rxPhase

theorem firstEdge_bounds (t : Timing) (delay : Nat) (later : t.rxPhase < t.txStart + delay) :
    1 ≤ firstEdge t delay ∧ t.txStart + delay ≤ t.edge (firstEdge t delay) ∧
      t.edge (firstEdge t delay) < t.txStart + delay + t.rxTick := by
  have division := Nat.mod_add_div' (t.txStart + delay - t.rxPhase - 1) t.rxTick
  have remainder := Nat.mod_lt (t.txStart + delay - t.rxPhase - 1) t.rxTickPositive
  simp only [firstEdge, Timing.edge, Nat.add_mul, Nat.one_mul]
  constructor
  case right => omega
  case left => exact Nat.succ_le_succ (Nat.zero_le _)
  done

theorem edge_before_first (t : Timing) (delay n : Nat)
    (later : t.rxPhase < t.txStart + delay) (before : n < firstEdge t delay) :
    t.edge n < t.txStart + delay := by
  have product := (Nat.le_div_iff_mul_le t.rxTickPositive).1 (Nat.le_of_lt_succ before)
  unfold Timing.edge
  omega
  done

theorem armed_phase (t : Timing) (b : Latency) (safe : Safe t b) :
    t.rxPhase < t.txStart + b.earliest :=
  Nat.lt_of_le_of_lt (Nat.le_add_right t.rxPhase (1 * t.rxTick)) safe.1

theorem detection_window (t : Timing) (b : Latency) (safe : Safe t b) (detected : Nat)
    (lo : firstEdge t b.earliest ≤ detected) (hi : detected ≤ firstEdge t b.latest) :
    t.txStart + b.earliest ≤ t.edge detected ∧
      t.edge detected < t.txStart + b.latest + t.rxTick :=
  ⟨Nat.le_trans (firstEdge_bounds t b.earliest (armed_phase t b safe)).2.1 (edge_monotone t _ _ lo),
    Nat.lt_of_le_of_lt (edge_monotone t _ _ hi) (firstEdge_bounds t b.latest
      (Nat.lt_of_lt_of_le (armed_phase t b safe) (Nat.add_le_add_left b.ordered t.txStart))).2.2⟩

theorem sample_edge (t : Timing) (detected : Nat) (symbol : Fin 10) :
    t.edge (Rx.sampleTime t.rx detected symbol) = t.edge detected + t.center + symbol.val * t.rxBit := by
  simp [Timing.edge, Rx.sampleTime, Timing.center, Timing.rxBit, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  done

theorem observation_window (t : Timing) (b : Latency) (safe : Safe t b) (age : Nat → Nat)
    (within : b.Contains age) (detected : Nat)
    (lo : firstEdge t b.earliest ≤ detected) (hi : detected ≤ firstEdge t b.latest) (symbol : Fin 10) :
    t.txStart + age (Rx.sampleTime t.rx detected symbol) + symbol.val * t.txBit ≤
        t.edge (Rx.sampleTime t.rx detected symbol) ∧
      t.edge (Rx.sampleTime t.rx detected symbol) <
        t.txStart + age (Rx.sampleTime t.rx detected symbol) + (symbol.val + 1) * t.txBit := by
  have phase := detection_window t b safe detected lo hi
  have window := sample_windows t b safe symbol
  have bounded := within (Rx.sampleTime t.rx detected symbol)
  simp only [sample_edge, Latency.spread] at window ⊢
  omega
  done

theorem latest_start_window (t : Timing) (b : Latency) (safe : Safe t b)
    (age : Nat → Nat) (within : b.Contains age) :
    t.txStart + age (firstEdge t b.latest) ≤ t.edge (firstEdge t b.latest) ∧
      t.edge (firstEdge t b.latest) < t.txStart + age (firstEdge t b.latest) + t.txBit := by
  have bounds := firstEdge_bounds t b.latest
    (Nat.lt_of_lt_of_le (armed_phase t b safe) (Nat.add_le_add_left b.ordered t.txStart))
  have bounded := within (firstEdge t b.latest)
  have margin := safe.2.2.1
  simp only [Latency.spread] at margin
  omega
  done

end Pinwheel.UART.Link
