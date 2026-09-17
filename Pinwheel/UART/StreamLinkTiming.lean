import Pinwheel.UART.StreamLink

namespace Pinwheel.UART.StreamLink
open Link

theorem next_edge (t : Timing) (rearm n : Nat) :
    (next t rearm).edge n = t.edge (rearm + n) := by
  simp [next, Timing.edge, Nat.add_mul, Nat.add_assoc]

theorem completion_edge (t : Timing) (d extra : Nat) :
    t.edge (completion t d + extra) = t.edge d + t.center + 9 * t.rxBit + extra * t.rxTick := by
  simp [completion, Timing.edge, Timing.center, Timing.rxBit, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem sample_before_completion (t : Timing) (d : Nat) (symbol : Fin 10) :
    Rx.sampleTime t.rx d symbol ≤ completion t d := by
  have bound := Nat.mul_le_mul_right t.rx.bitCycles (show symbol.val ≤ 9 from by omega)
  unfold Rx.sampleTime completion
  omega

theorem rearm_before_next (t : Timing) (b : Latency) (d : Nat) (safe : Safe t b)
    (lo : firstEdge t b.earliest ≤ d) (hi : d ≤ firstEdge t b.latest) :
    t.edge (completion t d + 2) < t.txStart + 10 * t.txBit + b.earliest := by
  have phase := detection_window t b safe.1 d lo hi
  simp only [Safe, Latency.spread, completion_edge] at safe ⊢
  omega

theorem after_stop (t : Timing) (b : Latency) (d n : Nat) (safe : Safe t b)
    (lo : firstEdge t b.earliest ≤ d) (hi : d ≤ firstEdge t b.latest)
    (age : Nat → Nat) (within : b.Contains age) (after : completion t d ≤ n) :
    t.txStart + age n + 9 * t.txBit ≤ t.edge n := by
  have phase := detection_window t b safe.1 d lo hi
  have later := edge_monotone t (completion t d) n after
  have finished := completion_edge t d 0
  have bounded := within n
  simp only [Safe, Link.Safe, Latency.spread, Nat.add_zero, Nat.zero_mul] at safe finished
  omega

end Pinwheel.UART.StreamLink
