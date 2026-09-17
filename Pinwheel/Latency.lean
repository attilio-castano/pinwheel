import Std

/-! Input latency as a parameter of pin-level contracts. A controller behind `d`
input registers consumes on its cycle `n` what the pins carried on cycle `n - d`.
Protocol theorems that hold for every input history then specialize to pin
histories by substitution; what remains protocol-specific is which assumptions
about the peer make the delayed history a good one. -/
namespace Pinwheel.Latency

/-- The history consumed behind `d` registers that all held `idle` at cycle zero. -/
def delayed (d : Nat) (idle : α) (pins : Nat → α) (cycle : Nat) : α :=
  if cycle < d then idle else pins (cycle - d)

theorem delayed_zero (idle : α) (pins : Nat → α) : delayed 0 idle pins = pins := by
  funext cycle
  simp [delayed]

/-- After the pipeline has drained, the controller sees exactly the pins, late. -/
theorem delayed_shift (d : Nat) (idle : α) (pins : Nat → α) (cycle : Nat) :
    delayed d idle pins (cycle + d) = pins cycle := by
  simp only [delayed, show ¬ cycle + d < d by omega, if_false, Nat.add_sub_cancel]

theorem delayed_draining (d : Nat) (idle : α) (pins : Nat → α) (cycle : Nat) (h : cycle < d) :
    delayed d idle pins cycle = idle := by
  simp [delayed, h]

/-- Pipelines compose: `a` stages behind `b` stages are `a + b` stages. -/
theorem delayed_add (a b : Nat) (idle : α) (pins : Nat → α) :
    delayed a idle (delayed b idle pins) = delayed (a + b) idle pins := by
  funext cycle
  simp only [delayed]
  by_cases ha : cycle < a
  · simp [ha, show cycle < a + b by omega]
  · by_cases hb : cycle - a < b
    · simp [ha, hb, show cycle < a + b by omega]
    · simp [ha, hb, show ¬ cycle < a + b by omega, Nat.sub_sub]

end Pinwheel.Latency
