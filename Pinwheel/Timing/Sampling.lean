import Std

/-! # Sampling a continuous-time line with the core clock

Program proofs count core clock cycles. This module relates them to real time.
Time is a natural number in any unit fine enough to express the relevant
instants exactly (for example picoseconds, or 1/(f·R) seconds). The core clock
samples the line once per `period` units, sample `n` at time `n * period`;
the sampling phase relative to the line is free, because line events may fall
at any instant.

`firstSample period x` is the index of the first sample taken at or after `x`.
The main result, `firstSample_skew`, shows that events within `slack` time
units of a schedule that is a whole number `cycles` of samples per step stay
within `slack / period` samples (rounded up) of that schedule after sampling.
Quantization at both ends cancels: the bound does not grow by one sample. -/
namespace Pinwheel.Timing

/-- Index of the first sample at or after time `x`. -/
def firstSample (period x : Nat) : Nat := (x + period - 1) / period

theorem firstSample_spec (period x : Nat) (positive : 0 < period) :
    x ≤ firstSample period x * period ∧ firstSample period x * period < x + period := by
  unfold firstSample
  constructor
  · have := Nat.lt_mul_div_succ (x + period - 1) positive
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at this
    omega
  · have := Nat.div_mul_le_self (x + period - 1) period
    omega

/-- A sample index `t` is before the event at `x` exactly when its time is. -/
theorem lt_firstSample_iff (period x t : Nat) (positive : 0 < period) :
    t < firstSample period x ↔ t * period < x := by
  have spec := firstSample_spec period x positive
  constructor
  · intro h
    have : (t + 1) * period ≤ firstSample period x * period := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · intro h
    apply Nat.lt_of_not_le
    intro le
    have : firstSample period x * period ≤ t * period := Nat.mul_le_mul_right _ le
    omega

private theorem lt_of_mul (period a b : Nat) (h : a * period < b * period) : a < b :=
  Nat.lt_of_mul_lt_mul_right h

/-- Events within `slack ≤ samples * period` of the schedule `start + k * cycles * period`
are first sampled within `samples` samples of `firstSample start + k * cycles`. -/
theorem firstSample_skew (period cycles samples slack start event k : Nat) (positive : 0 < period)
    (within : slack ≤ samples * period)
    (late : start + k * (cycles * period) ≤ event + slack)
    (early : event ≤ start + k * (cycles * period) + slack) :
    firstSample period start + k * cycles ≤ firstSample period event + samples ∧
      firstSample period event ≤ firstSample period start + k * cycles + samples := by
  have s := firstSample_spec period start positive
  have e := firstSample_spec period event positive
  have step : k * (cycles * period) = (k * cycles) * period := by rw [Nat.mul_assoc]
  rw [step] at late early
  constructor
  · apply Nat.le_of_lt_succ
    apply lt_of_mul period
    simp only [Nat.succ_mul, Nat.add_mul]
    omega
  · apply Nat.le_of_lt_succ
    apply lt_of_mul period
    simp only [Nat.succ_mul, Nat.add_mul]
    omega

theorem firstSample_mono (period x y : Nat) (le : x ≤ y) :
    firstSample period x ≤ firstSample period y :=
  Nat.div_le_div_right (by omega)

/-- An interval of real length between `low` and `high` periods spans between
`low` and `high` samples: the sample counts round the same way at both ends. -/
theorem firstSample_gap (period low high a b : Nat) (positive : 0 < period)
    (atLeast : a + low * period ≤ b) (atMost : b ≤ a + high * period) :
    firstSample period a + low ≤ firstSample period b ∧
      firstSample period b ≤ firstSample period a + high := by
  have s := firstSample_spec period a positive
  have e := firstSample_spec period b positive
  constructor
  · apply Nat.le_of_lt_succ
    apply lt_of_mul period
    simp only [Nat.succ_mul, Nat.add_mul]
    omega
  · apply Nat.le_of_lt_succ
    apply lt_of_mul period
    simp only [Nat.succ_mul, Nat.add_mul]
    omega

end Pinwheel.Timing
