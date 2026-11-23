import Pinwheel.Timing.Sampling
import Pinwheel.Program.StreamingI2CDeadline

/-! # Clock contract for I²C clock stretching

The I²C image releases SCL and polls it until the target lets it rise. The
cycle-level proofs count that wait in raw samples: a target holding SCL low
for `stretch` samples is served when `stretch + 2 ≤ B` (`stretch_success_for`)
and faulted when SCL is still low at sample `B - 2` (`missed_guard_for`), where
`B` is the profile's poll budget minus one.

This module states the same result in real time. A target that releases SCL
at time `release` after the first sample of the wait is served exactly when
`release ≤ (B - 2) · P`, with `P` the core clock period (`served`, `faulted`).
There is no gap between the two cases.

So the time a target may stretch the clock is `tolerance profile` core periods.
It is fixed in clocks, which means it shrinks as the core clock speeds up: the
standard profile allows 28 clocks, 7 µs at 4 MHz, and no profile allows more
than 252 clocks, 5.04 µs at the 20 ns physical target (`tolerance_le`).

The SCL LOW/HIGH durations and SDA setup times that the I²C standard bounds in
real time are not covered here: the existing proofs do not yet state them as
waveform durations, so they cannot be converted. -/
namespace Pinwheel.Program.StreamingI2CClock
open Pinwheel.Timing Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingI2CDeadline

/-- The target holds SCL low until real time `release`, measured from the
first raw sample of the wait, and drives SDA as `sda` throughout. -/
def realTarget (release : Nat) (sda : Pinwheel.I2C.Drive) (x : Nat) : Pinwheel.I2C.Pins :=
  ⟨if x < release then .low else .release, sda⟩

theorem target_sampled (period release : Nat) (positive : 0 < period) (sda : Pinwheel.I2C.Drive) (k : Nat) :
    target (firstSample period release) sda k = realTarget release sda (k * period) := by
  simp only [target, realTarget, lt_firstSample_iff period release k positive]

/-- Raw inputs that sample a real-time target at every core clock. -/
structure Sampled (s : State a) (period release : Nat) (sda : Pinwheel.I2C.Drive) (inputs : List Input) :
    Prop where
  ordinary : ∀ i ∈ inputs, i.Runtime
  resolved : ∀ k (inside : k < inputs.length),
    inputs[k].rawInputs = StreamingI2CRead.resolvedRaw s.pins (realTarget release sda (k * period))

theorem Sampled.stimulus {s : State a} {period release sda inputs}
    (h : Sampled s period release sda inputs) (positive : 0 < period) :
    Stimulus s (firstSample period release) sda inputs :=
  ⟨h.ordinary, fun k inside => by rw [h.resolved k inside, target_sampled period release positive sda k]⟩

/-- How long a target may hold SCL low, in core clocks. -/
def tolerance (profile : I2cProfile) : Nat := profile.budgetMinusOne.val - 2

theorem budget_two (profile : I2cProfile) : 2 ≤ profile.budgetMinusOne.val := by
  have := profile.waitMargin
  omega

/-- The profile's declared stretch bound is within the tolerance. -/
theorem stretchBound_le (profile : I2cProfile) : profile.stretchBound ≤ tolerance profile := by
  have := profile.waitMargin
  simp only [tolerance]
  omega

theorem tolerance_le (profile : I2cProfile) : tolerance profile ≤ 252 := by
  have := profile.budgetMinusOne.isLt
  simp only [tolerance]
  omega

theorem standard_tolerance : tolerance .standard = 28 := rfl

theorem served_iff (profile : I2cProfile) (period release : Nat) (positive : 0 < period) :
    firstSample period release + 2 ≤ profile.budgetMinusOne.val ↔ release ≤ tolerance profile * period := by
  have two := budget_two profile
  have key := lt_firstSample_iff period release (tolerance profile) positive
  simp only [tolerance] at key ⊢
  omega

/-- A target that releases SCL within `tolerance` core periods is served:
the next SDA bit is captured and the slot continues to HIGH. -/
theorem served (profile : I2cProfile) (s : State a) (entry : WaitEntry s profile) (trace : BitTrace)
    (period release : Nat) (positive : 0 < period) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (sampled : Sampled s period release sda inputs) (inTime : release ≤ tolerance profile * period)
    (length : inputs.length = firstSample period release + 3) :
    CaptureResult s (run (programFor profile) s inputs) trace (traceRun (programFor profile) s trace inputs)
      (StreamingI2CRead.resolvedRaw s.pins
        (target (firstSample period release) sda (firstSample period release)))[1] profile :=
  stretch_success_for profile s entry trace _ sda inputs (sampled.stimulus positive)
    ((served_iff profile period release positive).mpr inTime) length

/-- A target that holds SCL low past `tolerance` core periods faults the
transfer, keeping the bits already captured. -/
theorem faulted (profile : I2cProfile) (s : State a) (entry : WaitEntry s profile) (trace : BitTrace)
    (period release : Nat) (positive : 0 < period) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (sampled : Sampled s period release sda inputs) (late : tolerance profile * period < release)
    (length : inputs.length = profile.budgetMinusOne.val + 1) :
    GuardedCell.TimeoutResult (programFor profile) s (run (programFor profile) s inputs)
      trace (traceRun (programFor profile) s trace inputs) := by
  apply missed_guard_for profile s entry trace inputs length sampled.ordinary
  intro k inside early
  rw [(sampled.stimulus positive).scl entry.release k inside]
  have before : k * period < release := by
    have : k * period ≤ tolerance profile * period :=
      Nat.mul_le_mul_right _ (by simp only [tolerance]; omega)
    omega
  have := (lt_firstSample_iff period release k positive).mpr before
  simp only [decide_eq_false_iff_not, Nat.not_le]
  exact this

/-- In physical units: with `hz * period = unitsPerSecond`, the deadline is
`tolerance / hz` seconds. -/
theorem in_time_iff (profile : I2cProfile) (hz period unitsPerSecond release : Nat) (positive : 0 < hz)
    (clock : hz * period = unitsPerSecond) :
    release ≤ tolerance profile * period ↔ hz * release ≤ tolerance profile * unitsPerSecond := by
  rw [← clock, Nat.mul_left_comm]
  exact ⟨fun h => Nat.mul_le_mul_left _ h, fun h => Nat.le_of_mul_le_mul_left h positive⟩

/-- The standard profile at 4 MHz: a target may stretch for 7000 ns. -/
theorem standard_at_4MHz (release : Nat) :
    release ≤ tolerance .standard * 250 ↔ release ≤ 7000 := by
  rw [standard_tolerance]

/-- At the 20 ns physical target no profile tolerates more than 5040 ns. -/
theorem at_50MHz (profile : I2cProfile) : tolerance profile * 20 ≤ 5040 := by
  have := tolerance_le profile
  omega

end Pinwheel.Program.StreamingI2CClock
