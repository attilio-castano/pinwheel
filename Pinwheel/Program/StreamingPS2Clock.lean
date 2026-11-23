import Pinwheel.Timing.Sampling
import Pinwheel.Program.StreamingPS2Spec

/-! # Clock contract for the PS/2 keyboard receive image

`StreamingPS2Spec.PeerFrame` describes a device-to-host frame in core clock
samples: each clock half-period lasts 120 through 200 samples, the clock stays
released for 221 samples after the last fall, and each bit is read at the
sample where its fall is first seen. This module states which real-time
device waveforms produce it, at which core clock.

`Line` describes the frame in real time, with half-periods between `minHalf`
and `maxHalf` time units. `peerFrame` builds the cycle-level `PeerFrame`
whenever those bounds lie within 120 and 200 core periods. Sampling rounds both
edges of a half-period the same way, so no extra margin is needed.

The PS/2 standard allows half-periods of 30 through 50 µs. That range fits
120–200 samples at exactly one core clock: `spec_admits_iff` shows it is
4 MHz. A faster core sees a 50 µs half-period as more than 200 samples; a
slower one sees 30 µs as fewer than 120. A device known to use a narrower range
is admitted over a band of clocks (`Admits`), but never at the 20 ns physical
target (`spec_not_admits_50MHz`). -/
namespace Pinwheel.Program.StreamingPS2Clock
open Pinwheel.Timing Pinwheel.Program.StreamingPS2

/-- One device-to-host frame in real time. `fallAt i` and `riseAt i` are the
clock edges of bit `i`; the device holds data bit `i` from its fall for `hold`
units, and keeps the clock released until `quiet` units after the last fall. -/
structure Line (minHalf maxHalf hold quiet : Nat) (clock data : Nat → Bool) (bits : List Bool) where
  fallAt : Nat → Nat
  riseAt : Nat → Nat
  count : bits.length = 11
  idle : ∀ x < fallAt 0, clock x = true
  low : ∀ i ≤ 10, ∀ x, fallAt i ≤ x → x < riseAt i → clock x = false
  high : ∀ i < 10, ∀ x, riseAt i ≤ x → x < fallAt (i + 1) → clock x = true
  released : ∀ x, riseAt 10 ≤ x → x < fallAt 10 + quiet → clock x = true
  lowTime : ∀ i ≤ 10, fallAt i + minHalf ≤ riseAt i ∧ riseAt i ≤ fallAt i + maxHalf
  highTime : ∀ i < 10, riseAt i + minHalf ≤ fallAt (i + 1) ∧ fallAt (i + 1) ≤ riseAt i + maxHalf
  valid : ∀ i ≤ 10, ∀ x, fallAt i ≤ x → x < fallAt i + hold → data x = bits[i]?.getD true

/-- Raw input 0 carries the clock and raw input 1 the data. -/
def sample (clock data : Bool) : BitVec 2 :=
  (if data then 2#2 else 0#2) ||| (if clock then 1#2 else 0#2)

def samples (period count : Nat) (clock data : Nat → Bool) : List (BitVec 2) :=
  (List.range count).map fun t => sample (clock (t * period)) (data (t * period))

theorem sample_clock : ∀ c d : Bool, (sample c d)[0] = c := by decide

theorem sample_data : ∀ c d : Bool, (sample c d)[1] = d := by decide

theorem clockAt_samples (period count t : Nat) (clock data : Nat → Bool) (inside : t < count) :
    clockAt (samples period count clock data) t = clock (t * period) := by
  simp only [clockAt, samples, List.getElem?_map, List.getElem?_range inside, Option.map_some,
    Option.getD_some]
  exact sample_clock _ _

theorem dataAt_samples (period count t : Nat) (clock data : Nat → Bool) (inside : t < count) :
    dataAt (samples period count clock data) t = data (t * period) := by
  simp only [dataAt, samples, List.getElem?_map, List.getElem?_range inside, Option.map_some,
    Option.getD_some]
  exact sample_data _ _

section
variable {minHalf maxHalf hold quiet : Nat} {clock data : Nat → Bool} {bits : List Bool}
  (period : Nat) (line : Line minHalf maxHalf hold quiet clock data bits)

/-- Sample index at which fall `i` is first seen. -/
def fallSample (i : Nat) : Nat := firstSample period (line.fallAt i)

/-- Sample index at which rise `i` is first seen. -/
def riseSample (i : Nat) : Nat := firstSample period (line.riseAt i)

/-- The falls after fall `i`, as sample indices. -/
def laterFalls (i : Nat) : List Nat := (List.range (10 - i)).map fun j => fallSample period line (i + 1 + j)

/-- The samples the receive program reads: through 221 samples after the last fall. -/
def raw : List (BitVec 2) := samples period (fallSample period line 10 + 221) clock data

end

/-- The conditions on the core clock period, in the time unit of `Line`. -/
structure Fits (period minHalf maxHalf hold quiet start : Nat) : Prop where
  positive : 0 < period
  fast : 120 * period ≤ minHalf
  slow : maxHalf ≤ 200 * period
  holds : period ≤ hold
  quiet : 221 * period ≤ quiet
  start : 2 * period < start

section
variable {period minHalf maxHalf hold quiet : Nat} {clock data : Nat → Bool} {bits : List Bool}
  {line : Line minHalf maxHalf hold quiet clock data bits}
  (fits : Fits period minHalf maxHalf hold quiet (line.fallAt 0))
include fits

private theorem at_or_after (x t : Nat) : firstSample period x ≤ t ↔ x ≤ t * period := by
  have := lt_firstSample_iff period x t fits.positive
  omega

private theorem before (x t : Nat) : t < firstSample period x ↔ t * period < x :=
  lt_firstSample_iff period x t fits.positive

theorem low_gap (i : Nat) (inside : i ≤ 10) :
    fallSample period line i + 120 ≤ riseSample period line i ∧
      riseSample period line i ≤ fallSample period line i + 200 :=
  firstSample_gap period 120 200 _ _ fits.positive
    (by have := (line.lowTime i inside).1; have := fits.fast; omega)
    (by have := (line.lowTime i inside).2; have := fits.slow; omega)

theorem high_gap (i : Nat) (inside : i < 10) :
    riseSample period line i + 120 ≤ fallSample period line (i + 1) ∧
      fallSample period line (i + 1) ≤ riseSample period line i + 200 :=
  firstSample_gap period 120 200 _ _ fits.positive
    (by have := (line.highTime i inside).1; have := fits.fast; omega)
    (by have := (line.highTime i inside).2; have := fits.slow; omega)

theorem fall_le_last : ∀ n i, i + n = 10 → fallSample period line i ≤ fallSample period line 10
  | 0, i, h => by
    obtain rfl : i = 10 := by omega
    exact Nat.le_refl _
  | n + 1, i, h => by
    have := fall_le_last n (i + 1) (by omega)
    have := low_gap fits i (by omega)
    have := high_gap fits i (by omega)
    omega

omit fits in
theorem laterFalls_succ (i : Nat) (inside : i < 10) :
    laterFalls period line i = fallSample period line (i + 1) :: laterFalls period line (i + 1) := by
  unfold laterFalls
  rw [show 10 - i = (10 - (i + 1)) + 1 by omega, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  congr 1
  omega

private theorem clock_low (i : Nat) (inside : i ≤ 10) (k : Nat)
    (after : fallSample period line i ≤ k) (stop : k < riseSample period line i) :
    clockAt (raw period line) k = false := by
  have gap := low_gap fits i inside
  have last := fall_le_last fits (10 - i) i (by omega)
  rw [raw, clockAt_samples _ _ _ _ _ (by omega)]
  exact line.low i inside _ ((at_or_after fits _ _).mp after) ((before fits _ _).mp stop)

theorem clocking : ∀ n i, i + n = 10 →
    Clocking (raw period line) (fallSample period line i) (laterFalls period line i)
  | 0, i, h => by
    obtain rfl : i = 10 := by omega
    have gap := low_gap fits 10 (by omega)
    have spec : line.fallAt 10 ≤ fallSample period line 10 * period ∧
        fallSample period line 10 * period < line.fallAt 10 + period :=
      firstSample_spec period _ fits.positive
    have nil : laterFalls period line 10 = [] := rfl
    rw [nil]
    refine .last (rise := riseSample period line 10) gap.1 gap.2 (clock_low fits 10 (by omega)) ?_ ?_
    · intro k after inside
      rw [raw, samples, List.length_map, List.length_range] at inside
      rw [raw, clockAt_samples _ _ _ _ _ inside]
      apply line.released _ ((at_or_after fits _ _).mp after)
      have : k * period ≤ (fallSample period line 10 + 220) * period :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [Nat.add_mul] at this
      have := fits.quiet
      omega
    · simp [raw, samples]
  | n + 1, i, h => by
    rw [laterFalls_succ i (by omega)]
    have low := low_gap fits i (by omega)
    have high := high_gap fits i (by omega)
    have last := fall_le_last fits (10 - (i + 1)) (i + 1) (by omega)
    refine .next (rise := riseSample period line i) low.1 low.2 high.1 high.2
      (clock_low fits i (by omega)) ?_ (clocking n (i + 1) (by omega))
    intro k after stop
    rw [raw, clockAt_samples _ _ _ _ _ (by omega)]
    exact line.high i (by omega) _ ((at_or_after fits _ _).mp after) ((before fits _ _).mp stop)

omit fits in
theorem falls_eq : fallSample period line 0 :: laterFalls period line 0 =
    (List.range 11).map (fallSample period line) := by
  apply List.ext_getElem
  · simp [laterFalls]
  · intro k _ _
    cases k with
    | zero => simp
    | succ j =>
      simp only [laterFalls, List.getElem_cons_succ, List.getElem_map, List.getElem_range]
      congr 1
      omega

/-- A real-time frame whose half-periods lie within 120 and 200 core periods,
sampled by that core clock, satisfies the cycle-level PS/2 peer contract with
exactly the device's bits as symbols. -/
def peerFrame : PeerFrame (raw period line) bits where
  firstFall := fallSample period line 0
  laterFalls := laterFalls period line 0
  laterCount := by simp [laterFalls]
  start := by
    have := (before fits (line.fallAt 0) 2).mpr fits.start
    simp only [fallSample]
    omega
  idle k early := by
    have last := fall_le_last fits 10 0 rfl
    rw [raw, clockAt_samples _ _ _ _ _ (by simp only [fallSample] at early last ⊢; omega)]
    exact line.idle _ ((before fits _ _).mp early)
  clocking := clocking fits 10 0 rfl
  data := by
    rw [falls_eq, List.map_map]
    apply List.ext_getElem
    · simp [line.count]
    · intro i inside _
      have bound : i < 11 := by simpa using inside
      have last := fall_le_last fits (10 - i) i (by omega)
      have spec : line.fallAt i ≤ fallSample period line i * period ∧
          fallSample period line i * period < line.fallAt i + period :=
        firstSample_spec period _ fits.positive
      simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
      rw [raw, dataAt_samples _ _ _ _ _ (by omega)]
      rw [line.valid i (by omega) _ spec.1 (by have := fits.holds; omega)]
      simp [List.getElem?_eq_getElem (show i < bits.length by rw [line.count]; exact bound)]

end

/-! ## Physical units -/

/-- A core clock of `hz` admits a device whose half-periods lie between
`minHalf` and `maxHalf`, where `unitsPerSecond` time units make a second. -/
def Admits (hz unitsPerSecond minHalf maxHalf : Nat) : Prop :=
  120 * unitsPerSecond ≤ hz * minHalf ∧ hz * maxHalf ≤ 200 * unitsPerSecond

/-- The PS/2 standard's 30–50 µs half-periods, in nanoseconds. -/
def SpecAdmits (hz : Nat) : Prop := Admits hz 1000000000 30000 50000

instance : DecidablePred SpecAdmits := fun hz =>
  inferInstanceAs (Decidable (120 * 1000000000 ≤ hz * 30000 ∧ hz * 50000 ≤ 200 * 1000000000))

/-- The full PS/2 range is admitted at exactly one core clock. -/
theorem spec_admits_iff (hz : Nat) : SpecAdmits hz ↔ hz = 4000000 := by
  simp only [SpecAdmits, Admits]
  omega

theorem spec_not_admits_50MHz : ¬ SpecAdmits 50000000 := by decide

/-- The core clock the demo is built for. -/
def coreHz : Nat := 4000000

/-- In physical units: with the core clock period dividing a second exactly,
an admitted clock gives the period conditions `peerFrame` needs. -/
theorem fits_of_admits (hz period unitsPerSecond minHalf maxHalf hold quiet start : Nat)
    (positive : 0 < hz) (unit : 0 < unitsPerSecond) (clock : hz * period = unitsPerSecond)
    (admits : Admits hz unitsPerSecond minHalf maxHalf)
    (holds : unitsPerSecond ≤ hz * hold) (quietLong : 221 * unitsPerSecond ≤ hz * quiet)
    (late : 2 * unitsPerSecond < hz * start) :
    Fits period minHalf maxHalf hold quiet start := by
  have scale (a : Nat) : a * unitsPerSecond = hz * (a * period) := by
    rw [← clock, Nat.mul_left_comm]
  have cancel {a b : Nat} (h : hz * a ≤ hz * b) : a ≤ b := Nat.le_of_mul_le_mul_left h positive
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    intro zero
    rw [zero, Nat.mul_zero] at clock
    omega
  · exact cancel (by rw [← scale 120]; exact admits.1)
  · exact cancel (by rw [← scale 200]; exact admits.2)
  · exact cancel (by rw [← clock] at holds; exact holds)
  · exact cancel (by rw [← scale 221]; exact quietLong)
  · exact Nat.lt_of_mul_lt_mul_left (a := hz) (by rw [← scale 2]; exact late)

/-- The demo in nanoseconds: at 4 MHz the core samples every 250 ns. A
standard PS/2 frame (half-periods 30–50 µs), with data held at least 250 ns
past each fall, the clock released for 55.25 µs after the last fall, and the
frame starting after the window's third sample, is captured exactly. -/
def peerFrame_at_4MHz (hold quiet : Nat) (clock data : Nat → Bool) (bits : List Bool)
    (line : Line 30000 50000 hold quiet clock data bits)
    (holds : 250 ≤ hold) (quietLong : 55250 ≤ quiet) (late : 500 < line.fallAt 0) :
    PeerFrame (raw 250 line) bits :=
  peerFrame (fits_of_admits 4000000 250 1000000000 30000 50000 hold quiet (line.fallAt 0)
    (by decide) (by decide) (by decide) ((spec_admits_iff _).mpr rfl) (by omega) (by omega) (by omega))

/-- The hypotheses are satisfiable: a frame with 40 µs half-periods (time unit
one core period, so 160 samples) of all-one bits. -/
def steadyLine : Line 120 200 1 221 (fun x => decide (x < 3 ∨ 160 ≤ (x - 3) % 320 ∨ 3363 ≤ x))
    (fun _ => true) (List.replicate 11 true) where
  fallAt i := 3 + 320 * i
  riseAt i := 3 + 320 * i + 160
  count := by simp
  idle x early := by simp only [decide_eq_true_eq]; omega
  low i _ x lo hi := by simp only [decide_eq_false_iff_not]; omega
  high i _ x lo hi := by simp only [decide_eq_true_eq]; omega
  released x lo _ := by simp only [decide_eq_true_eq]; omega
  lowTime i _ := by omega
  highTime i _ := by omega
  valid i _ _ _ _ := by rw [List.getElem?_replicate]; split <;> rfl

def steadyFrame : PeerFrame (raw 1 steadyLine) (List.replicate 11 true) :=
  peerFrame ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end Pinwheel.Program.StreamingPS2Clock
