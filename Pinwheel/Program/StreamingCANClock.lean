import Pinwheel.Timing.Sampling
import Pinwheel.Program.StreamingCANPeer

/-! # Clock contract for the passive CAN receive image

`StreamingCANCore` proves the receive image in core clock cycles: a peer whose
symbol boundaries stay within four samples of a 32-sample grid is captured
exactly (`PeerFrame.samples`). Those numbers only mean "125 kbit/s with 1 µs
of slack" at one core clock. This module states that clock explicitly.

The bus is described in real time (`LineFrame`): a line level at every instant
and 65 boundaries within `slack` of the nominal bit grid. Time is a natural
number in any unit; `unitsPerSecond` fixes the unit. The core clock samples
the line every `period` units, where `hz * period = unitsPerSecond`.

`captured` concludes the cycle-level `PeerFrame`, so every existing package
theorem that assumes a `PeerFrame` (for example `CANSession.completed_frame_from`)
now follows from a real-time bus description plus the clock contract `Admits`. -/
namespace Pinwheel.Program.StreamingCANClock
open Pinwheel.Timing Pinwheel.Program.StreamingCANCore

/-- The receive image takes one sample per core clock and expects this many per bit. -/
def cyclesPerBit : Nat := 32

/-- `PeerFrame` tolerates this much boundary skew, in samples. -/
def skewSamples : Nat := 4

/-- The bit rate the demo is built for. -/
def bitRate : Nat := 125000

/-- The only core clock at which the compiled image receives `bitRate`:
its cycle counts are fixed, so the clock must supply exactly `cyclesPerBit`
samples per bit. -/
def Admits (hz : Nat) : Prop := hz = cyclesPerBit * bitRate

instance : DecidablePred Admits := fun hz => inferInstanceAs (Decidable (hz = cyclesPerBit * bitRate))

def coreHz : Nat := cyclesPerBit * bitRate

theorem coreHz_eq : coreHz = 4000000 := rfl

theorem admits_iff (hz : Nat) : Admits hz ↔ hz = 4000000 := Iff.rfl

/-- One CAN observation window on the bus, in real time. `bitUnits` is the
nominal bit time and `slack` bounds how far each actual boundary may sit from
its nominal position, measured from the start-of-frame edge. -/
structure LineFrame (bitUnits slack : Nat) (level : Nat → Bool) (slots : List Bool) where
  boundary : Nat → Nat
  count : slots.length = 64
  idle : ∀ x < boundary 0, level x = true
  bits : ∀ k < 64, ∀ x, boundary k ≤ x → x < boundary (k + 1) → level x = slots[k]?.getD true
  skew : ∀ k ≤ 64, boundary 0 + k * bitUnits ≤ boundary k + slack ∧
    boundary k ≤ boundary 0 + k * bitUnits + slack

/-- Raw-input samples of the line, sample `t` at time `t * period` on raw input 0. -/
def samples (period : Nat) (level : Nat → Bool) (count : Nat) : List (BitVec 2) :=
  (List.range count).map fun t => if level (t * period) then 1#2 else 0#2

theorem rawBit_samples (period count t : Nat) (level : Nat → Bool) (inside : t < count) :
    rawBit (samples period level count) t = level (t * period) := by
  simp only [rawBit, samples, List.getElem?_map, List.getElem?_range inside, Option.map_some,
    Option.getD_some]
  cases level (t * period) <;> rfl

/-- The sample index at which the core first observes the start of frame. -/
def fall (period : Nat) (line : LineFrame bitUnits slack level slots) : Nat :=
  firstSample period (line.boundary 0)

/-- Sampling a line at exactly `cyclesPerBit` samples per nominal bit, with at
most `skewSamples` periods of slack, yields the cycle-level peer contract. -/
def peerFrame (period : Nat) (positive : 0 < period)
    (within : slack ≤ skewSamples * period)
    (line : LineFrame (cyclesPerBit * period) slack level slots) :
    PeerFrame (samples period level (fall period line + 2053)) slots where
  fall := fall period line
  boundary k := firstSample period (line.boundary k)
  count := line.count
  startAtFall := rfl
  skew k bound := by
    have h := firstSample_skew period cyclesPerBit skewSamples slack (line.boundary 0)
      (line.boundary k) k positive within (line.skew k bound).1 (line.skew k bound).2
    simp only [cyclesPerBit, skewSamples, fall] at h ⊢
    omega
  idle t before := by
    have time := (lt_firstSample_iff period (line.boundary 0) t positive).mp before
    rw [rawBit_samples _ _ _ _ (by simp only [fall] at before ⊢; omega)]
    exact line.idle _ time
  bits k bound t after before := by
    have last := firstSample_skew period cyclesPerBit skewSamples slack (line.boundary 0)
      (line.boundary (k + 1)) (k + 1) positive within (line.skew (k + 1) (by omega)).1
      (line.skew (k + 1) (by omega)).2
    simp only [cyclesPerBit, skewSamples] at last
    have inside : t < fall period line + 2053 := by simp only [fall]; omega
    rw [rawBit_samples _ _ _ _ inside]
    apply line.bits k bound
    · apply Nat.le_of_not_lt
      intro early
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le
        ((lt_firstSample_iff period _ t positive).mpr early) after)
    · exact (lt_firstSample_iff period _ t positive).mp before
  length := by simp [samples]

/-- The clock contract in physical units. If the core clock runs at `hz`, the
bus bit time is `1 / bitRate` seconds, the boundary slack is at most
`skewSamples` core periods, and the clock is admitted, then the sampled line
satisfies the cycle-level contract and every one of the 64 capture apertures
returns the bus symbol. -/
theorem captured (hz period unitsPerSecond bitUnits slack : Nat) (level : Nat → Bool)
    (slots : List Bool) (positive : 0 < hz) (unit : 0 < unitsPerSecond)
    (clock : hz * period = unitsPerSecond) (rate : bitUnits * bitRate = unitsPerSecond)
    (admits : Admits hz) (within : slack * hz ≤ skewSamples * unitsPerSecond)
    (line : LineFrame bitUnits slack level slots) :
    ∃ frame : PeerFrame (samples period level (fall period line + 2053)) slots,
      frame.fall = fall period line ∧
      (apertures frame.fall).map (rawBit (samples period level (fall period line + 2053))) = slots := by
  have periodPositive : 0 < period := by
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero, Nat.mul_zero] at clock
    omega
  have bit : bitUnits = cyclesPerBit * period := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < bitRate by decide)
    rw [rate, ← clock, admits, Nat.mul_right_comm]
  have scaled : slack * hz ≤ skewSamples * period * hz := by
    rw [Nat.mul_assoc, Nat.mul_comm period hz, clock]
    exact within
  have slackBound : slack ≤ skewSamples * period := Nat.le_of_mul_le_mul_right scaled positive
  subst bit
  exact ⟨peerFrame period periodPositive slackBound line, rfl,
    (peerFrame period periodPositive slackBound line).samples⟩

/-- The demo in nanoseconds: at 4 MHz the core samples every 250 ns, a
125 kbit/s bit lasts 8000 ns, and boundaries may sit up to 1000 ns from
nominal. -/
theorem captured_at_4MHz (slack : Nat) (level : Nat → Bool) (slots : List Bool)
    (within : slack ≤ 1000) (line : LineFrame 8000 slack level slots) :
    (apertures (fall 250 line)).map (rawBit (samples 250 level (fall 250 line + 2053))) = slots := by
  obtain ⟨frame, same, result⟩ := captured 4000000 250 1000000000 8000 slack level slots
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp only [skewSamples]; omega) line
  rw [same] at result
  exact result

/-- The fixed image does not receive 125 kbit/s at the 20 ns physical target. -/
theorem not_admits_50MHz : ¬ Admits 50000000 := by decide

/-- The hypotheses are satisfiable: an idle bus with exact bit boundaries is a
line frame, so `captured_at_4MHz` is not vacuous. -/
def idealLine : LineFrame 8000 0 (fun _ => true) (List.replicate 64 true) where
  boundary k := 8000 * k
  count := by simp
  idle _ _ := rfl
  bits _ _ _ _ _ := by rw [List.getElem?_replicate]; split <;> rfl
  skew k _ := by omega

theorem idealLine_captured :
    (apertures (fall 250 idealLine)).map (rawBit (samples 250 (fun _ => true) (fall 250 idealLine + 2053))) =
      List.replicate 64 true :=
  captured_at_4MHz 0 _ _ (by decide) idealLine

end Pinwheel.Program.StreamingCANClock
