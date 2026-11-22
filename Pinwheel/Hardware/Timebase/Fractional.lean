import Std

/-! A rational timebase with one synchronous enable per elapsed beat.
An uninterrupted run starts with phase zero. The beat period is numerator /
denominator core clocks, with at most one beat on each core edge. -/
namespace Pinwheel.Hardware.Timebase

structure Period where
  numerator : Nat
  denominator : Nat
  positive : 0 < denominator
  atMostOne : denominator ≤ numerator

def beat (p : Period) (phase : Nat) : Bool :=
  decide (p.numerator ≤ phase + p.denominator)

def advance (p : Period) (phase : Nat) : Nat :=
  if beat p phase then phase + p.denominator - p.numerator else phase + p.denominator

structure State where
  phase : Nat
  beats : Nat

def run (p : Period) : Nat → State
  | 0 => ⟨0, 0⟩
  | n + 1 =>
    let previous := run p n
    ⟨advance p previous.phase, previous.beats + (beat p previous.phase).toNat⟩

/-- The accumulator holds the exact remainder of the ideal elapsed phase. -/
theorem run_conserves (p : Period) (n : Nat) :
    (run p n).phase < p.numerator ∧
      (run p n).phase + p.numerator * (run p n).beats = n * p.denominator := by
  induction n with
  | zero => simp [run, Nat.lt_of_lt_of_le p.positive p.atMostOne]
  | succ n ih =>
    have bound := p.atMostOne
    by_cases fire : p.numerator ≤ (run p n).phase + p.denominator <;>
      simp [run, advance, beat, fire, Nat.mul_add, Nat.succ_mul] <;> omega

theorem run_beats (p : Period) (n : Nat) :
    (run p n).beats = n * p.denominator / p.numerator := by
  symm
  exact Nat.div_eq_of_lt_le
    (by rw [Nat.mul_comm]; have := run_conserves p n; omega)
    (by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (run p n).beats]; have := run_conserves p n; omega)

/-- Beat k first occurs at the smallest edge n with k * numerator ≤ n * denominator.
This is the ceiling of the ideal deadline in core clocks. -/
theorem beat_deadline (p : Period) (n k : Nat) :
    k ≤ (run p n).beats ↔ k * p.numerator ≤ n * p.denominator := by
  rw [run_beats]
  exact Nat.le_div_iff_mul_le (Nat.lt_of_lt_of_le p.positive p.atMostOne)

theorem phase_after_beat (p : Period) (n : Nat) (fire : beat p (run p n).phase = true) :
    (run p (n + 1)).phase < p.denominator := by
  have phase := (run_conserves p n).1
  have crossed : p.numerator ≤ (run p n).phase + p.denominator := of_decide_eq_true fire
  simp [run, advance, fire]
  omega

/-- Each observed beat is less than one core clock after its ideal deadline.
The inequality is scaled by the denominator to keep all arithmetic exact. -/
theorem beat_phase_error (p : Period) (n : Nat) (fire : beat p (run p n).phase = true) :
    let k := (run p (n + 1)).beats
    p.numerator * k ≤ (n + 1) * p.denominator ∧
      (n + 1) * p.denominator < p.numerator * k + p.denominator := by
  have remainder := phase_after_beat p n fire
  have conservation := (run_conserves p (n + 1)).2
  exact ⟨by omega, by omega⟩

/-- Consecutive beats (or reset and the first beat) are separated by the
floor or ceiling of the period. Post-beat phases are bounded by `phase_after_beat`. -/
theorem beat_spacing (p : Period) (i j : Nat) (ordered : i ≤ j)
    (first : (run p i).phase < p.denominator) (last : (run p j).phase < p.denominator)
    (successive : (run p j).beats = (run p i).beats + 1) :
    p.numerator / p.denominator ≤ j - i ∧
      j - i ≤ (p.numerator + p.denominator - 1) / p.denominator := by
  have startTime := (run_conserves p i).2
  have endTime := (run_conserves p j).2
  rw [successive, Nat.mul_add, Nat.mul_one] at endTime
  have delta : (j - i) * p.denominator + (run p i).phase =
      p.numerator + (run p j).phase := by
    have elapsed := Nat.mul_le_mul_right p.denominator ordered
    rw [Nat.sub_mul]
    omega
  constructor
  · by_cases enough : p.numerator / p.denominator ≤ j - i
    · exact enough
    have lead := Nat.mul_le_mul_right p.denominator (show j - i + 1 ≤ p.numerator / p.denominator by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (p.numerator / p.denominator)] at lead
    have quotient := Nat.div_add_mod p.numerator p.denominator
    omega
  · exact (Nat.le_div_iff_mul_le p.positive).2 (by omega)

end Pinwheel.Hardware.Timebase
