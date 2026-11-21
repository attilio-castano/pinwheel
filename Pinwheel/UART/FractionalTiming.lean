import Pinwheel.Hardware.Timebase.Fractional

/-! Sample windows for an 8N1 receiver with a rational half-bit timebase.
Time is scaled in units of one denominator-th of a core clock. The line
contract measures START and symbol boundaries at the receiver's sampled input.
A constant transport latency translates those boundaries together. -/
namespace Pinwheel.UART.FractionalTiming
open Pinwheel.Hardware.Timebase

def center (p : Period) (symbol : Nat) : Nat :=
  (2 * symbol + 1) * p.numerator

def sampleEdge (p : Period) (symbol : Nat) : Nat :=
  (center p symbol - 1) / p.denominator + 1

/-- The digital center is rounded up by strictly less than one core clock. -/
theorem sampleEdge_bounds (p : Period) (symbol : Nat) :
    center p symbol ≤ p.denominator * sampleEdge p symbol ∧
      p.denominator * sampleEdge p symbol < center p symbol + p.denominator := by
  have positive : 0 < center p symbol :=
    Nat.mul_pos (by omega) (Nat.lt_of_lt_of_le p.positive p.atMostOne)
  have div := Nat.div_add_mod (center p symbol - 1) p.denominator
  have mod := Nat.mod_lt (center p symbol - 1) p.positive
  simp only [sampleEdge, Nat.mul_add, Nat.mul_one]
  omega

/-- The physical half-beat that advances the counter from `2 * symbol`
samples at that symbol's rounded center. -/
theorem sample_at_beat (p : Period) (n symbol : Nat)
    (count : (run p n).beats = 2 * symbol)
    (event : beat p (run p n).phase = true) :
    n + 1 = sampleEdge p symbol := by
  have error := beat_phase_error p n event
  have bounds := sampleEdge_bounds p symbol
  simp only [run, count, event, Bool.toNat_true] at error
  rw [center, Nat.mul_comm (2 * symbol + 1)] at bounds
  rw [Nat.mul_comm (n + 1)] at error
  have scaled : p.denominator * (n + 1) = p.denominator * sampleEdge p symbol := by
    rcases Nat.lt_trichotomy (n + 1) (sampleEdge p symbol) with h | h | h
    · have gap := Nat.mul_le_mul_left p.denominator (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at gap
      omega
    · rw [h]
    · have gap := Nat.mul_le_mul_left p.denominator (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at gap
      omega
  exact Nat.eq_of_mul_eq_mul_left p.positive scaled

theorem reaches_center (p : Period) (n symbol : Nat) :
    2 * symbol + 1 ≤ (run p n).beats ↔ sampleEdge p symbol ≤ n := by
  have before : n < sampleEdge p symbol ↔ n * p.denominator ≤ center p symbol - 1 := by
    change n < Nat.succ ((center p symbol - 1) / p.denominator) ↔ _
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le p.positive]
  rw [beat_deadline]
  have positive : 0 < center p symbol :=
    Nat.mul_pos (by omega) (Nat.lt_of_lt_of_le p.positive p.atMostOne)
  unfold center at *
  omega

/-- Every center is reached on exactly its designated half-beat. -/
theorem at_center (p : Period) (n symbol : Nat) (edge : n + 1 = sampleEdge p symbol) :
    (run p n).beats = 2 * symbol ∧ beat p (run p n).phase = true := by
  have before : ¬2 * symbol + 1 ≤ (run p n).beats := by
    rw [reaches_center, ← edge]
    omega
  have atEdge : 2 * symbol + 1 ≤ (run p (n + 1)).beats :=
    (reaches_center p (n + 1) symbol).2 (by omega)
  cases fire : beat p (run p n).phase <;> simp [run, fire] at atEdge ⊢ <;> omega

/-- Affine timing margins are checked at the START and STOP centers. Between
them the sample error changes linearly with the symbol index. Detection may
lag the sampled frame start by as much as `late` scaled units. -/
def Safe (p : Period) (senderBit late : Nat) : Prop :=
  9 * senderBit ≤ center p 9 ∧
  center p 0 + late + p.denominator ≤ senderBit ∧
  center p 9 + late + p.denominator ≤ 10 * senderBit

theorem sample_window (p : Period) (senderBit late delay : Nat) (safe : Safe p senderBit late)
    (detection : delay ≤ late) (symbol : Fin 10) :
    symbol.val * senderBit ≤ delay + p.denominator * sampleEdge p symbol.val ∧
      delay + p.denominator * sampleEdge p symbol.val < (symbol.val + 1) * senderBit := by
  have aperture := sampleEdge_bounds p symbol.val
  have cases : symbol.val = 0 ∨ symbol.val = 1 ∨ symbol.val = 2 ∨ symbol.val = 3 ∨
      symbol.val = 4 ∨ symbol.val = 5 ∨ symbol.val = 6 ∨ symbol.val = 7 ∨
      symbol.val = 8 ∨ symbol.val = 9 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h
  all_goals simp only [Safe, center, h, Nat.add_mul, Nat.one_mul] at safe aperture ⊢
  all_goals omega
  done

/-- At 7.5 receiver clocks per bit, the transmitter may use periods between
118/16 and 126/16 clocks, for every fractional START phase admitted by the
digital sampled-line model (detection lag up to 15/16 of a clock). -/
def nominal : Period := ⟨60, 16, by decide, by decide⟩

theorem nominal_safe (senderBit : Nat) (lo : 118 ≤ senderBit) (hi : senderBit ≤ 126) :
    Safe nominal senderBit 15 := by
  change 9 * senderBit ≤ 1140 ∧ 91 ≤ senderBit ∧ 1171 ≤ 10 * senderBit
  omega

end Pinwheel.UART.FractionalTiming
