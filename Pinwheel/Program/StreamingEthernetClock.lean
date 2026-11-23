import Pinwheel.Program.StreamingEthernetDeadline

/-! # Clock contract for the Ethernet SNI transmit image

The Ethernet proofs assume `PhyClock`: in every six-clock cell, the PHY's
TX_CLK is sampled low, low, high, then high for one more clock or not, then
low. That is a statement about core clock samples. This module states which
real-time TX_CLK waveforms produce it.

`TxClock` describes TX_CLK in real time: for each cell, one rising and one
falling edge, the rise in the sample window ((6k+1)P, (6k+2)P] and the fall in
((6k+2)P, (6k+4)P], where P is the core clock period. `phyClock` proves that
any such waveform, wired to raw input 0, yields `PhyClock`.

Consequences that the cycle-level proofs leave implicit:

* `Admits`: one bit per cell means the core clock must be exactly six times the
  10 MHz SNI clock, 60 MHz. `not_admits_50MHz`: the 20 ns physical target is
  not enough.
* `drift_excluded`: every rise sits in the same window of its cell. A TX_CLK
  whose period differs from six core periods, by any amount, eventually leaves
  that window. The contract therefore needs TX_CLK and the core clock locked
  together, for example one derived from the other.
* `high_lt_three`: TX_CLK must be high for less than three core periods, under
  half its period. `half_duty_excluded`: a locked 50%-duty TX_CLK never fits. -/
namespace Pinwheel.Program.StreamingEthernetClock
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingEthernetCore
open Pinwheel.Program.StreamingEthernetDeadline

/-- Core clocks per transmitted bit (one six-clock cell per PHY clock). -/
def cyclesPerBit : Nat := 6

/-- The SNI bit rate and TX_CLK frequency. -/
def bitRate : Nat := 10000000

def Admits (hz : Nat) : Prop := hz = cyclesPerBit * bitRate

instance : DecidablePred Admits := fun hz => inferInstanceAs (Decidable (hz = cyclesPerBit * bitRate))

def coreHz : Nat := cyclesPerBit * bitRate

theorem coreHz_eq : coreHz = 60000000 := rfl

theorem not_admits_50MHz : ¬ Admits 50000000 := by decide

/-- TX_CLK in real time over `cells` cells, with core clock period `period`.
Within cell `k`'s span the line is high exactly on `[rise k, fall k)`. -/
structure TxClock (period cells : Nat) (level : Nat → Bool) where
  rise : Nat → Nat
  fall : Nat → Nat
  level_eq : ∀ k < cells, ∀ x, 6 * k * period ≤ x → x < (6 * k + 6) * period →
    level x = decide (rise k ≤ x ∧ x < fall k)
  rise_window : ∀ k < cells, (6 * k + 1) * period < rise k ∧ rise k ≤ (6 * k + 2) * period
  fall_window : ∀ k < cells, (6 * k + 2) * period < fall k ∧ fall k ≤ (6 * k + 4) * period

/-- One extra sampled high clock exactly when the fall comes after sample 6k+3. -/
def TxClock.width (clock : TxClock period cells level) (k : Nat) : Fin 2 :=
  if (6 * k + 3) * period < clock.fall k then 1 else 0

private theorem mul_lt_mul_iff (period a b : Nat) (positive : 0 < period) :
    a * period < b * period ↔ a < b :=
  ⟨Nat.lt_of_mul_lt_mul_right, fun h => Nat.mul_lt_mul_of_pos_right h positive⟩

private theorem mul_le_mul_iff (period a b : Nat) (positive : 0 < period) :
    a * period ≤ b * period ↔ a ≤ b :=
  ⟨fun h => Nat.le_of_mul_le_mul_right h positive, fun h => Nat.mul_le_mul_right _ h⟩

/-- Sampling the real-time waveform at every core edge gives `phyLevel`. -/
theorem sampled (period cells : Nat) (positive : 0 < period) (clock : TxClock period cells level)
    (t : Nat) (inside : t < 6 * cells) :
    level (t * period) = phyLevel clock.width t := by
  have cell : t / 6 < cells := by omega
  have start : 6 * (t / 6) * period ≤ t * period := Nat.mul_le_mul_right _ (by omega)
  have finish : t * period < (6 * (t / 6) + 6) * period :=
    (mul_lt_mul_iff period _ _ positive).mpr (by omega)
  rw [clock.level_eq (t / 6) cell _ start finish]
  have r := clock.rise_window (t / 6) cell
  have f := clock.fall_window (t / 6) cell
  unfold phyLevel TxClock.width
  -- Reduce every comparison between multiples of `period` to one on indices.
  have riseLe : clock.rise (t / 6) ≤ t * period ↔ 2 ≤ t % 6 := by
    constructor
    · intro h
      have : (6 * (t / 6) + 1) * period < t * period := Nat.lt_of_lt_of_le r.1 h
      have := (mul_lt_mul_iff period _ _ positive).mp this
      omega
    · intro h
      exact Nat.le_trans r.2 ((mul_le_mul_iff period _ _ positive).mpr (by omega))
  have fallGt : t * period < clock.fall (t / 6) ↔
      t % 6 < 3 + (if (6 * (t / 6) + 3) * period < clock.fall (t / 6) then (1 : Fin 2) else 0).val := by
    split
    · rename_i late
      constructor
      · intro h
        have : t * period < (6 * (t / 6) + 4) * period := Nat.lt_of_lt_of_le h f.2
        have := (mul_lt_mul_iff period _ _ positive).mp this
        show t % 6 < 4
        omega
      · intro h
        show t * period < _
        exact Nat.lt_of_le_of_lt ((mul_le_mul_iff period _ _ positive).mpr (by
          show t ≤ 6 * (t / 6) + 3
          simp only [Fin.val_one] at h
          omega)) late
    · rename_i early
      have early := Nat.le_of_not_lt early
      constructor
      · intro h
        have : t * period < (6 * (t / 6) + 3) * period := Nat.lt_of_lt_of_le h early
        have := (mul_lt_mul_iff period _ _ positive).mp this
        show t % 6 < 3
        omega
      · intro h
        exact Nat.lt_of_le_of_lt ((mul_le_mul_iff period _ _ positive).mpr (by
          show t ≤ 6 * (t / 6) + 2
          simp only [Fin.val_zero] at h
          omega)) f.1
  simp only [riseLe, fallGt]

/-- The board contract: raw input 0 carries TX_CLK, sampled at each core edge. -/
def Wired (period : Nat) (level : Nat → Bool) (cells : List CellInputs) : Prop :=
  ∀ (k : Fin cells.length) (tick : Fin 6),
    (cells[k.val].inputs[tick.val]?.getD {}).rawInputs[0] = level ((6 * k.val + tick.val) * period)

/-- Any real-time TX_CLK within the windows yields the cycle-level `PhyClock`
used by every Ethernet transmit theorem. -/
theorem phyClock (period : Nat) (positive : 0 < period) (cells : List CellInputs)
    (clock : TxClock period cells.length level) (wired : Wired period level cells) :
    PhyClock clock.width cells := by
  intro k tick
  rw [wired k tick]
  exact sampled period cells.length positive clock _ (by omega)

/-- With a locked clock, rise `k` sits `rise 0 + 6 k P`. Any other period —
here `rise k = rise 0 + k * (6 P + drift)` with `drift > 0` — leaves the window
after at most `P` cells. -/
theorem drift_excluded (period drift : Nat) (clock : TxClock period cells level)
    (periodic : ∀ k < cells, clock.rise k = clock.rise 0 + k * (6 * period + drift))
    (slow : 0 < drift) (enough : period < cells) : False := by
  have r0 := clock.rise_window 0 (by omega)
  have rp := clock.rise_window period enough
  rw [periodic period enough] at rp
  have : period * (6 * period + drift) = 6 * period * period + period * drift := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_assoc]
  have grow : period * 1 ≤ period * drift := Nat.mul_le_mul_left _ slow
  simp only [Nat.mul_zero, Nat.zero_add, Nat.add_mul, Nat.one_mul] at r0 rp
  rw [this] at rp
  omega

/-- TX_CLK is high for less than three core periods in every cell. -/
theorem high_lt_three (clock : TxClock period cells level) (k : Nat) (inside : k < cells) :
    clock.fall k < clock.rise k + 3 * period := by
  have r := clock.rise_window k inside
  have f := clock.fall_window k inside
  simp only [Nat.add_mul, Nat.one_mul] at r f
  omega

/-- A locked TX_CLK with 50% duty (high for three core periods) never fits. -/
theorem half_duty_excluded (clock : TxClock period cells level) (k : Nat) (inside : k < cells)
    (half : clock.fall k = clock.rise k + 3 * period) : False := by
  have := high_lt_three clock k inside
  omega

/-- The windows are satisfiable: a locked 60 MHz/10 MHz pair with TX_CLK high
for two core periods, rising just before sample `6k+2`. -/
def lockedClock (cells : Nat) : TxClock 6 cells
    (fun x => decide (6 * (x / 36) * 6 + 11 ≤ x ∧ x < 6 * (x / 36) * 6 + 23)) where
  rise k := 36 * k + 11
  fall k := 36 * k + 23
  level_eq k _ x lo hi := by
    have : x / 36 = k := by omega
    rw [this]
    congr 1
    apply propext
    omega
  rise_window k _ := by omega
  fall_window k _ := by omega

end Pinwheel.Program.StreamingEthernetClock
