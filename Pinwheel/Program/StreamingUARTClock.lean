import Pinwheel.Timing.Sampling
import Pinwheel.Program.StreamingUARTFrameResults

/-! # Clock contract for UART receive

The UART receive image counts in core clocks. `good_frame_result` needs four
samples, indexed from the first sample that sees the start bit low: sample 0
and sample `2Q` low, data bit `j` at sample `(6 + 4j) Q`, and the stop bit high
at sample `38 Q`, where `Q` is the profile's quarter-bit count.

This module describes the line in real time with any bit time `T`, so the
transmitter's baud need not match `4 Q` core periods exactly. `received` shows
the frame is received whenever each of those sample instants, which sampling
places up to one period `P` after its nominal time, stays inside its bit
(`Fits`).

In units of `1 / (hz · baud)` seconds, `P = baud` and `T = hz`, so `FitsAt Q hz
baud` decides a concrete board. The window is about −5 % to +5.5 % of bit time
around `4 Q` core periods. Because `Q` is at most 128, a core clock sets a
lowest usable baud near `hz / 512`: 9600 baud works at 4 MHz but not at the
20 ns target (`at_4MHz`, `at_50MHz`). -/
namespace Pinwheel.Program.StreamingUARTClock
open Pinwheel.Timing Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingUART
open Pinwheel.Program.StreamingUART.Frame Pinwheel.Program.StreamingUART.QuietTiming

/-- One 8N1 frame in real time: idle until `fall`, then start, eight data bits
least-significant first, and stop, each lasting `bitTime` units. -/
structure Line (bitTime : Nat) (level : Nat → Bool) (payload : BitVec 8) where
  fall : Nat
  start : ∀ x, fall ≤ x → x < fall + bitTime → level x = false
  data : ∀ (j : Nat) (within : j < 8) x, fall + (j + 1) * bitTime ≤ x → x < fall + (j + 2) * bitTime →
    level x = payload[j]'within
  stop : ∀ x, fall + 9 * bitTime ≤ x → x < fall + 10 * bitTime → level x = true

/-- Every sample instant the receiver uses, up to one period late, lies in its bit. -/
def Fits (Q period bitTime : Nat) : Prop :=
  (2 * Q + 1) * period ≤ bitTime ∧
  (∀ j : Fin 8, (j.val + 1) * bitTime ≤ (6 + 4 * j.val) * Q * period ∧
    (6 + 4 * j.val) * Q * period + period ≤ (j.val + 2) * bitTime) ∧
  9 * bitTime ≤ 38 * Q * period ∧ 38 * Q * period + period ≤ 10 * bitTime

instance (Q period bitTime : Nat) : Decidable (Fits Q period bitTime) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- `Fits` for a core clock of `hz` and a transmitter at `baud`. -/
def FitsAt (Q hz baud : Nat) : Prop := Fits Q baud hz

instance (Q hz baud : Nat) : Decidable (FitsAt Q hz baud) :=
  inferInstanceAs (Decidable (Fits Q baud hz))

section
variable {bitTime : Nat} {level : Nat → Bool} {payload : BitVec 8}

/-- The board inputs read the line at every core clock. -/
def Wired (p : Profile) (period : Nat) (level : Nat → Bool) (input : Nat → Input) : Prop :=
  ∀ m, (input m).rawInputs[p.rxInput.val] = level (m * period)

/-- Receiver inputs indexed from the first sample at or after the start edge. -/
def incoming (period : Nat) (line : Line bitTime level payload) (input : Nat → Input) (n : Nat) : Input :=
  input (firstSample period line.fall + n)

private theorem sample_time (period fall n : Nat) (positive : 0 < period) :
    fall + n * period ≤ (firstSample period fall + n) * period ∧
      (firstSample period fall + n) * period < fall + n * period + period := by
  have spec := firstSample_spec period fall positive
  simp only [Nat.add_mul]
  omega

theorem received {a : Nat} (p : Profile) (generation transfer : BitVec 16) (period : Nat) (positive : 0 < period)
    (line : Line bitTime level payload) (fits : Fits p.Q period bitTime) (input : Nat → Input)
    (wired : Wired p period level input) (quiet : ∀ n, Quiet (input n)) :
    let finalState := run (image p).program (Arm.armed (a := a) p generation transfer)
      (FrameSamples.clocks (incoming period line input) 0 (38 * p.Q + 4))
    finalState.phase = .completed ∧ Received generation transfer payload finalState := by
  obtain ⟨startFits, dataFits, stopLate, stopEarly⟩ := fits
  have at_sample (n : Nat) : (input (firstSample period line.fall + n)).rawInputs[p.rxInput.val] =
      level ((firstSample period line.fall + n) * period) := wired _
  apply good_frame_result p generation transfer payload _ (fun n => quiet _)
  · rw [at_sample]
    have t := sample_time period line.fall 0 positive
    apply line.start <;> omega
  · rw [at_sample]
    have t := sample_time period line.fall (2 * p.Q) positive
    apply line.start
    · omega
    · have : 2 * p.Q * period + period = (2 * p.Q + 1) * period := by simp only [Nat.add_mul, Nat.one_mul]
      omega
  · intro j within
    dsimp only
    rw [at_sample]
    have t := sample_time period line.fall ((6 + 4 * j) * p.Q) positive
    have f := dataFits ⟨j, within⟩
    simp only [Nat.mul_assoc] at f t
    apply line.data j within <;> omega
  · rw [at_sample]
    have t := sample_time period line.fall (38 * p.Q) positive
    simp only [Nat.mul_assoc] at stopLate stopEarly t
    apply line.stop <;> omega

end

/-! ## Boards -/

/-- 115200 baud at 4 MHz needs `Q = 9`; neighbouring quarters miss. -/
theorem at_4MHz :
    FitsAt 9 4000000 115200 ∧ ¬ FitsAt 8 4000000 115200 ∧ ¬ FitsAt 10 4000000 115200 ∧
      FitsAt 104 4000000 9600 := by
  decide

/-- At 50 MHz, 115200 baud works with `Q = 108`, but 9600 baud needs more
than the largest quarter count (128). -/
theorem at_50MHz : FitsAt 108 50000000 115200 ∧ ¬ FitsAt 128 50000000 9600 := by
  decide

/-- No quarter count up to the profile limit fits 9600 baud at 50 MHz. -/
theorem no_9600_at_50MHz : ∀ Q : Fin 125, ¬ FitsAt (Q.val + 4) 50000000 9600 := by
  decide

end Pinwheel.Program.StreamingUARTClock
