import Pinwheel.UART.StreamLinkTiming

namespace Pinwheel.UART.StreamLink
open Link

theorem frame_ticks (t : Timing) : t.tx.frameCycles * t.txTick = 10 * t.txBit := by
  simp [UART.Config.frameCycles, Timing.txBit, Nat.mul_assoc]

theorem offset_after_frame (t : Timing) (time delay : Nat) :
    (time - (t.txStart + delay)) / t.txTick - t.tx.frameCycles =
      (time - (t.txStart + 10 * t.txBit + delay)) / t.txTick := by
  simpa only [Nat.mul_comm t.txTick t.tx.frameCycles, frame_ticks, Nat.sub_sub,
    Nat.add_assoc, Nat.add_comm delay (10 * t.txBit)] using
    (Nat.sub_mul_div (time - (t.txStart + delay)) t.txTick t.tx.frameCycles).symm

/-- The real stream agrees with the one-frame model before any delayed next start. -/
theorem head_prefix (t : Timing) (b : Latency) (byte : BitVec 8) (rest : List (BitVec 8))
    (age : Nat → Nat) (within : b.Contains age) (n : Nat)
    (before : t.edge n < t.txStart + 10 * t.txBit + b.earliest) :
    sampled t (byte :: rest) age n = observe t (UART.expected t.tx byte) age n := by
  by_cases beforeStart : t.edge n < t.txStart + age n
  · simp [sampled, observe, beforeStart]
  · have bounded := within n
    have inside : (t.edge n - (t.txStart + age n)) / t.txTick < t.tx.frameCycles := by
      rw [Nat.div_lt_iff_lt_mul t.txTickPositive, frame_ticks]
      omega
    simp only [sampled, observe, beforeStart, ↓reduceIte, Rx.Stream.wireBody, inside]

/-- After every possible observation has reached stop, replacing that stop suffix with idle
before the next frame preserves the entire remaining observed wire. -/
theorem observed_suffix (t : Timing) (byte : BitVec 8) (rest : List (BitVec 8))
    (age : Nat → Nat) (n : Nat) (afterStop : t.txStart + age n + 9 * t.txBit ≤ t.edge n) :
    sampled t (byte :: rest) age n =
      sampled {t with txStart := t.txStart + 10 * t.txBit} rest age n := by
  have afterStart : t.txStart + age n ≤ t.edge n := by omega
  have stopCycles : 9 * t.tx.cycles ≤ (t.edge n - (t.txStart + age n)) / t.txTick :=
    (Nat.le_div_iff_mul_le t.txTickPositive).2 (by simpa only [Nat.mul_assoc, Timing.txBit] using
      (show 9 * t.txBit ≤ t.edge n - (t.txStart + age n) from by omega))
  have suffix := Rx.Stream.wire_stop_suffix t.tx 0 byte rest
    ((t.edge n - (t.txStart + age n)) / t.txTick) (by simpa only [Nat.zero_add] using stopCycles)
  simp only [Rx.Stream.wire, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, Nat.zero_add] at suffix
  have boundary : ((t.edge n - (t.txStart + age n)) / t.txTick < t.tx.frameCycles) ↔
      t.edge n < t.txStart + 10 * t.txBit + age n := by
    rw [Nat.div_lt_iff_lt_mul t.txTickPositive, frame_ticks]
    omega
  change (if t.edge n < t.txStart + age n then true else
    Rx.Stream.wireBody t.tx (byte :: rest) ((t.edge n - (t.txStart + age n)) / t.txTick)) =
      (if t.edge n < t.txStart + 10 * t.txBit + age n then true else
        Rx.Stream.wireBody t.tx rest ((t.edge n - (t.txStart + 10 * t.txBit + age n)) / t.txTick))
  simpa only [Nat.not_lt_of_ge afterStart, ↓reduceIte, boundary, offset_after_frame] using suffix

end Pinwheel.UART.StreamLink
