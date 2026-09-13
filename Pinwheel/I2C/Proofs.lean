import Pinwheel.I2C.Controller

namespace Pinwheel.I2C

/-- A target holding SCL low prevents entry into the timed high phase. -/
theorem stretch_blocks_high (cfg : Config) (s : State) (sda : Bool) (h : s.phase = .rise) :
    (step cfg s ⟨false, sda⟩).phase ≠ .high := by
  simp [step, h, blocked, finish]
  split <;> simp
  done

theorem released_clock_starts_timer (cfg : Config) (s : State) (sda : Bool) (h : s.phase = .rise) :
    step cfg s ⟨true, sda⟩ = move cfg s .high := by
  simp [step, h]

/-- Every ordinary high-period edge preserves the controller's SDA command. -/
theorem high_holds_data (cfg : Config) (s : State) (sda : Bool) (h : s.phase = .high) :
    (pins (step cfg s ⟨true, sda⟩)).sda = (pins s).sda := by
  simp [step, h, pins, afterHigh, move, count, dataDrive]
  by_cases hz : s.remaining = 0 <;> simp [hz]
  done

/-- The controller releases SDA for both ninth-clock ACK slots. -/
theorem ack_releases_data (s : State) (h : s.slot.val = 8 ∨ s.slot.val = 17)
    (hp : s.phase = .setup ∨ s.phase = .rise ∨ s.phase = .high ∨ s.phase = .fall) :
    (pins s).sda = .release := by
  rcases hp with hp | hp | hp | hp <;> rcases h with h | h <;>
    simp [pins, hp, dataDrive, releaseData, h]

/-- A low SDA is ACK; a high SDA on the address ninth clock takes the NACK path. -/
theorem address_ack_decision (cfg : Config) (s : State) (sda : Bool)
    (hs : s.slot.val = 8) (ho : s.outcome = .success) :
    (afterHigh cfg s sda).outcome = if sda then .addressNack else .success := by
  simp [afterHigh, move, hs, ho]

theorem data_ack_decision (cfg : Config) (s : State) (sda : Bool)
    (hs : s.slot.val = 17) (ho : s.outcome = .success) :
    (afterHigh cfg s sda).outcome = if sda then .dataNack else .success := by
  simp [afterHigh, move, hs, ho]

/-- Both ACK outcomes pass through a clock-low phase before STOP or the next byte. -/
theorem nack_stops (cfg : Config) (s : State) (h : s.outcome ≠ .success) :
    (afterFall cfg s).phase = .stopLow := by
  simp [afterFall, h, move]

/-- Persistent blocking consumes a finite budget, independent of the phase timer. -/
def blockRun (cfg : Config) (s : State) : Nat → State
  | 0 => s
  | n + 1 => blocked cfg (blockRun cfg s n)

theorem blocking_countdown (cfg : Config) (s : State) (n : Nat) (h : n ≤ s.waitLeft.val) :
    (blockRun cfg s n).waitLeft.val = s.waitLeft.val - n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [blockRun, blocked]
    have hn := ih (by omega)
    split <;> simp_all
    all_goals omega
    done

theorem blocking_timeout (cfg : Config) (s : State) :
    (blockRun cfg s (s.waitLeft.val + 1)).phase = .finished ∧
      (blockRun cfg s (s.waitLeft.val + 1)).outcome = .timeout := by
  have h := blocking_countdown cfg s s.waitLeft.val (Nat.le_refl _)
  simp [blockRun, blocked, h, finish]
  done

/-- Both transmitted bytes have the independently specified wire order. -/
theorem wire_order (r : Request) (bit : Fin 8) :
    releaseData r ⟨bit.val, by omega⟩ = (wireBits r)[bit.val] ∧
    releaseData r ⟨bit.val + 9, by omega⟩ = (wireBits r)[bit.val + 8] := by
  have h : bit.val = 0 ∨ bit.val = 1 ∨ bit.val = 2 ∨ bit.val = 3 ∨
      bit.val = 4 ∨ bit.val = 5 ∨ bit.val = 6 ∨ bit.val = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;>
    simp [releaseData, wireBits, h, BitVec.getLsbD_eq_getElem]
  done

/-- No ACK decision or slot change occurs during the configured high-period countdown. -/
theorem high_countdown (cfg : Config) (s : State) (incoming : Nat → Bool) (n : Nat)
    (hp : s.phase = .high) (hn : n ≤ s.remaining.val) :
    run cfg s (fun t => ⟨true, incoming t⟩) n =
      {s with remaining := ⟨s.remaining.val - n, by omega⟩} := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run, ih (by omega)]
    simp [step, hp, show s.remaining.val - n ≠ 0 by omega, count, Nat.sub_sub]
    done

/-- Before timeout, stretching retains slot/outcome and the full high-period budget. -/
theorem stretch_prefix (cfg : Config) (s : State) (incoming : Nat → Bool) (n : Nat)
    (hp : s.phase = .rise) (ht : s.remaining = cfg.phaseMinusOne) (hn : n ≤ s.waitLeft.val) :
    run cfg s (fun t => ⟨false, incoming t⟩) n =
      {s with remaining := cfg.phaseMinusOne, waitLeft := ⟨s.waitLeft.val - n, by omega⟩} := by
  induction n with
  | zero => simp [run, ← ht]
  | succ n ih =>
    rw [run, ih (by omega)]
    simp [step, hp, blocked, show 0 < s.waitLeft.val - n by omega, Nat.sub_sub]
    done

theorem stretch_timeout_exact (cfg : Config) (s : State) (incoming : Nat → Bool)
    (hp : s.phase = .rise) (ht : s.remaining = cfg.phaseMinusOne) :
    result (run cfg s (fun t => ⟨false, incoming t⟩) (s.waitLeft.val + 1)) = some .timeout := by
  rw [run, stretch_prefix cfg s incoming s.waitLeft.val hp ht (Nat.le_refl _)]
  simp [step, hp, blocked, finish, result, busy]
  done

theorem high_boundary (cfg : Config) (s : State) (incoming : Nat → Bool) (hp : s.phase = .high) :
    run cfg s (fun t => ⟨true, incoming t⟩) (s.remaining.val + 1) =
      afterHigh cfg {s with remaining := 0} (incoming (s.remaining.val + 1)) := by
  rw [run, high_countdown cfg s incoming s.remaining.val hp (Nat.le_refl _)]
  simp [step, hp]
  done

theorem reset_releases (cfg : Config) (s : State) (bus : Bus) :
    pins (step cfg s bus true) = ⟨.release, .release⟩ := by
  rfl

theorem finished_holds (cfg : Config) (s : State) (bus : Bus) (h : s.phase = .finished) :
    step cfg s bus = s := by
  simp [step, h]

end Pinwheel.I2C
