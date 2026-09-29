import Pinwheel.I2C.WriteTransaction

namespace Pinwheel.I2C.WriteTransaction

def ActiveBound (r : Request) (phase : Phase) : Prop :=
  match phase with
  | .setup slot | .rise slot | .high slot | .fall slot => slot.val < 9 * (r.payloadCount + 1)
  | _ => True

/-- Only ACK observations are writable; every other capture destination is preserved. -/
theorem latch_preserves_unused (samples : Vector Bool 16) (slot : Fin 27) (sda : Bool)
    (index : Fin 16) (h : 3 ≤ index.val) :
    (latch samples slot sda)[index.val] = samples[index.val] := by
  by_cases h8 : slot.val = 8 <;> by_cases h17 : slot.val = 17 <;> by_cases h26 : slot.val = 26 <;>
    simp_all [latch, sampleAt, show 0 ≠ index.val by omega,
      show 1 ≠ index.val by omega, show 2 ≠ index.val by omega]
  done

theorem step_preserves_unused (cfg : Config) (r : Request) (s : State) (bus : Bus)
    (index : Fin 16) (h : 3 ≤ index.val) :
    (step cfg r s bus).samples[index.val] = s.samples[index.val] := by
  cases hp : s.phase <;> simp [step, hp, guarded, timed, blocked, finish, count, move]
  all_goals repeat first | split | simp_all [latch_preserves_unused]
  done

theorem run_unused_false (cfg : Config) (r : Request) (incoming : Nat → Bus) (n : Nat)
    (index : Fin 16) (h : 3 ≤ index.val) :
    (run cfg r (initial cfg) incoming n).samples[index.val] = false := by
  induction n <;> simp_all [run, initial, step_preserves_unused]
  done

theorem afterFall_bound (r : Request) (samples : Vector Bool 16) (slot : Fin 27)
    (h : ActiveBound r (.fall slot)) : ActiveBound r (afterFall r samples slot) := by
  grind [afterFall, ActiveBound, Request.payloadCount]
  done

theorem step_bound (cfg : Config) (r : Request) (s : State) (bus : Bus)
    (h : ActiveBound r s.phase) : ActiveBound r (step cfg r s bus).phase := by
  cases hp : s.phase <;> grind [step, guarded, timed, blocked, count, move, finish,
    ActiveBound, afterFall_bound]
  done

theorem run_bound (cfg : Config) (r : Request) (incoming : Nat → Bus) (n : Nat) :
    ActiveBound r (run cfg r (initial cfg) incoming n).phase := by
  induction n with
  | zero => trivial
  | succ n ih => exact step_bound cfg r _ _ ih
  done

theorem latch_before_third (samples : Vector Bool 16) (slot : Fin 27) (sda : Bool)
    (h : slot.val < 18) : (latch samples slot sda)[2] = samples[2] := by
  by_cases h8 : slot.val = 8 <;> by_cases h17 : slot.val = 17 <;>
    simp_all [latch, sampleAt, show slot.val ≠ 26 by omega]
  done

theorem step_one_byte_preserves_third (cfg : Config) (r : Request) (s : State) (bus : Bus)
    (hc : r.countMinusOne = 0) (h : ActiveBound r s.phase) :
    (step cfg r s bus).samples[2] = s.samples[2] := by
  cases hp : s.phase <;> simp [step, hp, guarded, timed, blocked, finish, count, move]
  all_goals repeat first | split | (solve | simp_all [ActiveBound, Request.payloadCount, latch_before_third])
  done

/-- The third ACK flag is unconsumed and remains false in every one-byte history. -/
theorem run_one_byte_third_false (cfg : Config) (r : Request) (incoming : Nat → Bus) (n : Nat)
    (hc : r.countMinusOne = 0) : (run cfg r (initial cfg) incoming n).samples[2] = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [run, step_one_byte_preserves_third cfg r _ _ hc (run_bound cfg r incoming n)] using ih
  done

/-- Every transmitted data bit is its byte's MSB-first bit; ACK clocks are separate. -/
theorem wire_bit_correct (r : Request) (byte : Fin 3) (bit : Fin 8) :
    releaseData r ⟨9 * byte.val + bit.val, by omega⟩ = (wireByte r byte).getLsbD (7 - bit.val) := by
  simp [releaseData, show (9 * byte.val + bit.val) % 9 = bit.val by omega,
    show (9 * byte.val + bit.val) / 9 = byte.val by omega, show bit.val ≠ 8 by omega]
  done

theorem ack_released (r : Request) (byte : Fin 3) :
    releaseData r ⟨9 * byte.val + 8, by omega⟩ = true := by
  simp [releaseData, show (9 * byte.val + 8) % 9 = 8 by omega]
  done

theorem address_nack_stops (r : Request) (samples : Vector Bool 16) (h : samples[0] = true) :
    afterFall r samples 8 = .stopLow := by simp [afterFall, h, show (8 : Fin 27).val = 8 from rfl]

theorem payload1_nack_stops (r : Request) (samples : Vector Bool 16) (h : samples[1] = true) :
    afterFall r samples 17 = .stopLow := by simp [afterFall, h, show (17 : Fin 27).val = 17 from rfl]

theorem final_ack_stops (r : Request) (samples : Vector Bool 16) :
    afterFall r samples 26 = .stopLow := by simp [afterFall, show (26 : Fin 27).val = 26 from rfl]

theorem address_write_bit (r : Request) : (wireByte r 0).getLsbD 0 = false := by
  change (BitVec.ofNat 8 (r.address.val * 2)).getLsbD 0 = false
  rw [BitVec.getLsbD_ofNat]
  simp
  done

end Pinwheel.I2C.WriteTransaction
