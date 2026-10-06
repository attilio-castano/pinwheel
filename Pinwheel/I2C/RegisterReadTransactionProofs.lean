import Pinwheel.I2C.RegisterReadTransaction

namespace Pinwheel.I2C.RegisterReadTransaction

def ActiveBound (r : Request) (phase : Phase) : Prop :=
  match phase with
  | .setup slot | .rise slot | .high slot | .fall slot => slot.val < 9 * (r.byteCount + 3)
  | _ => True

theorem afterFall_bound (r : Request) (samples : Vector Bool 16) (slot : Fin 45)
    (h : ActiveBound r (.fall slot)) : ActiveBound r (afterFall r samples slot) := by
  grind [afterFall, ActiveBound, Request.byteCount]
  done

theorem step_bound (cfg : Config) (r : Request) (s : State) (bus : Bus)
    (h : ActiveBound r s.phase) : ActiveBound r (step cfg r s bus).phase := by
  cases hp : s.phase <;> grind [step, guarded, timed, blocked, count, move, finish, ActiveBound, afterFall_bound]
  done

theorem run_bound (cfg : Config) (r : Request) (incoming : Nat → Bus) (n : Nat) :
    ActiveBound r (run cfg r (initial cfg) incoming n).phase :=
  Nat.rec (show ActiveBound r (initial cfg).phase from True.intro) (fun _ ih => step_bound cfg r _ _ ih) n

theorem capture_before_second (slot : Fin 45) (destination : Fin 16)
    (h : slot.val < 36) (hs : sampleAt slot = some destination) : destination.val < 8 := by
  grind [sampleAt]
  done

theorem latch_before_second (samples : Vector Bool 16) (slot : Fin 45) (sda : Bool)
    (h : slot.val < 36) (index : Fin 16) (hi : 8 ≤ index.val) :
    (latch samples slot sda)[index.val] = samples[index.val] := by
  cases hs : sampleAt slot with
  | none => simp [latch, hs]
  | some destination =>
    simp [latch, hs]
    have hk := capture_before_second slot destination h hs
    simp [show destination.val ≠ index.val by omega]
    done

theorem step_one_byte_preserves_upper (cfg : Config) (r : Request) (s : State) (bus : Bus)
    (hc : r.countMinusOne = 0) (h : ActiveBound r s.phase) (index : Fin 16) (hi : 8 ≤ index.val) :
    (step cfg r s bus).samples[index.val] = s.samples[index.val] := by
  cases hp : s.phase <;> simp [step, hp, guarded, timed, blocked, finish, count, move]
  all_goals repeat first | split | (solve | simp_all [ActiveBound, Request.byteCount, latch_before_second])
  done

/-- The compact one-byte packet keeps its unused upper capture byte zero. -/
theorem run_one_byte_upper_false (cfg : Config) (r : Request) (incoming : Nat → Bus) (n : Nat)
    (hc : r.countMinusOne = 0) (index : Fin 16) (hi : 8 ≤ index.val) :
    (run cfg r (initial cfg) incoming n).samples[index.val] = false :=
  Nat.rec (show (initial cfg).samples[index.val] = false from by simp [initial])
    (fun n ih => (step_one_byte_preserves_upper cfg r _ _ hc (run_bound cfg r incoming n) index hi).trans ih) n

theorem write_address_nack_stops (r : Request) (samples : Vector Bool 16) (h : samples[0] = true) :
    afterFall r samples 8 = .stopLow true := by
  simp [afterFall, h, show (8 : Fin 45).val = 8 from rfl]
  done

theorem register_nack_stops (r : Request) (samples : Vector Bool 16) (h : samples[1] = true) :
    afterFall r samples 17 = .stopLow true := by
  simp [afterFall, h, show (17 : Fin 45).val = 17 from rfl]
  done

theorem read_address_nack_stops (r : Request) (samples : Vector Bool 16) (h : samples[2] = true) :
    afterFall r samples 26 = .stopLow true := by
  simp [afterFall, h, show (26 : Fin 45).val = 26 from rfl]
  done

theorem first_read_ack_two_bytes (r : Request) (h : r.countMinusOne = 1) :
    releaseData r 35 = false := by
  simp [releaseData, h, show (35 : Fin 45).val = 35 from rfl]
  done

theorem final_read_nack_released (r : Request) : releaseData r 44 = true := rfl

end Pinwheel.I2C.RegisterReadTransaction
