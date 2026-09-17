import Pinwheel.Latency
import Pinwheel.I2C.Proofs

/-! The I2C write controller behind an input pipeline. Unlike UART and SPI, this
controller checks the bus right after changing its own drive, so a delayed view
shows it its own earlier command. Two consequences are proved here for every
target, and a minimally revised controller is given that removes the first. -/
namespace Pinwheel.I2C

/-- While it prepares and holds STOP the controller itself keeps SDA low. -/
theorem stop_holds_data_low (s : State) (target : Pins)
    (h : s.phase = .stopLow ∨ s.phase = .stopRise ∨ s.phase = .stopHigh) :
    (resolve (pins s) target).sda = false := by
  rcases h with h | h | h <;> simp [pins, h, resolve, resolveLine]

/-- While it holds the clock low the controller itself keeps SCL low. -/
theorem low_phases_hold_clock_low (s : State) (target : Pins)
    (h : s.phase = .setup ∨ s.phase = .fall ∨ s.phase = .stopLow) :
    (resolve (pins s) target).scl = false := by
  rcases h with h | h | h <;> simp [pins, h, resolve, resolveLine]

/-- **Echo hazard.** In `stopFree` the controller expects a released bus at once.
Any observation that is still from its own STOP preparation reports a bus fault,
whatever the target does. Behind `d ≥ 1` input registers the first observation
consumed in `stopFree` is such an observation. -/
theorem stale_stop_observation_faults (cfg : Config) (s earlier : State) (target : Pins)
    (now : s.phase = .stopFree)
    (stale : earlier.phase = .stopLow ∨ earlier.phase = .stopRise ∨ earlier.phase = .stopHigh) :
    result (step cfg s (resolve (pins earlier) target)) = some .busFault := by
  have low := stop_holds_data_low earlier target stale
  simp [step, now, low, finish, result, busy]

/-- **Wait-budget hazard.** After releasing SCL the controller counts every
observation in which SCL still reads low as blocking. Observations from its own
clock-low phases are of that kind, so each clock rise spends one unit of the wait
budget per register of input latency before any target stretches at all. -/
theorem stale_clock_observation_blocks (cfg : Config) (s earlier : State) (target : Pins)
    (now : s.phase = .rise ∨ s.phase = .stopRise)
    (stale : earlier.phase = .setup ∨ earlier.phase = .fall ∨ earlier.phase = .stopLow) :
    step cfg s (resolve (pins earlier) target) = blocked cfg s := by
  have low := low_phases_hold_clock_low earlier target stale
  rcases now with now | now <;> simp [step, now, low]

/-- **Premature-high hazard.** If the latency exceeds the time the controller held
SCL low, the first observation consumed in `rise` predates that low phase and
reads high, so the high timer starts at once (`released_clock_starts_timer`).
The controller's own low phase then arrives as an observation in `high`, where a
low clock is a bus fault. The clock-low time must therefore cover the latency. -/
theorem stale_low_in_high_faults (cfg : Config) (s earlier : State) (target : Pins)
    (now : s.phase = .high ∨ s.phase = .stopHigh ∨ s.phase = .startHold)
    (stale : earlier.phase = .setup ∨ earlier.phase = .fall ∨ earlier.phase = .stopLow) :
    result (step cfg s (resolve (pins earlier) target)) = some .busFault := by
  have low := low_phases_hold_clock_low earlier target stale
  rcases now with now | now | now <;> simp [step, now, low, finish, result, busy]

/-- With a wait budget no larger than the latency, the first clock rise times out
on the controller's own echo: `waitLeft + 1` stale observations suffice. -/
theorem echo_exhausts_wait (cfg : Config) (s : State) (sda : Nat → Bool)
    (rising : s.phase = .rise) (fresh : s.remaining = cfg.phaseMinusOne) :
    result (run cfg s (fun t => ⟨false, sda t⟩) (s.waitLeft.val + 1)) = some .timeout :=
  stretch_timeout_exact cfg s sda rising fresh

/-- A revised controller: in `stopFree`, SDA still reading low *before any
bus-free cycle has been counted* is waited out against the wait budget, exactly as
a low SCL is in `rise`. Every other transition is unchanged. -/
def tolerantStep (cfg : Config) (s : State) (bus : Bus) (reset : Bool := false) : State :=
  if !reset && s.phase == .stopFree && bus.scl && !bus.sda && s.remaining == cfg.phaseMinusOne
  then blocked cfg s else step cfg s bus reset

/-- The revision is conservative: it differs only on that one kind of observation. -/
theorem tolerantStep_eq_step (cfg : Config) (s : State) (bus : Bus) (reset : Bool)
    (h : reset = true ∨ s.phase ≠ .stopFree ∨ bus.scl = false ∨ bus.sda = true ∨
      s.remaining ≠ cfg.phaseMinusOne) :
    tolerantStep cfg s bus reset = step cfg s bus reset := by
  unfold tolerantStep
  rcases h with h | h | h | h | h <;> simp [h]

/-- The echo no longer faults: it is waited out while budget remains. -/
theorem tolerant_waits_out_stop_echo (cfg : Config) (s earlier : State) (target : Pins)
    (now : s.phase = .stopFree) (fresh : s.remaining = cfg.phaseMinusOne)
    (stale : earlier.phase = .stopRise ∨ earlier.phase = .stopHigh)
    (clock : (resolve (pins earlier) target).scl = true) :
    tolerantStep cfg s (resolve (pins earlier) target) = blocked cfg s := by
  have low := stop_holds_data_low earlier target (Or.inr stale)
  simp [tolerantStep, now, fresh, low, clock]

/-- Once a bus-free cycle has been counted, a low SDA is again a fault: another
controller's START is not mistaken for an echo. Needs a phase of two or more cycles,
since the revision tells the cases apart by the phase timer. -/
theorem tolerant_faults_after_free (cfg : Config) (s : State) (scl : Bool)
    (now : s.phase = .stopFree) (counted : s.remaining ≠ cfg.phaseMinusOne) :
    result (tolerantStep cfg s ⟨scl, false⟩) = some .busFault := by
  rw [tolerantStep_eq_step cfg s ⟨scl, false⟩ false (Or.inr (Or.inr (Or.inr (Or.inr counted))))]
  simp [step, now, finish, result, busy]

end Pinwheel.I2C
