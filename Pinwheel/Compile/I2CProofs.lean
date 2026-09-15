import Pinwheel.Compile.I2CPhases

namespace Pinwheel.Compile.I2C
open Engine.Reactive

/-- Every reference phase is implemented by the same loaded instruction image. -/
theorem advance_simulation (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (e : State) (bus : Pinwheel.I2C.Bus) (hm : Matches s e) :
    Matches (Pinwheel.I2C.step cfg s bus)
      (advance (program cfg s.request) e (encodeInputs bus)) := by
  rcases hm with ⟨he, hs⟩
  rw [he]
  cases hp : s.phase with
  | free => exact advance_free cfg s e.samples bus hp hs
  | startHold => exact advance_start cfg s e.samples bus hp hs
  | setup => exact advance_setup cfg s e.samples bus hp hs
  | rise => exact advance_rise cfg s e.samples bus hp hs
  | high => exact advance_high cfg s e.samples bus hp hs
  | fall => exact advance_fall cfg s e.samples bus hp hs
  | stopLow => exact advance_stopLow cfg s e.samples bus hp hs
  | stopRise => exact advance_stopRise cfg s e.samples bus hp hs
  | stopHigh => exact advance_stopHigh cfg s e.samples bus hp hs
  | stopFree => exact advance_stopFree cfg s e.samples bus hp hs
  | finished => exact advance_finished cfg s e.samples bus hp hs
  done

theorem request_retained (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State) (bus : Pinwheel.I2C.Bus) :
    (Pinwheel.I2C.step cfg s bus).request = s.request := by
  cases hp : s.phase <;> simp [Pinwheel.I2C.step, hp, Pinwheel.I2C.finish, Pinwheel.I2C.move,
    Pinwheel.I2C.count, Pinwheel.I2C.blocked, Pinwheel.I2C.afterHigh, Pinwheel.I2C.afterFall]
  all_goals repeat first | rfl | split
  done

theorem run_request (cfg : Pinwheel.I2C.Config) (s : Pinwheel.I2C.State)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    (Pinwheel.I2C.run cfg s incoming n).request = s.request := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Pinwheel.I2C.run, request_retained, ih]
  done

theorem initial_matches (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request) (inputs : Inputs) :
    Matches (Pinwheel.I2C.initial cfg r) (start (program cfg r) inputs) := by
  simp [Matches, lift, control, SamplesOK, sampleOutcome, start, enter, program, Program.fetch,
    instruction, Pinwheel.I2C.initial, Pinwheel.I2C.pins, encodePins, Pins.openDrain]
  done

theorem run_simulation (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    Matches (Pinwheel.I2C.run cfg (Pinwheel.I2C.initial cfg r) incoming n)
      (run (program cfg r) (start (program cfg r) (encodeInputs (incoming 0)))
        (fun t => encodeInputs (incoming t)) n) := by
  induction n with
  | zero => exact initial_matches cfg r _
  | succ n ih =>
    simpa only [run, Pinwheel.I2C.run, run_request, Pinwheel.I2C.initial] using
      advance_simulation cfg (Pinwheel.I2C.run cfg (Pinwheel.I2C.initial cfg r) incoming n) _
        (incoming (n + 1)) ih
  done

def execute (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) : State :=
  run (program cfg r) (start (program cfg r) (encodeInputs (incoming 0)))
    (fun t => encodeInputs (incoming t)) n

theorem waveform_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    (execute cfg r incoming n).pins =
      encodePins (Pinwheel.I2C.pins (Pinwheel.I2C.run cfg (Pinwheel.I2C.initial cfg r) incoming n)) := by
  exact congrArg State.pins (run_simulation cfg r incoming n).1
  done

theorem outcome_matches (s : Pinwheel.I2C.State) (e : State) (h : Matches s e) :
    outcome e = Pinwheel.I2C.result s := by
  rcases h with ⟨he, hs⟩
  rw [he]
  cases hp : s.phase <;> simp [outcome, Pinwheel.I2C.result, Pinwheel.I2C.busy, lift, control, hp]
  all_goals simp [SamplesOK, hp] at hs
  all_goals rcases hs with (ho | ho) | ho <;> simp [ho, sampleOutcome]
  all_goals by_cases h0 : e.samples[0] = true <;> by_cases h1 : e.samples[1] = true <;> simp [h0, h1]
  done

theorem result_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    outcome (execute cfg r incoming n) =
      Pinwheel.I2C.result (Pinwheel.I2C.run cfg (Pinwheel.I2C.initial cfg r) incoming n) := by
  exact outcome_matches _ _ (run_simulation cfg r incoming n)
  done

theorem busy_lift (s : Pinwheel.I2C.State) (slots : Engine.Samples) :
    busy (lift s slots) = Pinwheel.I2C.busy s := by
  cases hp : s.phase <;> simp [busy, lift, control, Pinwheel.I2C.busy, hp]
  done

theorem busy_correct (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    busy (execute cfg r incoming n) =
      Pinwheel.I2C.busy (Pinwheel.I2C.run cfg (Pinwheel.I2C.initial cfg r) incoming n) := by
  simpa only [busy_lift, execute] using congrArg busy (run_simulation cfg r incoming n).1
  done

theorem reset_releases (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (s : State) (inputs : Inputs) (startRequested : Bool) :
    (step (program cfg r) s true startRequested inputs).pins = ({} : Pins) := rfl

end Pinwheel.Compile.I2C
