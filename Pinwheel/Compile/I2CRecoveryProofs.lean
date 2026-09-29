import Pinwheel.Compile.I2CRecovery
import Pinwheel.Compile.I2CPhases
import Pinwheel.Engine.FetchProofs

set_option maxRecDepth 4096

namespace Pinwheel.Compile.I2CRecovery
open Engine.Reactive

private theorem pulse_cases (pulse : Fin 9) :
    pulse = 0 ∨ pulse = 1 ∨ pulse = 2 ∨ pulse = 3 ∨ pulse = 4 ∨
      pulse = 5 ∨ pulse = 6 ∨ pulse = 7 ∨ pulse = 8 := by omega

private theorem remaining_pos (r : Fin 256) : (0 < r.val) ↔ r ≠ 0 := by omega

private theorem literals :
    (0 : Fin 256).val = 0 ∧
    (1 : Fin 256).val = 1 ∧
    (2 : Fin 256).val = 2 ∧
    (3 : Fin 256).val = 3 ∧
    (4 : Fin 256).val = 4 ∧
    (5 : Fin 256).val = 5 ∧
    (6 : Fin 256).val = 6 ∧
    (7 : Fin 256).val = 7 ∧
    (8 : Fin 256).val = 8 ∧
    (9 : Fin 256).val = 9 ∧
    (10 : Fin 256).val = 10 ∧
    (11 : Fin 256).val = 11 ∧
    (12 : Fin 256).val = 12 ∧
    (13 : Fin 256).val = 13 ∧
    (14 : Fin 256).val = 14 ∧
    (15 : Fin 256).val = 15 ∧
    (16 : Fin 256).val = 16 ∧
    (17 : Fin 256).val = 17 ∧
    (18 : Fin 256).val = 18 ∧
    (19 : Fin 256).val = 19 ∧
    (20 : Fin 256).val = 20 ∧
    (21 : Fin 256).val = 21 ∧
    (22 : Fin 256).val = 22 ∧
    (23 : Fin 256).val = 23 ∧
    (24 : Fin 256).val = 24 ∧
    (25 : Fin 256).val = 25 ∧
    (26 : Fin 256).val = 26 ∧
    (27 : Fin 256).val = 27 ∧
    (28 : Fin 256).val = 28 ∧
    (29 : Fin 256).val = 29 ∧
    (30 : Fin 256).val = 30 ∧
    (0 : Fin 9).val = 0 ∧
    (1 : Fin 9).val = 1 ∧
    (2 : Fin 9).val = 2 ∧
    (3 : Fin 9).val = 3 ∧
    (4 : Fin 9).val = 4 ∧
    (5 : Fin 9).val = 5 ∧
    (6 : Fin 9).val = 6 ∧
    (7 : Fin 9).val = 7 ∧
    (8 : Fin 9).val = 8 ∧
    (0 : Fin 3).val = 0 ∧
    (1 : Fin 3).val = 1 ∧
    (2 : Fin 3).val = 2 ∧
    (0 : Fin 16).val = 0 := by repeat constructor

attribute [local simp] capture lift control advance program Program.fetch instruction pulseInstruction pulsePC
  I2C.check_clock I2C.check_both I2C.input_clock I2C.input_data Condition.ready
  next enter stop dispatch jump
  Pinwheel.I2C.Recovery.step Pinwheel.I2C.Recovery.move Pinwheel.I2C.Recovery.count
  Pinwheel.I2C.Recovery.blocked Pinwheel.I2C.Recovery.finish Pinwheel.I2C.Recovery.qualify
  Pinwheel.I2C.Recovery.afterHigh Pinwheel.I2C.Recovery.pins
  I2C.encodePins Pins.openDrain remaining_pos literals

set_option maxHeartbeats 1000000 in
theorem advance_high (cfg : Config) (s : ModelState) (pulse : Fin 9)
    (bus : Pinwheel.I2C.Bus) (hp : s.phase = .high pulse) :
    advance (program cfg) (lift s) (I2C.encodeInputs bus) =
      lift (Pinwheel.I2C.Recovery.step cfg s bus) := by
  rcases pulse_cases pulse with hs | hs | hs | hs | hs | hs | hs | hs | hs
  all_goals by_cases hr : s.remaining = 0 <;> cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all [Engine.capture]
  all_goals ext i hi
  all_goals by_cases h : i = 0 <;> simp [h, Fin.ext_iff, Vector.getElem_set]
  done

/-- Every state and arbitrary sampled bus, including timeout/fault continuations. -/
theorem advance_simulation (cfg : Config) (s : ModelState) (bus : Pinwheel.I2C.Bus) :
    advance (program cfg) (lift s) (I2C.encodeInputs bus) =
      lift (Pinwheel.I2C.Recovery.step cfg s bus) := by
  cases hp : s.phase with
  | high pulse => exact advance_high cfg s pulse bus hp
  | low pulse =>
    rcases pulse_cases pulse with hs | hs | hs | hs | hs | hs | hs | hs | hs
    all_goals by_cases hr : s.remaining = 0 <;> simp_all
    done
  | rise pulse =>
    rcases pulse_cases pulse with hs | hs | hs | hs | hs | hs | hs | hs | hs
    all_goals by_cases hw : s.waitLeft = 0 <;> cases hb : bus.scl <;> simp_all
    done
  | clockFree | released | finished | timeout | fault =>
    by_cases hr : s.remaining = 0 <;> by_cases hw : s.waitLeft = 0 <;>
      cases hb : bus.scl <;> cases hd : bus.sda <;> simp_all
    done

theorem initial_matches (cfg : Config) (inputs : Inputs) :
    start (program cfg) inputs = lift (Pinwheel.I2C.Recovery.initial cfg) := by
  simp [start, Pinwheel.I2C.Recovery.initial]
  done

theorem run_simulation (cfg : Config) (incoming : Nat → Pinwheel.I2C.Bus) (n : Nat) :
    run (program cfg) (start (program cfg) (I2C.encodeInputs (incoming 0)))
      (fun t => I2C.encodeInputs (incoming t)) n =
      lift (Pinwheel.I2C.Recovery.run cfg (Pinwheel.I2C.Recovery.initial cfg) incoming n) := by
  induction n <;> simp_all only [run, Pinwheel.I2C.Recovery.run, initial_matches, advance_simulation]
  done

theorem result_lift (s : ModelState) :
    result (lift s) = Pinwheel.I2C.Recovery.result s := by
  cases hp : s.phase <;> simp [result, Pinwheel.I2C.Recovery.result, hp]
  done

theorem reset_releases (cfg : Config) (s : RecoveryState) (inputs : Inputs) (requested : Bool) :
    (step (program cfg) s true requested inputs).pins = ({} : Pins) := rfl

theorem position_bound (cfg : Config) : (program cfg).last.val + 1 = 30 := rfl

/-- Every remaining memory slot is the same halt as position 29. Together with
the position bound this limits the image to at most thirty distinct records. -/
theorem unused_halt (cfg : Config) (pc : Fin 256) (h : 29 ≤ pc.val) :
    (program cfg).fetch pc = .halt := by
  simp [show pc.val ≠ 0 by omega, show ¬pc.val < 28 by omega, show pc.val ≠ 28 by omega]
  done

/-- No phase, including timeout and fault, drives SDA or the unused logical output. -/
theorem drive_mask (s : ModelState) :
    (lift s).pins.levels = 0 ∧ ((lift s).pins.enabled &&& 6) = 0 := by
  cases hp : s.phase <;> simp [hp]
  done

theorem terminal_releases (s : ModelState) (h : (Pinwheel.I2C.Recovery.result s).isSome = true) :
    (lift s).pins = ({} : Pins) := by
  cases hp : s.phase <;> simp_all [Pinwheel.I2C.Recovery.result]
  done

theorem decoded_agrees (cfg : Config) :
    Fetch.Agrees (Hardware.Execution.directStore (Hardware.Execution.imageWords (program cfg))
      (program cfg).idle (program cfg).last) (program cfg) :=
  Hardware.Execution.direct_agrees (program cfg)

theorem decoded_run (cfg : Config) (incoming : Nat → Pinwheel.I2C.Bus) (cycle : Nat) :
    Fetch.run (Hardware.Execution.directStore (Hardware.Execution.imageWords (program cfg))
      (program cfg).idle (program cfg).last)
      (start (program cfg) (I2C.encodeInputs (incoming 0)))
      (fun t => I2C.encodeInputs (incoming t)) cycle =
      lift (Pinwheel.I2C.Recovery.run cfg (Pinwheel.I2C.Recovery.initial cfg) incoming cycle) :=
  (Fetch.run_eq _ _ (decoded_agrees cfg) _ _ _).trans (run_simulation cfg incoming cycle)

end Pinwheel.Compile.I2CRecovery
