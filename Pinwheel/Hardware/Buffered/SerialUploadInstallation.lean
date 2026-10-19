import Pinwheel.Hardware.Buffered.SerialUploadTrace

/-! From arbitrary digital SRAM contents and responses, a cold sampled edge
followed by all 67 actual serial loader transactions installs the I²C image.
The resulting frontend is available for the first source transfer. -/
namespace Pinwheel.Hardware.Buffered.SerialUpload
open Pinwheel.Hardware SerialWire
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

theorem cold_input (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (cold : pin.cold = true) : s.coreInputs pin .initialize = 1 := by
  rw [s.record_coreInputs]
  simp [Serial.State.coreInput, SerialPackage.State.inputs, SerialPackage.Pins.inputs, cold]
  done

theorem cold_available (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (cold : pin.cold = true) (idle : pin.csn = true) : Serial.Frames.Available (s.step pin).record := by
  rw [s.record_step]
  constructor
  all_goals simp [Serial.State.step, SerialPackage.State.inputs, SerialPackage.Pins.inputs, cold, idle]
  all_goals done

theorem cold_progress (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (cold : pin.cold = true) : TableProgress 0 0 (s.step pin).controller := by
  have coldInit := cold_input s pin cold
  have reset : Reactive.resetting.eval (s.coreInputs pin) s.controller.core = 1 := by
    simp [Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, coldInit]
  have cleared := Lifecycle.reset_ownership s.controller (s.coreInputs pin) reset
  exact ⟨cleared.2.2, cleared.2.1, by omega, by intro k impossible; omega,
    (Lifecycle.cold_counters s.controller (s.coreInputs pin) coldInit).1⟩
  done

theorem Loading.controller_run {before} (loading : Loading before) :
    before.controller.run (before.commands loading.pins) = loading.after.controller := by
  rw [← before.run_controller, loading.run_pins]
  done

theorem cold_install (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (cold : pin.cold = true) (idle : pin.csn = true) (loading : Loading (s.step pin)) :
    Refinement.InstalledSram I2cSource.source I2cCertificate.layout loading.after.controller ∧
      loading.after.controller.core .phase = 0 ∧ loading.after.controller.core .retained = 0 ∧
      loading.after.controller.core .generation = 1 ∧ loading.after.controller.core .transfer = 0 ∧
      Serial.Frames.Available loading.after.record ∧
      s.run (pin :: loading.pins) = loading.after := by
  have result := loading.result (cold_progress s pin cold) (by decide) (cold_available s pin cold idle)
  have coldInit := cold_input s pin cold
  have reset : Reactive.resetting.eval (s.coreInputs pin) s.controller.core = 1 := by
    simp [Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, coldInit]
  have installed := I2cReload.reset_installed s.controller (s.coreInputs pin) reset
    ((s.step pin).commands loading.pins) result.2.1
  rw [I2cReloadSession.loading_run] at installed
  change ((s.step pin).controller.run ((s.step pin).commands loading.pins)).core .valid = 1 →
    Refinement.InstalledSram I2cSource.source I2cCertificate.layout
      ((s.step pin).controller.run ((s.step pin).commands loading.pins)) at installed
  rw [loading.controller_run] at installed
  have transfer := (LifecycleUpload.run (s.step pin).controller _ result.2.2.1
    (cold_progress s pin cold).phase (cold_progress s pin cold).retained).2.2.1
  rw [loading.controller_run] at transfer
  refine ⟨installed result.1.valid, result.1.phase, result.1.retained, ?_, ?_, result.2.2.2, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    exact result.1.generation
  · exact transfer.trans (Lifecycle.cold_counters s.controller (s.coreInputs pin) coldInit).2
  · exact loading.run_pins
  done

end Pinwheel.Hardware.Buffered.SerialUpload
