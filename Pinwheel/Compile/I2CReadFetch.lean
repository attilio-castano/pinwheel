import Pinwheel.Compile.I2CReadProofs

/-! Identify the first ACK capture and the following dispatch in the
independent reference. These are different cuts of the same compiled image. -/
namespace Pinwheel.Compile.I2CRead
open Engine.Reactive
open Pinwheel.I2C

private theorem high_not_dispatch : ∀ slot : Fin 36, bitPC slot 2 ≠ 37 := by
  decide +kernel

private theorem first_dispatch_slot : ∀ slot : Fin 36, bitPC slot 3 = 37 ↔ slot = 8 := by
  decide +kernel

/-- PC 37 dispatches the first ACK branch after its low hold. -/
theorem first_ack_dispatch (s : RegisterRead.State) :
    control s = .checked 37 0 ↔ s.phase = .fall 8 ∧ s.remaining = 0 := by
  cases phase : s.phase <;> simp [control, phase, high_not_dispatch, first_dispatch_slot]

private theorem dispatch_not_high : ∀ slot : Fin 36, bitPC slot 3 ≠ 36 := by
  decide +kernel

private theorem first_capture_slot : ∀ slot : Fin 36, bitPC slot 2 = 36 ↔ slot = 8 := by
  decide +kernel

/-- PC 36 is still at the high-phase aperture and has not latched the ACK. -/
theorem first_ack_capture (s : RegisterRead.State) :
    control s = .checked 36 0 ↔ s.phase = .high 8 ∧ s.remaining = 0 := by
  cases phase : s.phase <;> simp [control, phase, dispatch_not_high, first_capture_slot]

end Pinwheel.Compile.I2CRead
