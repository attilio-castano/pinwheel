import Pinwheel.Engine.ReactiveProofs

/-! A five-slot program exercising observation-anchored timing; not a full I2C transfer. -/
namespace Pinwheel.Compile.StretchedPulse
open Engine.Reactive

/-- Logical output/input 0 is SCL; 1 is SDA. Output 2 is released. -/
def program (durationMinusOne budgetMinusOne : Fin 256) (data : Bool) : Program :=
  let dataLow : Engine.Levels := if data then 0 else 2
  let low := Pins.openDrain (dataLow ||| 1)
  let releasedClock := Pins.openDrain dataLow
  ⟨Vector.ofFn (fun pc =>
    if pc.val == 0 then .action ⟨low, durationMinusOne, none⟩
    else if pc.val == 1 then .wait ⟨releasedClock, ⟨0, true⟩, budgetMinusOne⟩
    else if pc.val == 2 then .action ⟨releasedClock, durationMinusOne, none⟩
    else if pc.val == 3 then .action ⟨low, durationMinusOne, some ⟨1, 0⟩⟩
    else .halt), {}⟩

end Pinwheel.Compile.StretchedPulse
