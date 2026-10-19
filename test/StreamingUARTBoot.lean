import Pinwheel.Hardware.StreamingUART.All

namespace Pinwheel.Test.StreamingUARTBoot
open Pinwheel.Program.StreamingReady
open Pinwheel.Program.StreamingUART
open Pinwheel.Hardware.StreamingUART

example (rate : Fin 3) : (Boot.pins rate).length + 1 = 2451 := by rw [Boot.length]
example : StartPins.pins.length = 245 := StartPins.length

example (rate : Fin 3) (startup : Pinwheel.Hardware.StreamingReady.Package.State 1) :
    ∃ final : Pinwheel.Program.StreamingReady.Session.State 1,
      Pinwheel.Hardware.StreamingReady.BootCorrespondence.Initialized (image (Boot.profile rate))
        (Session.loaded rate startup) final := Boot.initialized rate startup

example (rate : Fin 3) (startup : Pinwheel.Hardware.StreamingReady.Package.State 2) :
    ∃ final : Pinwheel.Program.StreamingReady.Session.State 2,
      Session.Armed rate (Session.armedActual rate startup) final :=
  Session.initialized_armed rate startup (by decide)

/-- Selected-rate physical initialization has no source agreement premise. -/
example (startup : Pinwheel.Hardware.StreamingReady.Package.State 1) :
    ∃ final : Pinwheel.Program.StreamingReady.Session.State 1,
      Session.Armed 0 (Session.armedActual 0 startup) final :=
  Session.initialized_armed 0 startup (by decide)

example (rate : Fin 3) : StartPins.Certified (Boot.endControl BootPins.initialControl (Boot.pins rate))
    false 0 StartPins.pins := Boot.start_certified rate

#print axioms Boot.checked
#print axioms Boot.start_checked
#print axioms Session.initialized_armed
#print axioms Session.armed_runtime
#print axioms Pinwheel.Hardware.StreamingUART.Frame.concrete_good
#print axioms Pinwheel.Hardware.StreamingUART.Frame.concrete_bad_stop
#print axioms Pinwheel.Hardware.StreamingUART.Frame.concrete_false_start
end Pinwheel.Test.StreamingUARTBoot
