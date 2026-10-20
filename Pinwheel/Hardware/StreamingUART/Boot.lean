import Pinwheel.Hardware.StreamingReady.BootCorrespondence
import Pinwheel.Hardware.StreamingReady.InitializedCustody
import Pinwheel.Program.StreamingUARTArm
import Pinwheel.Program.StreamingUARTStartPins

/-! Concrete cold upload of the UART source image. The three qualification
rates use sampled wire frames, not an assumed delivered loader history. -/
namespace Pinwheel.Hardware.StreamingUART.Boot
open Pinwheel.Program.StreamingReady
open Pinwheel.Program.StreamingUART
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

def profile (rate : Fin 3) : Profile :=
  ⟨⟨if rate.val = 0 then 0 else if rate.val = 1 then 8 else 124, by split <;> (try split) <;> omega⟩,0⟩

def pins (rate : Fin 3) : List Session.Pins := BootPins.compiled (image (profile rate))

theorem length (rate : Fin 3) : (pins rate).length = 2450 := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked (rate : Fin 3) :
    Pinwheel.Program.Streaming.BootPins.check (image (profile rate)).words ⟨0,0⟩ BootPins.initialControl 0 false (pins rate) = true := by
  revert rate
  decide +kernel

theorem certified (rate : Fin 3) :
    Pinwheel.Program.Streaming.BootPins.Certified (image (profile rate)).words ⟨0,0⟩ BootPins.initialControl 0 false (pins rate) :=
  Pinwheel.Program.Streaming.BootPins.check_sound _ _ _ _ _ _ (checked rate)

/-- No startup, bank, VALID, sampler or loader-admission premise. -/
theorem initialized (rate : Fin 3) (startup : Pinwheel.Hardware.StreamingReady.Package.State a) :
    ∃ final : Session.State a, Pinwheel.Hardware.StreamingReady.BootCorrespondence.Initialized (image (profile rate))
      (startup.run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
        (Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins BootPins.coldPin :: (pins rate).map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)) final :=
  Pinwheel.Hardware.StreamingReady.BootCorrespondence.compiled_initialized (image (profile rate)) (pins rate) (certified rate) startup

def endControl (control : Pinwheel.Program.Streaming.BootPins.Control) (pins : List Session.Pins) : Pinwheel.Program.Streaming.BootPins.Control :=
  pins.foldl (fun c pin => Pinwheel.Program.Streaming.Host.BootControl.step false (pin.host {}) c) control

/-- The exact projected frontend control at the end of the physical upload. -/
theorem certified_control {src : List Instruction} (image : Compiled src idle) (control : Pinwheel.Program.Streaming.BootPins.Control)
    (n : Nat) (installed : Bool) (pins : List Session.Pins)
    (certificate : Pinwheel.Program.Streaming.BootPins.Certified image.words idle control n installed pins)
    (actual : Pinwheel.Hardware.StreamingReady.Package.State a) (sourceCore : Pinwheel.Hardware.StreamingReady.Initialization.Carrier a)
    (related : Pinwheel.Hardware.StreamingReady.BootCorrespondence.Related image control n installed actual sourceCore) :
    Pinwheel.Program.Streaming.Host.BootControl.project (Pinwheel.Hardware.Streaming.HostCorrespondence.stateFromValues
      (actual.run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a) (pins.map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)).frontend) =
      endControl control pins := by
  induction certificate generalizing actual sourceCore with
  | nil => exact related.project
  | cons safe delivery after induction =>
    obtain ⟨next,nextRelated⟩ := Pinwheel.Hardware.StreamingReady.BootCorrespondence.Related.step image _ _ _ actual sourceCore related _ safe delivery
    exact induction _ _ nextRelated

theorem compiled_control {src : List Instruction} (compiled : Compiled src idle)
    (samples : List Session.Pins)
    (certificate : Pinwheel.Program.Streaming.BootPins.Certified compiled.words idle BootPins.initialControl 0 false samples)
    (startup : Pinwheel.Hardware.StreamingReady.Package.State a) :
    Pinwheel.Program.Streaming.Host.BootControl.project (Pinwheel.Hardware.Streaming.HostCorrespondence.stateFromValues
      (startup.run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
        (Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins BootPins.coldPin :: samples.map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)).frontend) =
      endControl BootPins.initialControl samples := by
  change Pinwheel.Program.Streaming.Host.BootControl.project (Pinwheel.Hardware.Streaming.HostCorrespondence.stateFromValues
    ((startup.step (Pinwheel.Hardware.StreamingReady.Package.Components.typed a) (Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins BootPins.coldPin)).run
      (Pinwheel.Hardware.StreamingReady.Package.Components.typed a) (samples.map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)).frontend) = _
  rw [Pinwheel.Hardware.StreamingReady.InitializedSession.cold_correct startup (Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins BootPins.coldPin) rfl]
  exact certified_control compiled _ _ _ _ certificate _ _
    (Pinwheel.Hardware.StreamingReady.BootCorrespondence.cold_related compiled)

theorem initialized_control (rate : Fin 3) (startup : Pinwheel.Hardware.StreamingReady.Package.State a) :
    Pinwheel.Program.Streaming.Host.BootControl.project (Pinwheel.Hardware.Streaming.HostCorrespondence.stateFromValues
      (startup.run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
        (Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins BootPins.coldPin :: (pins rate).map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)).frontend) =
      endControl BootPins.initialControl (pins rate) :=
  compiled_control (image (profile rate)) (pins rate) (certified rate) startup

set_option maxHeartbeats 4000000 in
theorem start_checked (rate : Fin 3) :
    StartPins.check (endControl BootPins.initialControl (pins rate)) false 0 StartPins.pins = true := by
  revert rate
  decide +kernel

theorem start_certified (rate : Fin 3) :
    StartPins.Certified (endControl BootPins.initialControl (pins rate)) false 0 StartPins.pins :=
  StartPins.check_sound _ _ _ _ (start_checked rate)

end Pinwheel.Hardware.StreamingUART.Boot
