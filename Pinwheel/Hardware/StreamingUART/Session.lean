import Pinwheel.Hardware.StreamingUART.Boot
import Pinwheel.Program.StreamingUARTStart
import Pinwheel.Program.StreamingUARTFrame

/-! Actual initialized UART continuation. The frontend generates the engine
commands on every edge, and public deselected pins derive their quiescence. -/
namespace Pinwheel.Hardware.StreamingUART.Session
open Pinwheel.Program.StreamingReady
open Pinwheel.Program.StreamingUART
set_option linter.unusedSimpArgs false

abbrev Actual (a : Nat) := Pinwheel.Hardware.StreamingReady.Package.State a

def loaded (rate : Fin 3) (startup : Actual a) : Actual a :=
  startup.run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
    (Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins BootPins.coldPin ::
      (Boot.pins rate).map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)

def armedActual (rate : Fin 3) (startup : Actual a) : Actual a :=
  (loaded rate startup).run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
    (StartPins.pins.map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins)

structure Armed (rate : Fin 3) (actual : Actual a) (s : Pinwheel.Program.StreamingReady.Session.State a) : Prop where
  package : actual = Pinwheel.Hardware.StreamingReady.SessionCorrespondence.values
    (Pinwheel.Hardware.StreamingReady.Initialization.compiledImage (image (Boot.profile rate))) s
  core : s.core = Arm.armed (Boot.profile rate) 1 1
  idle : HostQuiet.Idle s.host
  custody : ∃ trace : BitTrace, s.Custody trace ∧ s.FreeExport

/-- Concrete cold, nine writes, COMMIT and accepted START. No input-state,
loader-history, source/circuit agreement or START admission premise. -/
theorem initialized_armed (rate : Fin 3) (startup : Actual a) (ha : a ≤ 3) :
    ∃ s : Pinwheel.Program.StreamingReady.Session.State a, Armed rate (armedActual rate startup) s := by
  obtain ⟨boot,initialized⟩ := Boot.initialized rate startup
  have project := Boot.initialized_control rate startup
  rw [initialized.package] at project
  change Pinwheel.Program.Streaming.Host.BootControl.project
    (Pinwheel.Hardware.Streaming.HostCorrespondence.stateFromValues
      (Pinwheel.Hardware.Streaming.HostCorrespondence.values boot.host)) = _ at project
  rw [Pinwheel.Hardware.StreamingReady.InitializedSession.frontend_source_roundtrip] at project
  have cut : Start.CoreCut (Boot.profile rate) false 0 boot.core :=
    .free boot.core initialized.free initialized.generation initialized.transfer
  have reached := Start.certified_run (Boot.profile rate) boot _ StartPins.pins (Boot.start_certified rate) project cut
  have custody := Start.certified_custody (Boot.profile rate) boot _ StartPins.pins (Boot.start_certified rate)
    project cut ha (Pinwheel.Hardware.StreamingReady.InitializedCustody.initialized_control initialized) trivial
  refine ⟨boot.run (image (Boot.profile rate)).program false StartPins.pins,?_,reached.1,reached.2.1,custody⟩
  change (loaded rate startup).run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
    (StartPins.pins.map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins) = _
  have bootPackage := initialized.package
  change loaded rate startup = _ at bootPackage
  rw [bootPackage]
  simpa only [Pinwheel.Hardware.StreamingReady.InitializedCustody.compiled_pending] using
    Pinwheel.Hardware.StreamingReady.SessionCorrespondence.run_correct
      (Pinwheel.Hardware.StreamingReady.Initialization.compiledImage (image (Boot.profile rate))) boot StartPins.pins ha
      (by simpa only [Pinwheel.Hardware.StreamingReady.InitializedCustody.compiled_pending] using reached.2.2) initialized.structural

/-- Any physical idle-host continuation clocks the same source engine on every
sample. Raw data may vary arbitrarily; no delivered quiet command is assumed. -/
theorem armed_runtime (rate : Fin 3) (actual : Actual a) (s : Pinwheel.Program.StreamingReady.Session.State a)
    (armed : Armed rate actual s) (inputs : List Pinwheel.Program.StreamingReady.Session.Pins)
    (ha : a ≤ 3) (pins : ∀ pin ∈ inputs, HostQuiet.Pins pin) :
    actual.run (Pinwheel.Hardware.StreamingReady.Package.Components.typed a)
        (inputs.map Pinwheel.Hardware.StreamingReady.SessionCorrespondence.pins) =
      Pinwheel.Hardware.StreamingReady.SessionCorrespondence.values
        (Pinwheel.Hardware.StreamingReady.Initialization.compiledImage (image (Boot.profile rate)))
        (s.run (image (Boot.profile rate)).program false inputs) ∧
    (s.run (image (Boot.profile rate)).program false inputs).core =
      run (image (Boot.profile rate)).program (Arm.armed (Boot.profile rate) 1 1)
        (inputs.map (fun pin => ({rawInputs := pin.rawInputs} : Input))) ∧
    (∃ trace : BitTrace, (s.run (image (Boot.profile rate)).program false inputs).Custody trace ∧
      (s.run (image (Boot.profile rate)).program false inputs).FreeExport) := by
  have runtime := HostQuiet.runtime_trace s (image (Boot.profile rate)).program false inputs armed.idle pins
  obtain ⟨trace,custody,freeExport⟩ := armed.custody
  refine ⟨?_,?_,⟨s.traceRun (image (Boot.profile rate)).program false trace inputs,
    custody.run s _ false inputs trace ha runtime,freeExport.run s _ false inputs trace ha runtime custody⟩⟩
  · rw [armed.package]
    simpa only [Pinwheel.Hardware.StreamingReady.InitializedCustody.compiled_pending] using
      Pinwheel.Hardware.StreamingReady.SessionCorrespondence.run_correct
        (Pinwheel.Hardware.StreamingReady.Initialization.compiledImage (image (Boot.profile rate))) s inputs ha
        (by simpa only [Pinwheel.Hardware.StreamingReady.InitializedCustody.compiled_pending] using runtime) custody.structural
  · rw [HostQuiet.run_core_canonical s _ false inputs armed.idle pins,armed.core]

end Pinwheel.Hardware.StreamingUART.Session
