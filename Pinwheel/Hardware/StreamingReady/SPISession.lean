import Pinwheel.Hardware.StreamingReady.SessionProof
import Pinwheel.Program.StreamingSPIData

/-! The sampled-ready package executes both leading-edge SPI modes using
the same core, host frontend, and public pin wiring. -/
namespace Pinwheel.Hardware.StreamingReady.SPISession
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingSPI
open Pinwheel.Hardware.StreamingReady.InitializedCustody
set_option linter.unusedSimpArgs false

def bootPins (mode : Mode) : List Session.Pins := BootPins.compiled (image mode 3) 0

/-- Words and idle levels loaded by the standard four-cycle public-pin replay. -/
theorem standard_words (mode : Mode) :
    ((image mode 3).words, idlePins mode) =
      match mode with
      | .mode0 => ([1908414488,53515130905,1908414488,2], ⟨4,7⟩)
      | .mode2 => ([1976571928,53449070617,1976571928,2], ⟨6,7⟩) := by
  cases mode <;> decide +kernel

theorem boot (mode : Mode) (startup : Package.State a) :
    let actual := startup.run (Package.Components.typed a)
      (SessionCorrespondence.pins BootPins.coldPin :: (bootPins mode).map SessionCorrespondence.pins)
    ∃ source : Session.State a,
      BootCorrespondence.Initialized (image mode 3) actual source ∧ Pipeline (image mode 3) actual source := by
  apply compiled_session
  apply Pinwheel.Program.Streaming.BootPins.check_sound
  cases mode <;> decide +kernel

theorem driveTrace_eq {rows : List Instruction} (im : Compiled rows idle)
    (s : Session.State a) (pins : List Session.Pins)
    (ha : a ≤ 3) (runtime : Session.RuntimeTrace im.program false s pins) (structural : s.core.Structural) :
    PublicPins.driveTrace (SessionCorrespondence.values (Initialization.compiledImage im) s) pins =
      pinTrace im.program s.core (s.runtimeInputs im.program false pins) := by
  simpa only [compiled_pending] using PublicPins.driveTrace_eq (Initialization.compiledImage im)
    s pins ha (by simpa only [compiled_pending] using runtime) structural

theorem rawTrace_eq (s : Session.State a) (p : Program) (pins : List Session.Pins) :
    (s.runtimeInputs p false pins).map Pinwheel.Program.Streaming.Input.rawInputs =
      pins.map (fun pin => (PublicPins.embed pin).ui.extractLsb' 3 2) := by
  exact PublicPins.rawTrace_eq s p false pins

/-- Pin framing, payloads, and final host acknowledgment of one exchange. -/
def Exchange (mode : Mode) (d : Fin 256)
    (actualReady : Package.State a) (ready : Session.State a) (startPin : Session.Pins)
    (after : List Session.Pins) : Prop :=
    let p := (image mode d).program
    let started := ready.step p false startPin
    let actualStarted := actualReady.step (Package.Components.typed a) (SessionCorrespondence.pins startPin)
    let final := started.run p false after
    let trace := started.traceRun p false {} after
    let pins := PublicPins.driveTrace actualStarted after
    let apertures := 0 :: 0 :: after.map (fun pin => (PublicPins.embed pin).ui.extractLsb' 3 2)
    let count := (ready.command startPin).runtime.startCount.toNat
    events mode pins = .select :: edgesFor count ++ [.deselect] ∧
    activePulses mode d.val pins ∧
    (∀ sample ∈ pins, sample.enabled = 7#3) ∧
    trace.accepted = mosiOnLeading mode pins ∧
    trace.exported = misoOnLeading mode pins apertures ∧
    final.host.ackOffset.toNat = count ∧ final.host.exportBits.toNat = 0

/-- Actual START selects an installed SPI image. The proof also applies to
    a warm-installed image with old words outside its executable range. -/
theorem completed_from_start (mode : Mode) (d : Fin 256)
    (rep : SourceRefinement.Image (image mode d).program)
    (actualReady : Package.State a) (ready : Session.State a) (startPin : Session.Pins)
    (first : SessionProof.Started (image mode d) actualReady ready startPin rep)
    (after : List Session.Pins) (releasePin : Session.Pins) (ha : a ≤ 3) :
    let p := (image mode d).program
    let started := ready.step p false startPin
    let actualStarted := actualReady.step (Package.Components.typed a) (SessionCorrespondence.pins startPin)
    let final := started.run p false after
    let actualFinal := actualStarted.run (Package.Components.typed a) (after.map SessionCorrespondence.pins)
    Session.RuntimeTrace p false started after →
    (∀ i ∈ started.runtimeInputs p false after, i.command ≠ 4#4) →
    Session.RuntimeInput final releasePin →
    ActualRelease actualFinal releasePin →
    Exchange mode d actualReady ready startPin after := by
  dsimp only
  intro afterRuntime noRelease releaseRuntime release
  let im := image mode d
  let started := ready.step im.program false startPin
  let actualStarted := actualReady.step (Package.Components.typed a) (SessionCorrespondence.pins startPin)
  let final := started.run im.program false after
  let inputs := started.runtimeInputs im.program false after
  let trace := started.traceRun im.program false {} after
  let pins := PublicPins.driveTrace actualStarted after
  let apertures := 0 :: 0 :: after.map (fun pin => (PublicPins.embed pin).ui.extractLsb' 3 2)
  let cmd := (ready.command startPin).runtime
  let count := cmd.startCount.toNat
  change events mode pins = .select :: edgesFor count ++ [.deselect] ∧
    activePulses mode d.val pins ∧
    (∀ sample ∈ pins, sample.enabled = 7#3) ∧
    trace.accepted = mosiOnLeading mode pins ∧
    trace.exported = misoOnLeading mode pins apertures ∧
    final.host.ackOffset.toNat = count ∧ final.host.exportBits.toNat = 0
  have segment := SessionProof.advance first.reached after ha afterRuntime
  have released : SessionProof.Released final trace :=
    SessionProof.release segment.reached releasePin ha releaseRuntime release
  have coreStart : started.core = ready.core.start im.program cmd := first.coreStart
  have positioned : Positioned mode d started.core :=
    coreStart ▸ positioned_start mode d ready.core cmd
  have ordinary : ∀ i ∈ inputs, Unreleased i := fun i member =>
    ⟨afterRuntime.runtimeInputs im.program false started after i member,noRelease i member⟩
  have retained : (run im.program started.core inputs).phase.retained = true :=
    started.run_core im.program false after ▸ released.retained
  have completed : (run (image mode d).program started.core inputs).phase = .completed := by
    change (run (image mode d).program started.core inputs).phase.retained = true at retained
    rcases (run_schedule mode d started.core inputs positioned ordinary).1.phase with
      phase | (phase | phase | phase) | phase <;> simp [phase,Phase.retained] at retained ⊢
  have complete : (run im.program (ready.core.start im.program cmd) inputs).phase = .completed :=
    coreStart ▸ completed
  have pinsEq : pins = pinTrace im.program started.core inputs := segment.wire
  have traceEq : trace = traceRun im.program started.core {} inputs :=
    started.traceRun_runtimeInputs im.program false {} after
  have aperturesEq : apertures = 0 :: 0 :: inputs.map (·.rawInputs) := by
    unfold apertures inputs
    rw [rawTrace_eq]
  have data := completed_data mode d ready.core cmd inputs ordinary complete
  refine ⟨?_,?_,?_,?_,?_,?_,released.emptyExport⟩
  · rw [pinsEq,coreStart]
    exact completed_exchange mode d ready.core cmd inputs ordinary complete
  · rw [pinsEq]
    exact completed_timing mode d started.core inputs positioned ordinary completed
  · rw [pinsEq]
    exact driven_trace mode d started.core inputs positioned ordinary
  · rw [released.accepted,traceEq,pinsEq,coreStart]
    exact data.1
  · rw [← released.exported,traceEq,pinsEq,aperturesEq,coreStart]
    exact data.2.trans (start_apertures mode d ready.core cmd inputs ordinary)
  · rw [← released.ackOffset,← released.exported,traceEq,coreStart,data.2]
    exact (completed_count mode d ready.core cmd inputs ordinary complete).2

/-- A cold-loaded SPI session uses the same START-to-RELEASE proof. -/
theorem completed_release (mode : Mode) (d : Fin 256)
    (actualBoot : Package.State a) (bootState : Session.State a)
    (initialized : BootCorrespondence.Initialized (image mode d) actualBoot bootState)
    (before : List Session.Pins) (startPin : Session.Pins) (after : List Session.Pins)
    (releasePin : Session.Pins) (ha : a ≤ 3)
    (beforeRuntime : Session.RuntimeTrace (image mode d).program false bootState before) :
    let p := (image mode d).program
    let ready := bootState.run p false before
    let actualReady := actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)
    let started := ready.step p false startPin
    let actualStarted := actualReady.step (Package.Components.typed a) (SessionCorrespondence.pins startPin)
    let final := started.run p false after
    let actualFinal := actualStarted.run (Package.Components.typed a) (after.map SessionCorrespondence.pins)
    let inputs := started.runtimeInputs p false after
    let trace := started.traceRun p false {} after
    let pins := PublicPins.driveTrace actualStarted after
    let apertures := 0 :: 0 :: after.map (fun pin => (PublicPins.embed pin).ui.extractLsb' 3 2)
    let count := (ready.command startPin).runtime.startCount.toNat
    Session.RuntimeInput ready startPin →
    ActualStart actualReady startPin →
    Session.RuntimeTrace p false started after →
    (∀ i ∈ inputs, i.command ≠ 4#4) →
    Session.RuntimeInput final releasePin →
    ActualRelease actualFinal releasePin →
    events mode pins = .select :: edgesFor count ++ [.deselect] ∧
    activePulses mode d.val pins ∧
    (∀ sample ∈ pins, sample.enabled = 7#3) ∧
    trace.accepted = mosiOnLeading mode pins ∧
    trace.exported = misoOnLeading mode pins apertures ∧
    final.host.ackOffset.toNat = count ∧ final.host.exportBits.toNat = 0 := by
  intro p ready actualReady _ _ _ _ _ _ _ _ _ runtime admitted
  have first := SessionProof.start (image mode d) actualBoot bootState initialized before startPin ha
    beforeRuntime runtime admitted
  exact completed_from_start mode d (Initialization.compiledImage (image mode d))
    actualReady ready startPin first after releasePin ha

end Pinwheel.Hardware.StreamingReady.SPISession
