import Pinwheel.Hardware.StreamingReady.InitializedCustody
import Pinwheel.Hardware.StreamingReady.PublicPins
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
  induction pins generalizing s with
  | nil => simp [PublicPins.driveTrace,PublicPins.drive_eq,Session.State.runtimeInputs,pinTrace]
  | cons i rest ih =>
    have first := SessionCorrespondence.step_correct (Initialization.compiledImage im)
      s i ha runtime.1 structural
    rw [compiled_pending] at first
    simp only [PublicPins.driveTrace,PublicPins.drive_eq,PublicPins.step_eq,first,
      Session.State.runtimeInputs,pinTrace]
    exact congrArg (s.core.pins :: ·) (ih _ runtime.2 (s.step_structural im.program false i structural))

theorem rawTrace_eq (s : Session.State a) (p : Program) (pins : List Session.Pins) :
    (s.runtimeInputs p false pins).map Pinwheel.Program.Streaming.Input.rawInputs =
      pins.map (fun pin => (PublicPins.embed pin).ui.extractLsb' 3 2) := by
  rw [s.runtime_rawInputs]
  apply List.map_congr_left
  intro pin _
  exact (congrArg Pinwheel.Program.Streaming.Session.Pins.rawInputs (PublicPins.physical_embed pin)).symm

/-- Actual START selects the compiled image. Actual RELEASE certifies that both
    streams have been drained, including the last host acknowledgment. -/
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
  dsimp only
  intro startRuntime start afterRuntime noRelease releaseRuntime release
  let im := image mode d
  let ready := bootState.run im.program false before
  let actualReady := actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)
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
  have initial := started_run im actualBoot bootState initialized before startPin [] ha
    beforeRuntime startRuntime start trivial
  have reached := started_run im actualBoot bootState initialized before startPin after ha
    beforeRuntime startRuntime start afterRuntime
  have released := reached.release_all_bits releasePin ha releaseRuntime release
  change trace.accepted = trace.consumed ∧ trace.captured = trace.exported ∧
    trace.exported.length = final.host.ackOffset.toNat ∧ final.host.exportBits.toNat = 0 at released
  have releaseEq := release
  rw [reached.package] at releaseEq
  have acceptedRelease := release_source (Initialization.compiledImage im) final releasePin
    ha releaseRuntime releaseEq
  have admission : ActualStart actualReady startPin := start
  have actualEq : actualReady = SessionCorrespondence.values (Initialization.compiledImage im) ready :=
    initialized_run_eq im actualBoot bootState initialized before ha beforeRuntime
  rw [actualEq] at admission
  have acceptedStart := start_source (Initialization.compiledImage im) ready startPin startRuntime admission
  have coreStart : started.core = ready.core.start im.program cmd :=
    ready.core_admitted_start im.program false startPin startRuntime acceptedStart
  have positioned : Positioned mode d started.core :=
    coreStart ▸ positioned_start mode d ready.core cmd
  have ordinary : ∀ i ∈ inputs, Unreleased i := fun i member =>
    ⟨afterRuntime.runtimeInputs im.program false started after i member,noRelease i member⟩
  have retained : (run im.program started.core inputs).phase.retained = true := by
    have admitted := acceptedRelease.2
    simp only [State.canRelease,Bool.and_eq_true] at admitted
    exact started.run_core im.program false after ▸ admitted.1.1
  have completed : (run (image mode d).program started.core inputs).phase = .completed := by
    change (run (image mode d).program started.core inputs).phase.retained = true at retained
    rcases (run_schedule mode d started.core inputs positioned ordinary).1.phase with
      phase | (phase | phase | phase) | phase <;> simp [phase,Phase.retained] at retained ⊢
  have complete : (run im.program (ready.core.start im.program cmd) inputs).phase = .completed :=
    coreStart ▸ completed
  have initialEq : actualStarted =
      SessionCorrespondence.values (Initialization.compiledImage im) started := initial.package
  have pinsEq : pins = pinTrace im.program started.core inputs := by
    unfold pins
    rw [initialEq]
    exact driveTrace_eq im started after ha afterRuntime initial.custody.structural
  have traceEq : trace = traceRun im.program started.core {} inputs :=
    started.traceRun_runtimeInputs im.program false {} after
  have aperturesEq : apertures = 0 :: 0 :: inputs.map (·.rawInputs) := by
    unfold apertures inputs
    rw [rawTrace_eq]
  have data := completed_data mode d ready.core cmd inputs ordinary complete
  refine ⟨?_,?_,?_,?_,?_,?_,released.2.2.2⟩
  · rw [pinsEq,coreStart]
    exact completed_exchange mode d ready.core cmd inputs ordinary complete
  · rw [pinsEq]
    exact completed_timing mode d started.core inputs positioned ordinary completed
  · rw [pinsEq]
    exact driven_trace mode d started.core inputs positioned ordinary
  · rw [released.1,traceEq,pinsEq,coreStart]
    exact data.1
  · rw [← released.2.1,traceEq,pinsEq,aperturesEq,coreStart]
    exact data.2.trans (start_apertures mode d ready.core cmd inputs ordinary)
  · rw [← released.2.2.1,← released.2.1,traceEq,coreStart,data.2]
    exact (completed_count mode d ready.core cmd inputs ordinary complete).2

end Pinwheel.Hardware.StreamingReady.SPISession
