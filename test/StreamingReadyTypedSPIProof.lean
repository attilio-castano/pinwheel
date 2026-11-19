import StreamingReadyTypedEngine
import Pinwheel.Hardware.StreamingReady.SPISession

/-! The generated Ready certificate supplies the two-state pad transition and observation.
This join applies the SPI session proof to that reconstructed digital device. -/
namespace Pinwheel.Artifact.StreamingReadyTypedSPI

open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady
open Pinwheel.Hardware.StreamingReady.InitializedCustody
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingSPI
open StreamingReadyTypedEngine

theorem boot (mode : Mode) (startup : Package.State addrBits) :
    let actual := physicalRun startup ((BootPins.coldPin :: SPISession.bootPins mode).map PublicPins.embed)
    ∃ source : Session.State addrBits,
      BootCorrespondence.Initialized (image mode 3) actual source ∧ Pipeline (image mode 3) actual source := by
  simpa only [physical_run_correct, embedded_engine_pins, PublicPins.engine_embed, List.map_cons] using
    SPISession.boot mode startup

/-- The START-to-RELEASE contract for the independently reconstructed SPI artifact. -/
theorem completed_release (mode : Mode) (d : Fin 256)
    (actualBoot : Package.State addrBits) (bootState : Session.State addrBits)
    (initialized : BootCorrespondence.Initialized (image mode d) actualBoot bootState)
    (before : List Session.Pins) (startPin : Session.Pins) (after : List Session.Pins)
    (releasePin : Session.Pins)
    (beforeRuntime : Session.RuntimeTrace (image mode d).program false bootState before) :
    let p := (image mode d).program
    let ready := bootState.run p false before
    let actualReady := physicalRun actualBoot (before.map PublicPins.embed)
    let started := ready.step p false startPin
    let actualStarted := physicalStep actualReady (PublicPins.embed startPin)
    let final := started.run p false after
    let actualFinal := physicalRun actualStarted (after.map PublicPins.embed)
    let inputs := started.runtimeInputs p false after
    let trace := started.traceRun p false {} after
    let replayPins := after.map PublicPins.embed
    let pins := publicDriveTrace actualStarted replayPins
    let apertures := 0 :: 0 :: replayPins.map (fun pin => pin.ui.extractLsb' 3 2)
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
  simpa only [physical_run_correct, embedded_engine_pins, physical_step_correct, PublicPins.engine_embed,
    publicDriveTrace_correct, List.map_map, Function.comp_def] using
    SPISession.completed_release mode d actualBoot bootState initialized before startPin after releasePin
      (by decide) beforeRuntime

end Pinwheel.Artifact.StreamingReadyTypedSPI
