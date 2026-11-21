import StreamingReadyTypedEngine
import Pinwheel.Hardware.StreamingReady.I2CReadSession

/-! Transport the standard I²C read and sampler deadline to the reconstructed digital pads. -/
namespace Pinwheel.Artifact.StreamingReadyTypedI2C

open Pinwheel.Hardware.StreamingReady Pinwheel.Hardware.StreamingReady.InitializedCustody
open Pinwheel.Program Pinwheel.Program.StreamingReady
open StreamingReadyTypedEngine

private abbrev image := I2CReadSession.image

/-- Before each edge the raw input is the resolution of the actual pad drive with the peer. -/
def PublicConnection (actual : Package.State addrBits) (pins : List Session.Pins)
    (peer : Nat → Pinwheel.I2C.Pins) : Prop :=
  ∀ k < pins.length, (I2CReadSession.rawSamples pins)[k]? =
    ((publicDriveTrace actual (pins.map PublicPins.embed))[k]?).map (fun drive =>
      StreamingI2CRead.resolvedRaw drive (peer k))

theorem publicConnection_correct (actual : Package.State addrBits) (pins : List Session.Pins)
    (peer : Nat → Pinwheel.I2C.Pins) :
    PublicConnection actual pins peer ↔ I2CReadSession.PublicConnection actual pins peer := by
  simp only [PublicConnection, I2CReadSession.PublicConnection, publicDriveTrace_correct]

theorem boot (startup : Package.State addrBits) :
    ∃ source : Session.State addrBits,
      BootCorrespondence.Initialized image (physicalRun startup i2cBootPins) source ∧
      PhysicalCustody image (physicalRun startup i2cBootPins) source :=
  concrete_i2c_custody startup

/-- The last allowed poll captures an SDA sample from the reconstructed pins. -/
theorem last_poll (actual : Package.State addrBits) (s : Session.State addrBits) (trace : BitTrace)
    (reached : Reached image actual s trace)
    (entry : StreamingI2CDeadline.WaitEntry s.core) (pins : List Session.Pins)
    (length : pins.length = 31) (sda : Pinwheel.I2C.Drive)
    (runtime : Session.RuntimeTrace image.program false s pins)
    (resolved : PublicConnection actual pins (StreamingI2CDeadline.target 28 sda)) :
    let final := s.run image.program false pins
    let finalActual := physicalRun actual (pins.map PublicPins.embed)
    let result := s.traceRun image.program false trace pins
    Reached image finalActual final result ∧
    StreamingI2CDeadline.CaptureResult s.core final.core trace result
      (StreamingI2CRead.resolvedRaw (publicDrive actual)
        (StreamingI2CDeadline.target 28 sda 28))[1] := by
  simpa only [physical_run_correct, embedded_engine_pins, publicDrive_correct] using
    I2CReadSession.last_poll actual s trace reached entry pins length sda (by decide) runtime
      ((publicConnection_correct _ _ _).mp resolved)

/-- The one-poll-late wire rise times out and retains exactly the captured prefix. -/
theorem one_poll_late (actual : Package.State addrBits) (s : Session.State addrBits) (trace : BitTrace)
    (reached : Reached image actual s trace)
    (entry : StreamingI2CDeadline.WaitEntry s.core) (pins : List Session.Pins)
    (length : pins.length = 31) (sda : Pinwheel.I2C.Drive)
    (runtime : Session.RuntimeTrace image.program false s pins)
    (resolved : PublicConnection actual pins (StreamingI2CDeadline.target 29 sda)) :
    let final := s.run image.program false pins
    let finalActual := physicalRun actual (pins.map PublicPins.embed)
    let result := s.traceRun image.program false trace pins
    Reached image finalActual final result ∧
    StreamingI2CDeadline.TimeoutResult s.core final.core trace result ∧
    (∀ k < 31, ((I2CReadSession.rawSamples pins)[k]?).map (fun raw => raw.getLsbD 0) =
      some (decide (29 ≤ k))) := by
  simpa only [physical_run_correct, embedded_engine_pins] using
    I2CReadSession.one_poll_late actual s trace reached entry pins length sda (by decide) runtime
      ((publicConnection_correct _ _ _).mp resolved)

/-- A completed 64-byte read on the reconstructed wrapper exports the resolved wire data. -/
theorem completed_read (actualBoot : Package.State addrBits) (boot : Session.State addrBits)
    (initialized : BootCorrespondence.Initialized image actualBoot boot)
    (before : List Session.Pins) (startPin : Session.Pins) (after : List Session.Pins)
    (releasePin : Session.Pins)
    (beforeRuntime : Session.RuntimeTrace image.program false boot before)
    (payload : List (BitVec 8)) (size : payload.length = 64)
    (peer : Nat → Pinwheel.I2C.Pins) :
    let p := image.program
    let ready := boot.run p false before
    let actualReady := physicalRun actualBoot (before.map PublicPins.embed)
    let started := ready.step p false startPin
    let actualStarted := physicalStep actualReady (PublicPins.embed startPin)
    let final := started.run p false after
    let actualFinal := physicalRun actualStarted (after.map PublicPins.embed)
    let inputs := started.runtimeInputs p false after
    let trace := started.traceRun p false {} after
    Session.RuntimeInput ready startPin →
    ActualStart actualReady startPin →
    (ready.command startPin).runtime.startCount = 585#16 →
    Session.RuntimeTrace p false started after →
    (∀ i ∈ inputs, i.command ≠ 4#4) →
    PublicConnection actualStarted after peer →
    StreamingI2CTrace.ReadPeer started.core inputs payload peer →
    final.core.phase = .completed →
    trace.accepted = StreamingI2CRead.hostBits →
    Session.RuntimeInput final releasePin →
    ActualRelease actualFinal releasePin →
    publicDriveTrace actualStarted (after.map PublicPins.embed) = pinTrace p started.core inputs ∧
    StreamingI2CTrace.frameEvents started.core inputs =
      [.start] ++ List.replicate 585 .slot ++ [.stop] ∧
    StreamingI2CTrace.ResolvedFraming started.core inputs peer ∧
    trace.exported = StreamingI2CRead.wireBits payload ∧
    StreamingI2CRead.project trace.exported = some payload ∧
    final.host.ackOffset.toNat = 585 ∧ final.host.exportBits.toNat = 0 := by
  simpa only [physical_run_correct, embedded_engine_pins, physical_step_correct, PublicPins.engine_embed,
    publicDriveTrace_correct, publicConnection_correct] using
    I2CReadSession.completed_read actualBoot boot initialized before startPin after releasePin
      (by decide) beforeRuntime payload size peer

end Pinwheel.Artifact.StreamingReadyTypedI2C
