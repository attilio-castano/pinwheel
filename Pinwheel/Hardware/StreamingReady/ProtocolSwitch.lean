import Pinwheel.Hardware.StreamingReady.I2CReadSuccess
import Pinwheel.Hardware.StreamingReady.SPISession

/-! A completed transfer and the next program use successive states of the
same package. The host drains RELEASE, uploads, then starts the new image. -/
namespace Pinwheel.Hardware.StreamingReady.ProtocolSwitch
open Pinwheel.Program Pinwheel.Program.StreamingReady InitializedCustody
open Pinwheel.Hardware.Streaming

/-- The input cuts for an SPI exchange from an already installed program. -/
def SPIInput (mode : StreamingSPI.Mode) (d : Fin 256)
    (actual : Package.State a) (ready : Session.State a)
    (before : List Session.Pins) (start : Session.Pins) (body : List Session.Pins)
    (release : Session.Pins) : Prop :=
  let p := (StreamingSPI.image mode d).program
  let sourceStart := ready.run p false before
  let actualStart := actual.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)
  let sourceBody := sourceStart.step p false start
  let actualBody := actualStart.step (Package.Components.typed a) (SessionCorrespondence.pins start)
  Session.RuntimeTrace p false ready before ∧
  Session.RuntimeInput sourceStart start ∧ ActualStart actualStart start ∧
  Session.RuntimeTrace p false sourceBody body ∧
  (∀ i ∈ sourceBody.runtimeInputs p false body, i.command ≠ 4#4) ∧
  Session.RuntimeInput (sourceBody.run p false body) release ∧
  ActualRelease (actualBody.run (Package.Components.typed a) (body.map SessionCorrespondence.pins)) release

/-- Extend an exact I²C result through its RELEASE edge and a certified warm
    upload into a complete SPI exchange on the same physical package. -/
theorem i2c_to_spi (profile : I2cProfile) (actual : Package.State a) (started : Session.State a)
    (frame drain : List Session.Pins) (release : Session.Pins)
    (payload : List (BitVec 8)) (peer : Nat → Pinwheel.I2C.Pins)
    (read : I2CReadSuccess.Result profile actual started frame drain release payload peer)
    (mode : StreamingSPI.Mode) (d : Fin 256) (upload before body : List Session.Pins)
    (startSPI releaseSPI : Session.Pins) (ha : a ≤ 3) :
    let old := i2cImage profile
    let next := StreamingSPI.image mode d
    let oldRep := Initialization.compiledImage old
    let rep := Initialization.compiledImageFrom next (Initialization.installedMetadata oldRep)
    let final := (started.run old.program false frame).run old.program false drain
    let actualFinal := (actual.run (Package.Components.typed a) (frame.map SessionCorrespondence.pins)).run
      (Package.Components.typed a) (drain.map SessionCorrespondence.pins)
    let sourceFree := final.step old.program false release
    let actualFree := actualFinal.step (Package.Components.typed a) (SessionCorrespondence.pins release)
    let replacement := actualFree.run (Package.Components.typed a) (upload.map SessionCorrespondence.pins)
    final.core.generation ≠ 65535#16 →
    BootPins.Certified next.words (StreamingSPI.idlePins mode)
      (Pinwheel.Program.Streaming.Host.BootControl.project sourceFree.host) 0 false upload →
    (∀ source, BootCorrespondence.Ready next rep replacement source →
      SPIInput mode d replacement source before startSPI body releaseSPI) →
    ∃ source,
      BootCorrespondence.Ready next rep replacement source ∧
      source.core.generation = final.core.generation + 1 ∧ source.core.transfer = final.core.transfer ∧
      SPISession.Exchange mode d
        (replacement.run (Package.Components.typed a) (before.map SessionCorrespondence.pins))
        (source.run next.program false before) startSPI body := by
  intro old next oldRep rep final actualFinal sourceFree actualFree replacement room certified spi
  have released := SessionProof.release_to_free read.reached release ha read.releaseRuntime read.admitted
  obtain ⟨source, ready, generation, transfer⟩ := BootCorrespondence.reload_after_release next oldRep
    actualFree sourceFree final.core (final.command release).runtime released.package released.core upload certified room
  obtain ⟨beforeRuntime, startRuntime, startAdmitted, bodyRuntime, noRelease, releaseRuntime, releaseAdmitted⟩ :=
    spi source ready
  have first := SessionProof.start_from next rep replacement source ready before startSPI ha
    beforeRuntime startRuntime startAdmitted
  exact ⟨source, ready, generation, transfer, SPISession.completed_from_start mode d rep
    _ _ startSPI first body releaseSPI ha bodyRuntime noRelease releaseRuntime releaseAdmitted⟩

end Pinwheel.Hardware.StreamingReady.ProtocolSwitch
