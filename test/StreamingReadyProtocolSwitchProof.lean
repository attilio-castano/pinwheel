import StreamingReadyTxShiftProof
import Pinwheel.Hardware.StreamingReady.ProtocolSwitch
import Pinwheel.Hardware.StreamingReady.StaleStart

namespace Pinwheel.Artifact.StreamingReadyProtocolSwitch
open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady
open Pinwheel.Program Pinwheel.Program.StreamingReady
open StreamingReadySessionD2 StreamingReadyTxShift

/-- The two reconstructed layouts execute the read, RELEASE, loader and SPI
    histories on one package, with equal public observations at every cut. -/
theorem i2c_to_spi (profile : I2cProfile) (l r : Package.State 1) (started : Session.State 1)
    (related : TxShiftPackage.Related l r) (frame drain : List Session.Pins) (release : Session.Pins)
    (payload : List (BitVec 8)) (peer : Nat → Pinwheel.I2C.Pins)
    (read : I2CReadSuccess.Result profile r started frame drain release payload peer)
    (mode : StreamingSPI.Mode) (d : Fin 256) (upload before body : List Session.Pins)
    (startSPI releaseSPI : Session.Pins) :
    let old := i2cImage profile
    let next := StreamingSPI.image mode d
    let rep := Initialization.compiledImageFrom next (Initialization.installedMetadata (Initialization.compiledImage old))
    let final := (started.run old.program false frame).run old.program false drain
    let sourceFree := final.step old.program false release
    let reloadPins := frame ++ drain ++ release :: upload
    let replacement := physicalRun r (reloadPins.map PublicPins.embed)
    final.core.generation ≠ 65535#16 →
    BootPins.Certified next.words (StreamingSPI.idlePins mode)
      (Pinwheel.Program.Streaming.Host.BootControl.project sourceFree.host) 0 false upload →
    (∀ source, BootCorrespondence.Ready next rep replacement source →
      ProtocolSwitch.SPIInput mode d replacement source before startSPI body releaseSPI) →
    ∃ source,
      BootCorrespondence.Ready next rep replacement source ∧
      source.core.generation = final.core.generation + 1 ∧ source.core.transfer = final.core.transfer ∧
      SPISession.Exchange mode d (physicalRun replacement (before.map PublicPins.embed))
        (source.run next.program false before) startSPI body ∧
      PublicRun l r (reloadPins ++ before ++ startSPI :: (body ++ [releaseSPI])) := by
  intro old next rep final sourceFree reloadPins replacement room certified spi
  have atReload := public_run l r reloadPins related
  have installed : replacement =
      ((((r.run (Package.Components.typed 1) (frame.map SessionCorrespondence.pins)).run
        (Package.Components.typed 1) (drain.map SessionCorrespondence.pins)).step
        (Package.Components.typed 1) (SessionCorrespondence.pins release)).run
        (Package.Components.typed 1) (upload.map SessionCorrespondence.pins)) := by
    dsimp only [replacement]
    rw [atReload.ringState]
    simp only [reloadPins, List.map_append, List.map_cons, List.foldl_append, List.foldl_cons,
      Package.State.run, Pinwheel.Hardware.Streaming.Package.State.run]
  have drive := ProtocolSwitch.i2c_to_spi profile r started frame drain release payload peer read
    mode d upload before body startSPI releaseSPI (by decide) room certified
  rw [← installed] at drive
  obtain ⟨source, ready, generation, transfer, exchange⟩ := drive spi
  rw [physical_run_correct, embedded_engine_pins]
  exact ⟨source, ready, generation, transfer, exchange, public_run _ _ _ related⟩

/-- A stale delivered START raises rejection on both reconstructed cores.
    The ring cut retains its image generation, owner counter and the pad drive;
    package simulation lifts preservation of the public pads to shift. -/
theorem rejects_stale_start (rep : SourceRefinement.Image p) (l r : Package.State 1)
    (s : Session.State 1) (pin : Session.Pins) (related : TxShiftPackage.Related l r)
    (represented : r = SessionCorrespondence.values rep s) (structural : s.core.Structural)
    (free : s.core.phase = .free) (runtime : Session.RuntimeInput s pin)
    (start : (s.command pin).runtime.command = 3#4)
    (stale : (s.command pin).runtime.expectedGeneration ≠ s.core.generation) :
    let pins := SessionCorrespondence.pins pin
    let after := physicalStep r (PublicPins.embed pin)
    r.status ring pins .rejected = 1#1 ∧ l.status shift pins .rejected = 1#1 ∧
    after.core .phase = 0#3 ∧ after.core .generation = s.core.generation ∧
    after.core .transfer = s.core.transfer ∧
    after.core .levels = s.core.pins.levels ∧ after.core .enabled = s.core.pins.enabled ∧
    PublicRun l r [pin] := by
  dsimp only
  have denied := stale_start_rejected rep r s pin (by decide) represented structural free runtime start stale
  have same := congrArg (fun status : Values StreamingReady.Core.Output => status .rejected)
    (simulates.status_eq (SessionCorrespondence.pins pin) related)
  have ringRejected : r.status ring (SessionCorrespondence.pins pin) .rejected = 1#1 := by
    rw [ring_correct]
    exact denied.1
  rw [physical_step_correct, PublicPins.engine_embed]
  exact ⟨ringRejected, same.trans ringRejected, denied.2.1, denied.2.2.1,
    denied.2.2.2.1, denied.2.2.2.2.1, denied.2.2.2.2.2, public_run _ _ _ related⟩

end Pinwheel.Artifact.StreamingReadyProtocolSwitch
