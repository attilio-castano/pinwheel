import StreamingReadyTypedEngine
import Pinwheel.Hardware.StreamingReady.EthernetRefill

/-! The host prelude and wire observations of Ethernet use the reconstructed
depth-two engine and the same physical pin map as the independent PHY. -/
namespace Pinwheel.Artifact.StreamingReadyTypedEthernet

open Pinwheel.Hardware.StreamingReady Pinwheel.Program
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingEthernetSchedule
open Pinwheel.Program.StreamingEthernetFrame Pinwheel.Program.StreamingEthernetCore
open StreamingEthernetRefill (Policy Executed checkCredit alignmentPins activePins complete uniform staggered
  uniform_executed uniform_credit staggered_executed staggered_credit)
open StreamingReadyTypedEngine

def beforeWire (startup : Package.State addrBits) : Package.State addrBits :=
  let booted := physicalRun startup ((BootPins.coldPin :: bootPins).map PublicPins.embed)
  let ready := physicalRun booted (beforeStart.map PublicPins.embed)
  let started := physicalStep ready (PublicPins.embed startPin)
  physicalRun started (afterStart.map PublicPins.embed)

theorem beforeWire_correct (startup : Package.State addrBits) :
    beforeWire startup = EthernetSession.beforeWire startup := by
  simp only [beforeWire, EthernetSession.beforeWire, EthernetSession.afterBoot, physical_run_correct,
    embedded_engine_pins, List.map_cons, physical_step_correct, PublicPins.engine_embed]

def wireTrace (startup : Package.State addrBits) (policy : Policy) (highWidth : Nat) :=
  let aligned := physicalRun (beforeWire startup) ((alignmentPins policy highWidth).map PublicPins.embed)
  publicDriveTrace aligned ((activePins policy highWidth).map PublicPins.embed)

theorem wire_exact (startup : Package.State addrBits) (policy : Policy) (highWidth : Nat)
    (execution : StreamingEthernetRefill.Executed policy highWidth) (credit : checkCredit policy highWidth = true) :
    wireTrace startup policy highWidth = frameBits.flatMap cellPins ++ [txPins false, idlePins] := by
  simpa only [wireTrace, physical_run_correct, embedded_engine_pins, beforeWire_correct,
    publicDriveTrace_correct] using EthernetRefill.wire_exact startup policy highWidth execution credit

theorem uniform_wire (startup : Package.State addrBits) (highWidth : Nat)
    (legal : highWidth = 1 ∨ highWidth = 2) :
    wireTrace startup uniform highWidth = frameBits.flatMap cellPins ++ [txPins false, idlePins] :=
  wire_exact startup uniform highWidth (uniform_executed legal) (uniform_credit legal)

theorem staggered_wire (startup : Package.State addrBits) (highWidth : Nat)
    (legal : highWidth = 1 ∨ highWidth = 2) :
    wireTrace startup staggered highWidth = frameBits.flatMap cellPins ++ [txPins false, idlePins] :=
  wire_exact startup staggered highWidth (staggered_executed legal) (staggered_credit legal)

theorem owner_released (startup : Package.State addrBits) (policy : Policy) (highWidth : Nat)
    (execution : Executed policy highWidth) :
    let wireEnd := physicalRun (beforeWire startup)
      ((StreamingEthernetRefill.bodyPins policy highWidth).map PublicPins.embed)
    let after := physicalRun wireEnd ((releaseClocked highWidth).map PublicPins.embed)
    let done := complete policy highWidth
    let freed := StreamingEthernetRefill.released policy highWidth
    wireEnd = SessionCorrespondence.values (Initialization.compiledImage image) done ∧
    after = SessionCorrespondence.values (Initialization.compiledImage image) freed ∧
    done.core.phase = .completed ∧ done.core.drained = true ∧
    done.core.txAccepted = 576 ∧ done.core.txConsumed = 576 ∧
    freed.core.phase = .free ∧ freed.core.transfer = 1 ∧ freed.host.code = 0 := by
  simpa only [physical_run_correct, embedded_engine_pins, beforeWire_correct] using
    EthernetRefill.owner_released startup policy highWidth execution

end Pinwheel.Artifact.StreamingReadyTypedEthernet
