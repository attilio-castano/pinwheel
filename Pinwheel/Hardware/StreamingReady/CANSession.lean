import Pinwheel.Hardware.StreamingReady.InitializedCustody
import Pinwheel.Hardware.StreamingReady.PublicPins
import Pinwheel.Program.StreamingCANCodec
import Pinwheel.Program.StreamingCANCore

/-! Passive Classical CAN reception through the initialized Ready package. -/
namespace Pinwheel.Hardware.StreamingReady.CANSession
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingCANCore Pinwheel.Program.StreamingCAN
open Pinwheel.Hardware.StreamingReady.InitializedCustody

abbrev receiveImage := Pinwheel.Program.StreamingCANCore.image

/-- The exact three words uploaded by the frozen public-pin replay. -/
theorem standard_words : (receiveImage.words, idlePins) = ([1125899906842628, 34359771241, 2], ⟨0, 0⟩) := by
  decide +kernel

def bootPins : List Session.Pins := BootPins.compiled receiveImage 3

set_option maxRecDepth 12000 in
theorem boot (startup : Package.State a) :
    let actual := startup.run (Package.Components.typed a)
      (SessionCorrespondence.pins BootPins.coldPin :: bootPins.map SessionCorrespondence.pins)
    ∃ source : Session.State a,
      BootCorrespondence.Initialized receiveImage actual source ∧ Pipeline receiveImage actual source := by
  apply compiled_session
  apply Pinwheel.Program.Streaming.BootPins.check_sound
  decide +kernel

def rawSamples (pins : List Session.Pins) : List (BitVec 2) :=
  pins.map (fun pin => (PublicPins.embed pin).ui.extractLsb' 3 2)

inductive FrameCase where
  | valid | badStuff | badCRC

def FrameCase.symbols (id : BitVec 11) (data : BitVec 8) : FrameCase → List Bool
  | .valid => frameBits id data
  | .badStuff => badStuffBits id data
  | .badCRC => badCRCBits id data

def FrameCase.decoded (id : BitVec 11) (data : BitVec 8) : FrameCase → Option (BitVec 11 × BitVec 8)
  | .valid => some (id, data)
  | _ => none

/-- After START on a recessive bus, the peer supplies the CAN window. The
package releases every protocol output and captures its 64 slots in order.
The host acknowledges those same bits by the time RELEASE is accepted. -/
theorem completed_frame (actualBoot : Package.State 1) (bootState : Session.State 1)
    (initialized : BootCorrespondence.Initialized receiveImage actualBoot bootState)
    (before : List Session.Pins) (startPin : Session.Pins) (wire drain : List Session.Pins)
    (releasePin : Session.Pins) (beforeRuntime : Session.RuntimeTrace program false bootState before)
    (id : BitVec 11) (data : BitVec 8) (kind : FrameCase) :
    let symbols := kind.symbols id data
    let ready := bootState.run program false before
    let actualReady := actualBoot.run (Package.Components.typed 1) (before.map SessionCorrespondence.pins)
    let started := ready.step program false startPin
    let actualStarted := actualReady.step (Package.Components.typed 1) (SessionCorrespondence.pins startPin)
    let wireEnd := started.run program false wire
    let actualWireEnd := actualStarted.run (Package.Components.typed 1) (wire.map SessionCorrespondence.pins)
    let wireBits := started.traceRun program false {} wire
    let final := wireEnd.run program false drain
    let actualFinal := actualWireEnd.run (Package.Components.typed 1) (drain.map SessionCorrespondence.pins)
    let result := wireEnd.traceRun program false wireBits drain
    let inputs := started.runtimeInputs program false wire
    let drives := PublicPins.driveTrace actualStarted wire
    Session.RuntimeInput ready startPin →
    ActualStart actualReady startPin →
    (ready.command startPin).runtime.startCount = 64#16 →
    startPin.rawInputs.getLsbD 0 = true →
    Session.RuntimeTrace program false started wire →
    (∀ i ∈ inputs, Pinwheel.Program.StreamingUART.QuietTiming.Quiet i) →
    ∀ peer : PeerFrame (rawSamples wire) symbols,
    Session.RuntimeTrace program false wireEnd drain →
    (∀ i ∈ wireEnd.runtimeInputs program false drain, i.command ≠ 4#4) →
    Session.RuntimeInput final releasePin →
    ActualRelease actualFinal releasePin →
    (∀ pad ∈ drives, pad.enabled = 0) ∧
    captureCuts started.core inputs = (apertures peer.fall).map (· + 2) ∧
    wireEnd.core.phase = .completed ∧ result.exported = symbols ∧
    final.host.ackOffset.toNat = 64 ∧ final.host.exportBits.toNat = 0 ∧
    decodeFrame result.exported = kind.decoded id data := by
  intro symbols ready actualReady started actualStarted wireEnd actualWireEnd wireBits final actualFinal result inputs drives
  intro startRuntime start count recessive wireRuntime quiet peer drainRuntime beforeRelease releaseRuntime release
  have initial : Reached receiveImage actualStarted started {} :=
    started_run receiveImage actualBoot bootState initialized before startPin [] (by decide)
      beforeRuntime startRuntime start trivial
  have wired : Reached receiveImage actualWireEnd wireEnd wireBits := initial.run wire (by decide) wireRuntime
  have reached : Reached receiveImage actualFinal final result := wired.run drain (by decide) drainRuntime
  have released := reached.release_all_bits releasePin (by decide) releaseRuntime release
  have readyEq : actualReady = SessionCorrespondence.values (Initialization.compiledImage receiveImage) ready :=
    initialized_run_eq receiveImage actualBoot bootState initialized before (by decide) beforeRuntime
  have admission := start
  rw [readyEq] at admission
  have admitted := start_source (Initialization.compiledImage receiveImage) ready startPin startRuntime admission
  let command := (ready.command startPin).runtime
  have coreStart : started.core = ready.core.start program command :=
    ready.core_admitted_start program false startPin startRuntime admitted
  let raw := inputs.map Pinwheel.Program.Streaming.Input.rawInputs
  have rawEq : raw = rawSamples wire := PublicPins.rawTrace_eq started program false wire
  have inputLength : inputs.length = peer.fall + 2053 := by
    have same := congrArg List.length rawEq
    simpa only [raw, List.length_map, peer.length] using same
  have first : symbols[0]? = some false := by
    cases kind
    · exact frameBits_sof id data
    · exact badStuffBits_sof id data
    · exact badCRCBits_sof id data
  have idle : ∀ k < peer.fall, rawBit raw k = true := by
    rw [rawEq]
    exact peer.idle
  have dominant : rawBit raw peer.fall = false := by
    rw [rawEq]
    exact peer.dominant first
  have frame := run_frame ready.core command inputs peer.fall count quiet recessive idle dominant inputLength
  rcases frame with ⟨completed, captured, allReleased, cuts⟩
  have complete : wireEnd.core.phase = .completed := by
    change (started.run program false wire).core.phase = .completed
    rw [started.run_core, coreStart]
    exact completed
  have wireCapture : wireBits.captured = symbols := by
    change (started.traceRun program false {} wire).captured = _
    rw [started.traceRun_runtimeInputs, coreStart, captured]
    change (apertures peer.fall).map (rawBit raw) = symbols
    rw [rawEq]
    exact peer.samples
  have drainStable := retained_trace program wireEnd.core wireBits (wireEnd.runtimeInputs program false drain)
    (by simp [complete, Phase.retained])
    (fun i member => ⟨drainRuntime.runtimeInputs program false wireEnd drain i member, beforeRelease i member⟩)
  have kept : result.captured = wireBits.captured := by
    change (wireEnd.traceRun program false wireBits drain).captured = _
    rw [wireEnd.traceRun_runtimeInputs]
    exact drainStable.2.2
  have exported : result.exported = symbols := released.2.1.symm.trans (kept.trans wireCapture)
  refine ⟨?_, ?_, complete, exported, ?_, released.2.2.2, ?_⟩
  · change ∀ pad ∈ PublicPins.driveTrace actualStarted wire, pad.enabled = 0
    rw [initial.package]
    have published : PublicPins.driveTrace
        (SessionCorrespondence.values (Initialization.compiledImage receiveImage) started) wire =
        pinTrace program started.core inputs := by
      simpa only [compiled_pending] using PublicPins.driveTrace_eq (Initialization.compiledImage receiveImage)
        started wire (by decide) (by simpa only [compiled_pending] using wireRuntime) initial.custody.structural
    rw [published, coreStart]
    exact allReleased
  · rw [coreStart]
    exact cuts
  · rw [← released.2.2.1, exported, peer.count]
  · rw [exported]
    cases kind <;> simp [symbols, FrameCase.symbols, FrameCase.decoded, decode_frame, decode_badStuff, decode_badCRC]

end Pinwheel.Hardware.StreamingReady.CANSession
