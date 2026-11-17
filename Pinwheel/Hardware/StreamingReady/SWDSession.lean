import Pinwheel.Hardware.StreamingReady.InitializedCustody
import Pinwheel.Hardware.StreamingReady.PublicPins
import Pinwheel.Program.StreamingSWDData

/-! The fixed SWD read on the initialized package and an independently
clocked target on a push-pull shared wire. -/
namespace Pinwheel.Hardware.StreamingReady.SWDSession
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingSWD
open Pinwheel.Hardware.StreamingReady.InitializedCustody

abbrev readImage := image 3

/-- These are the words uploaded by the frozen public-pin replay. -/
theorem standard_words : (readImage.words, idlePins) =
    ([919607320,851449880,919607320,851449880,851449880,919607320,851449880,919607320,
      306190360,43255863321,306190360,851449880,851449880,851449880,851449880,
      851449880,851449880,851449880,851449880,2],⟨0,1⟩) := by
  decide +kernel

def bootPins : List Session.Pins := BootPins.compiled readImage 0

set_option maxRecDepth 12000 in
theorem boot (startup : Package.State a) :
    let actual := startup.run (Package.Components.typed a)
      (SessionCorrespondence.pins BootPins.coldPin :: bootPins.map SessionCorrespondence.pins)
    ∃ source : Session.State a,
      BootCorrespondence.Initialized readImage actual source ∧ Pipeline readImage actual source := by
  apply compiled_session
  apply Pinwheel.Program.Streaming.BootPins.check_sound
  decide +kernel

def rawSamples (pins : List Session.Pins) : List (BitVec 2) :=
  pins.map (fun pin => (PublicPins.embed pin).ui.extractLsb' 3 2)

def hostDrive (pins : Pins) : Option Bool :=
  if pins.enabled[1] then some pins.levels[1] else none

/-- The target launches the first ACK bit after the ninth rising edge. Each
    reply edge advances one bit, and the parity edge releases SWDIO. -/
def targetDrive (reply : List Bool) (seen : Nat) : Option Bool :=
  if 9 ≤ seen ∧ seen < 45 then reply[seen - 9]? else none

def wireValue : Option Bool → Option Bool → Option Bool
  | none, target => target
  | host, none => host
  | some _, some _ => none

def sampleLinks (pads : List Pins) (raw : List (BitVec 2)) (reply : List Bool) : Prop :=
  ∀ k < raw.length, ∀ bit,
    wireValue (hostDrive (pads[k]?.getD {}))
      (targetDrive reply ((risesSeen pads)[k]?.getD 0)) = some bit →
    ((raw[k]?).getD 0).getLsbD 1 = bit

def uncontended (pads : List Pins) (reply : List Bool) : Prop :=
  ∀ k < pads.length,
    hostDrive (pads[k]?.getD {}) = none ∨
      targetDrive reply ((risesSeen pads)[k]?.getD 0) = none

private def refPins : List Pins := reference.map Pose.pins

private theorem reference_releases : ((refPins.zip (risesSeen refPins)).all fun observation =>
    !(decide (9 ≤ observation.2 ∧ observation.2 < 45) && observation.1.enabled[1])) = true := by
  decide +kernel

private theorem reference_released_at (k : Nat) (inside : k < refPins.length)
    (window : 9 ≤ ((risesSeen refPins)[k]?.getD 0) ∧ ((risesSeen refPins)[k]?.getD 0) < 45) :
    hostDrive (refPins[k]?.getD {}) = none := by
  have countBound : k < (risesSeen refPins).length := by simpa only [risesSeen_length] using inside
  have index : k < (refPins.zip (risesSeen refPins)).length := by
    simpa only [List.length_zip,risesSeen_length,Nat.min_self] using inside
  have checked := List.all_eq_true.mp reference_releases _ (List.getElem_mem index)
  rw [List.getElem_zip] at checked
  rw [List.getElem?_eq_getElem countBound] at window
  simp only [Option.getD_some] at window
  have active : decide (9 ≤ (risesSeen refPins)[k]'countBound ∧
      (risesSeen refPins)[k]'countBound < 45) = true :=
    decide_eq_true window
  simp only [active,Bool.true_and,Bool.not_eq_true'] at checked
  rw [List.getElem?_eq_getElem inside,Option.getD_some,hostDrive,checked]
  rfl

theorem reference_uncontended (reply : List Bool) : uncontended refPins reply := by
  intro k inside
  by_cases window : 9 ≤ ((risesSeen refPins)[k]?.getD 0) ∧ ((risesSeen refPins)[k]?.getD 0) < 45
  · exact Or.inl (reference_released_at k inside window)
  · exact Or.inr (by simp [targetDrive,window])

private theorem pinLength : refPins.length = clockCount + 1 := by
  decide +kernel

private theorem clockDriven : (refPins.all fun pins => pins.enabled[0]) = true := by
  decide +kernel

private def preRise (pads : List Pins) (edge : Nat) : Option Bool × Nat :=
  let k := (risingCuts pads)[edge]?.getD 0
  (hostDrive (pads[k]?.getD {}),(risesSeen pads)[k]?.getD 0)

/-- Both endpoints release SWDIO at the sampling point of a turnaround clock. -/
def turnaroundReleased (pads : List Pins) (reply : List Bool) (edge : Nat) : Prop :=
  let before := preRise pads edge
  before.1 = none ∧ targetDrive reply before.2 = none

private theorem reference_turnarounds (reply : List Bool) :
    turnaroundReleased refPins reply 8 ∧ turnaroundReleased refPins reply 45 := by
  have first : preRise refPins 8 = (none,8) := by decide +kernel
  have second : preRise refPins 45 = (none,45) := by decide +kernel
  simp [turnaroundReleased,first,second,targetDrive]

theorem linked_reply (raw : List (BitVec 2)) (reply : List Bool) (size : reply.length = 36)
    (length : raw.length = clockCount) (link : sampleLinks refPins raw reply) :
    responseSamples raw = reply := by
  apply response_of_peer reply raw size
  intro k inside first last
  let seen := referenceSeenAt k
  have window : 9 ≤ seen ∧ seen < 45 := ⟨first,last⟩
  have pinBound : k < refPins.length := by rw [pinLength]; omega
  have released := reference_released_at k pinBound window
  have bitBound : seen - 9 < reply.length := by rw [size]; omega
  have driven : wireValue (hostDrive (refPins[k]?.getD {}))
      (targetDrive reply seen) = some reply[seen - 9] := by
    rw [released,targetDrive,if_pos window,wireValue,List.getElem?_eq_getElem bitBound]
  have rawBound : k < raw.length := length.symm ▸ inside
  have linked := link k rawBound reply[seen - 9] driven
  change (raw[k]?.getD 0).getLsbD 1 = reply[seen - 9]?.getD false
  rw [List.getElem?_eq_getElem bitBound]
  exact linked

def reply (value : BitVec 32) : Bool → List Bool
  | true => replyBits value
  | false => badParityBits value

/-- The settled point-to-point peer clocks ACK, data and parity on the
    shared line. Draining the two RX chunks preserves the sampled reply. -/
theorem completed_read (actualBoot : Package.State 1) (bootState : Session.State 1)
    (initialized : BootCorrespondence.Initialized readImage actualBoot bootState)
    (before : List Session.Pins) (startPin : Session.Pins) (wire drain : List Session.Pins)
    (releasePin : Session.Pins)
    (beforeRuntime : Session.RuntimeTrace program false bootState before)
    (value : BitVec 32) (parityOK : Bool) :
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
    (ready.command startPin).runtime.startCount = 36#16 →
    Session.RuntimeTrace program false started wire →
    (∀ i ∈ inputs, Pinwheel.Program.StreamingUART.QuietTiming.Quiet i) →
    wire.length = clockCount →
    sampleLinks drives (rawSamples wire) (reply value parityOK) →
    Session.RuntimeTrace program false wireEnd drain →
    (∀ i ∈ wireEnd.runtimeInputs program false drain, i.command ≠ 4#4) →
    Session.RuntimeInput final releasePin →
    ActualRelease actualFinal releasePin →
    rises drives = requestBits.map some ++ List.replicate 38 none ++ List.replicate 8 (some false) ∧
    (∀ pad ∈ drives, pad.enabled[0] = true) ∧
    turnaroundReleased drives (reply value parityOK) 8 ∧
    turnaroundReleased drives (reply value parityOK) 45 ∧
    uncontended drives (reply value parityOK) ∧
    wireEnd.core.phase = .completed ∧ result.exported = reply value parityOK ∧
    final.host.ackOffset.toNat = 36 ∧ final.host.exportBits.toNat = 0 ∧
    decodeReply result.exported = (if parityOK then some value else none) := by
  intro ready actualReady started actualStarted wireEnd actualWireEnd wireBits final actualFinal result inputs drives
  intro startRuntime start count wireRuntime quiet length linked drainRuntime beforeRelease releaseRuntime release
  have initial : Reached readImage actualStarted started {} :=
    started_run readImage actualBoot bootState initialized before startPin [] (by decide)
      beforeRuntime startRuntime start trivial
  have wired : Reached readImage actualWireEnd wireEnd wireBits :=
    initial.run wire (by decide) wireRuntime
  have reached : Reached readImage actualFinal final result := wired.run drain (by decide) drainRuntime
  have released := reached.release_all_bits releasePin (by decide) releaseRuntime release
  have readyEq : actualReady = SessionCorrespondence.values (Initialization.compiledImage readImage) ready :=
    initialized_run_eq readImage actualBoot bootState initialized before (by decide) beforeRuntime
  have admission := start
  rw [readyEq] at admission
  have admitted := start_source (Initialization.compiledImage readImage) ready startPin startRuntime admission
  let command := (ready.command startPin).runtime
  have coreStart : started.core = ready.core.start program command :=
    ready.core_admitted_start program false startPin startRuntime admitted
  have rawEq : inputs.map Pinwheel.Program.Streaming.Input.rawInputs = rawSamples wire :=
    PublicPins.rawTrace_eq started program false wire
  have inputLength : inputs.length = clockCount := by
    have same := congrArg List.length rawEq
    simpa only [rawSamples,List.length_map,length] using same
  have control : poses started.core inputs = reference := by
    rw [coreStart]
    exact quiet_poses ready.core command inputs count quiet inputLength
  have complete : wireEnd.core.phase = .completed := by
    change (started.run program false wire).core.phase = .completed
    rw [started.run_core,coreStart]
    exact quiet_completed ready.core command inputs count quiet inputLength
  have publicEq : drives = reference.map Pose.pins := by
    change PublicPins.driveTrace actualStarted wire = _
    rw [initial.package]
    have published : PublicPins.driveTrace
        (SessionCorrespondence.values (Initialization.compiledImage readImage) started) wire =
        pinTrace program started.core inputs := by
      simpa only [compiled_pending] using PublicPins.driveTrace_eq (Initialization.compiledImage readImage)
        started wire (by decide) (by simpa only [compiled_pending] using wireRuntime) initial.custody.structural
    rw [published,← poses_pins,control]
  have linkedRef := linked
  rw [publicEq] at linkedRef
  have size : (reply value parityOK).length = 36 := by cases parityOK <;> simp [reply]
  have recovered := linked_reply (rawSamples wire) (reply value parityOK) size
    (by simpa only [rawSamples,List.length_map] using length) linkedRef
  have wireCapture : wireBits.captured = reply value parityOK := by
    change (started.traceRun program false {} wire).captured = _
    rw [started.traceRun_runtimeInputs,captured_of_poses started.core inputs quiet control,rawEq]
    exact recovered
  have drainStable := retained_trace program wireEnd.core wireBits (wireEnd.runtimeInputs program false drain)
    (by simp [complete,Phase.retained])
    (fun i member => ⟨drainRuntime.runtimeInputs program false wireEnd drain i member,beforeRelease i member⟩)
  have kept : result.captured = wireBits.captured := by
    change (wireEnd.traceRun program false wireBits drain).captured = _
    rw [wireEnd.traceRun_runtimeInputs]
    exact drainStable.2.2
  have exported : result.exported = reply value parityOK :=
    released.2.1.symm.trans (kept.trans wireCapture)
  have turns := reference_turnarounds (reply value parityOK)
  refine ⟨?_,?_,?_,?_,?_,complete,exported,?_,released.2.2.2,?_⟩
  · rw [publicEq]
    exact reference_rises
  · rw [publicEq]
    exact List.all_eq_true.mp clockDriven
  · rw [publicEq]
    exact turns.1
  · rw [publicEq]
    exact turns.2
  · rw [publicEq]
    exact reference_uncontended _
  · rw [← released.2.2.1,exported,size]
  · rw [exported]
    cases parityOK <;> simp [reply,decode_reply,decode_badParity]

end Pinwheel.Hardware.StreamingReady.SWDSession
