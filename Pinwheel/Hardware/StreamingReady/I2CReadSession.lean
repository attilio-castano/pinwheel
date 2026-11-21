import Pinwheel.Hardware.StreamingReady.SessionProof
import Pinwheel.Program.StreamingI2CDeadline
import Pinwheel.Program.StreamingI2CTx

/-! The read image and deadline profiles at the public pads of the sampled-ready package. -/
namespace Pinwheel.Hardware.StreamingReady.I2CReadSession
open Pinwheel.Program Pinwheel.Program.StreamingReady
open Pinwheel.Hardware.StreamingReady.InitializedCustody

abbrev image := i2cImage .standard

/-- The same LOW and HIGH durations, with 19 guard polls. -/
def shortDeadlineProfile : I2cProfile :=
  { I2cProfile.standard with
    budgetMinusOne := 18
    stretchBound := 16
    waitMargin := by decide }

/-- These are the words uploaded in the frozen RTL and gate replays. -/
theorem standard_words : image.words =
    [575334852396580868,545265688,5175770730129791001,817895448,564075853336543236,545265688,2] := by
  decide +kernel

def rawSamples (pins : List Session.Pins) : List (BitVec 2) :=
  pins.map (fun pin => (PublicPins.embed pin).ui.extractLsb' 3 2)

theorem public_trace {profile : I2cProfile} (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached (i2cImage profile) actual s trace) (pins : List Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace (i2cImage profile).program false s pins) :
    PublicPins.driveTrace actual pins =
      pinTrace (i2cImage profile).program s.core (s.runtimeInputs (i2cImage profile).program false pins) :=
  (SessionProof.advance reached pins ha runtime).wire

theorem runtime_raw_at_for (profile : I2cProfile) (s : Session.State a) (pins : List Session.Pins) (k : Nat) :
    ((s.runtimeInputs (i2cImage profile).program false pins)[k]?).map Pinwheel.Program.Streaming.Input.rawInputs =
      (rawSamples pins)[k]? := by
  rw [← List.getElem?_map,PublicPins.rawTrace_eq]
  rfl

theorem runtime_raw_at (s : Session.State a) (pins : List Session.Pins) (k : Nat) :
    ((s.runtimeInputs image.program false pins)[k]?).map Pinwheel.Program.Streaming.Input.rawInputs =
      (rawSamples pins)[k]? :=
  runtime_raw_at_for .standard s pins k

private theorem drive_at_prefix (p : Program) (s : State a) (pre rest : List Input) :
    (pinTrace p s (pre ++ rest))[pre.length]? = some (run p s pre).pins := by
  induction pre generalizing s with
  | nil => cases rest <;> rfl
  | cons i pre ih =>
    change (pinTrace p (step p i s) (pre ++ rest))[pre.length]? =
      some (run p (step p i s) pre).pins
    exact ih _

/-- Each pre-edge raw sample comes from resolving the current public drive
    with an independently supplied open-drain target drive. -/
def PublicConnection (actual : Package.State a) (pins : List Session.Pins)
    (peer : Nat → Pinwheel.I2C.Pins) : Prop :=
  ∀ k < pins.length, (rawSamples pins)[k]? =
    ((PublicPins.driveTrace actual pins)[k]?).map (fun drive =>
      StreamingI2CRead.resolvedRaw drive (peer k))

theorem command_length {profile : I2cProfile} (s : Session.State a) (pins : List Session.Pins) :
    (s.runtimeInputs (i2cImage profile).program false pins).length = pins.length := by
  have same := congrArg List.length (PublicPins.rawTrace_eq s (i2cImage profile).program false pins)
  simpa only [List.length_map] using same

theorem connected_inputs {profile : I2cProfile} (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached (i2cImage profile) actual s trace) (pins : List Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace (i2cImage profile).program false s pins)
    (peer : Nat → Pinwheel.I2C.Pins) (wire : PublicConnection actual pins peer)
    (pre : List Input) (i : Input) (rest : List Input)
    (suffix : s.runtimeInputs (i2cImage profile).program false pins = pre ++ i :: rest) :
    i.rawInputs = StreamingI2CRead.resolvedRaw (run (i2cImage profile).program s.core pre).pins (peer pre.length) := by
  have bound : pre.length < pins.length := by
    rw [← command_length (profile := profile) s pins,suffix]
    simp
  have placed := wire pre.length bound
  rw [public_trace actual s trace reached pins ha runtime,suffix,drive_at_prefix,
    ← runtime_raw_at_for profile s pins pre.length,suffix,
    List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at placed
  exact Option.some.inj placed

theorem connected_at {profile : I2cProfile} (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached (i2cImage profile) actual s trace) (pins : List Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace (i2cImage profile).program false s pins)
    (peer : Nat → Pinwheel.I2C.Pins) (wire : PublicConnection actual pins peer)
    (k : Nat) (hk : k < (s.runtimeInputs (i2cImage profile).program false pins).length) :
    let inputs := s.runtimeInputs (i2cImage profile).program false pins
    inputs[k].rawInputs =
      StreamingI2CRead.resolvedRaw (run (i2cImage profile).program s.core (inputs.take k)).pins (peer k) := by
  let inputs := s.runtimeInputs (i2cImage profile).program false pins
  have split := List.take_append_drop k inputs
  rw [List.drop_eq_getElem_cons hk] at split
  have raw := connected_inputs actual s trace reached pins ha runtime peer wire
    (inputs.take k) inputs[k] (inputs.drop (k+1)) split.symm
  have length : (inputs.take k).length = k := by
    rw [List.length_take,Nat.min_eq_left (show k ≤ inputs.length from Nat.le_of_lt hk)]
  rw [length] at raw
  exact raw

theorem wait_stimulus {profile : I2cProfile} (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached (i2cImage profile) actual s trace) (entry : StreamingI2CDeadline.WaitEntry s.core profile)
    (pins : List Session.Pins) (stretch : Nat) (sda : Pinwheel.I2C.Drive) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace (i2cImage profile).program false s pins)
    (wire : PublicConnection actual pins (StreamingI2CDeadline.target stretch sda))
    (budget : pins.length ≤ profile.budgetMinusOne.val + 1) (delayed : pins.length ≤ stretch + 3) :
    StreamingI2CDeadline.Stimulus s.core stretch sda (s.runtimeInputs (i2cImage profile).program false pins) := by
  apply StreamingI2CDeadline.Stimulus.of_runtime_resolved_for profile _ entry _ _ _
    (runtime.runtimeInputs (i2cImage profile).program false s pins)
    (connected_at actual s trace reached pins ha runtime _ wire)
  · rwa [command_length (profile := profile)]
  · rwa [command_length (profile := profile)]

/-- The four driven-low clocks supply both initial low sampler values. -/
theorem enter_wait {profile : I2cProfile} (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached (i2cImage profile) actual s trace) (pins : List Session.Pins)
    (low : s.core.phase = .low) (countdown : s.core.countdown = 3#8)
    (row : s.core.current = StreamingI2CDeadline.streamRowFor profile)
    (sclDrive : (PublicPins.drive actual).enabled[0] = true)
    (length : pins.length = 4) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace (i2cImage profile).program false s pins)
    (peer : Nat → Pinwheel.I2C.Pins) (wire : PublicConnection actual pins peer) :
    let final := s.run (i2cImage profile).program false pins
    let finalActual := actual.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins)
    Reached (i2cImage profile) finalActual final (s.traceRun (i2cImage profile).program false trace pins) ∧
    StreamingI2CDeadline.WaitEntry final.core profile := by
  rw [reached.package,PublicPins.drive_eq] at sclDrive
  refine ⟨reached.run pins ha runtime,?_⟩
  rw [s.run_core]
  apply StreamingI2CDeadline.enter_wait_from_low_for profile _ _ low countdown row sclDrive
    ((command_length (profile := profile) s pins).trans length) (runtime.runtimeInputs (i2cImage profile).program false s pins)
  intro k bound
  let inputs := s.runtimeInputs (i2cImage profile).program false pins
  have runtimeInputs := runtime.runtimeInputs (i2cImage profile).program false s pins
  have within : (inputs.take k).length ≤ s.core.countdown.toNat := by
    have len : inputs.length = 4 := (command_length (profile := profile) s pins).trans length
    simp only [countdown,BitVec.toNat_ofNat,List.length_take,len]
    have inside : k < inputs.length := bound
    omega
  have keep := (low_prefix (i2cImage profile).program s.core (inputs.take k) low
    (fun i member => runtimeInputs i (List.mem_of_mem_take member)) within).2.2.1
  have raw := connected_at actual s trace reached pins ha runtime peer wire k bound
  change inputs[k].rawInputs =
    StreamingI2CRead.resolvedRaw (run (i2cImage profile).program s.core (inputs.take k)).pins (peer k) at raw
  rw [keep] at raw
  exact ⟨peer k,raw⟩

/-- At the last allowed poll the package still captures one physical SDA sample. -/
theorem last_poll_for (profile : I2cProfile) (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached (i2cImage profile) actual s trace)
    (entry : StreamingI2CDeadline.WaitEntry s.core profile) (pins : List Session.Pins)
    (length : pins.length = profile.budgetMinusOne.val + 1)
    (minimum : 2 ≤ profile.budgetMinusOne.val) (sda : Pinwheel.I2C.Drive) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace (i2cImage profile).program false s pins)
    (resolved : PublicConnection actual pins (StreamingI2CDeadline.target (profile.budgetMinusOne.val - 2) sda)) :
    let final := s.run (i2cImage profile).program false pins
    let finalActual := actual.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins)
    let result := s.traceRun (i2cImage profile).program false trace pins
    Reached (i2cImage profile) finalActual final result ∧
    StreamingI2CDeadline.CaptureResult s.core final.core trace result
      (StreamingI2CRead.resolvedRaw (PublicPins.drive actual)
        (StreamingI2CDeadline.target (profile.budgetMinusOne.val - 2) sda (profile.budgetMinusOne.val - 2)))[1] profile := by
  let stretch := profile.budgetMinusOne.val - 2
  have stimulus := wait_stimulus actual s trace reached entry pins stretch sda ha runtime resolved (by omega) (by omega)
  have timely := StreamingI2CDeadline.stretch_success_for profile s.core entry trace stretch sda
    (s.runtimeInputs (i2cImage profile).program false pins) stimulus (by omega) (by rw [command_length (profile := profile), length]; omega)
  refine ⟨reached.run pins ha runtime,?_⟩
  rw [s.run_core,s.traceRun_runtimeInputs,reached.package,PublicPins.drive_eq]
  exact timely

/-- Raw SCL already rose on the public input. The sampler sees it too late
    to qualify a capture, so the earlier captured prefix remains owned. -/
theorem one_poll_late_for (profile : I2cProfile) (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached (i2cImage profile) actual s trace)
    (entry : StreamingI2CDeadline.WaitEntry s.core profile) (pins : List Session.Pins)
    (length : pins.length = profile.budgetMinusOne.val + 1)
    (minimum : 2 ≤ profile.budgetMinusOne.val) (sda : Pinwheel.I2C.Drive) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace (i2cImage profile).program false s pins)
    (resolved : PublicConnection actual pins (StreamingI2CDeadline.target (profile.budgetMinusOne.val - 1) sda)) :
    let final := s.run (i2cImage profile).program false pins
    let finalActual := actual.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins)
    let result := s.traceRun (i2cImage profile).program false trace pins
    Reached (i2cImage profile) finalActual final result ∧
    StreamingI2CDeadline.TimeoutResult s.core final.core trace result ∧
    (∀ k < profile.budgetMinusOne.val + 1, ((rawSamples pins)[k]?).map (fun raw => raw.getLsbD 0) =
      some (decide (profile.budgetMinusOne.val - 1 ≤ k))) := by
  let inputs := s.runtimeInputs (i2cImage profile).program false pins
  have stimulus := wait_stimulus actual s trace reached entry pins (profile.budgetMinusOne.val - 1) sda ha runtime resolved (by omega) (by omega)
  have len : inputs.length = profile.budgetMinusOne.val + 1 := (command_length (profile := profile) s pins).trans length
  have timeout := StreamingI2CDeadline.one_late_for profile s.core entry trace sda inputs minimum stimulus len
    reached.custody.related reached.custody.structural
  refine ⟨reached.run pins ha runtime,?_,?_⟩
  · rw [s.run_core,s.traceRun_runtimeInputs]
    exact timeout
  · intro k hk
    have bound : k < inputs.length := len.symm ▸ hk
    rw [← runtime_raw_at_for profile s pins k,List.getElem?_eq_getElem bound]
    change some (inputs[k].rawInputs[0]) = _
    rw [stimulus.scl entry.release k bound]

theorem last_poll (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached image actual s trace)
    (entry : StreamingI2CDeadline.WaitEntry s.core) (pins : List Session.Pins)
    (length : pins.length = 31) (sda : Pinwheel.I2C.Drive) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace image.program false s pins)
    (resolved : PublicConnection actual pins (StreamingI2CDeadline.target 28 sda)) :
    let final := s.run image.program false pins
    let finalActual := actual.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins)
    let result := s.traceRun image.program false trace pins
    Reached image finalActual final result ∧
    StreamingI2CDeadline.CaptureResult s.core final.core trace result
      (StreamingI2CRead.resolvedRaw (PublicPins.drive actual)
        (StreamingI2CDeadline.target 28 sda 28))[1] :=
  last_poll_for .standard actual s trace reached entry pins length (by decide) sda ha runtime resolved

theorem one_poll_late (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached image actual s trace)
    (entry : StreamingI2CDeadline.WaitEntry s.core) (pins : List Session.Pins)
    (length : pins.length = 31) (sda : Pinwheel.I2C.Drive) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace image.program false s pins)
    (resolved : PublicConnection actual pins (StreamingI2CDeadline.target 29 sda)) :
    let final := s.run image.program false pins
    let finalActual := actual.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins)
    let result := s.traceRun image.program false trace pins
    Reached image finalActual final result ∧
    StreamingI2CDeadline.TimeoutResult s.core final.core trace result ∧
    (∀ k < 31, ((rawSamples pins)[k]?).map (fun raw => raw.getLsbD 0) =
      some (decide (29 ≤ k))) :=
  one_poll_late_for .standard actual s trace reached entry pins length (by decide) sda ha runtime resolved

/-- ACK of a drained fault prefix preserves the exact pre-fault captures
    even in a session where unsent TX still prevents RELEASE. -/
theorem acknowledge_fault (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached image actual s trace) (fault : s.core.phase = .fault) (flushed : s.core.rxUsed = 0#6)
    (pins : List Session.Pins) (ha : a ≤ 3) (runtime : Session.RuntimeTrace image.program false s pins)
    (unreleased : ∀ i ∈ s.runtimeInputs image.program false pins, i.command ≠ 4#4) :
    let final := s.run image.program false pins
    let result := s.traceRun image.program false trace pins
    final.core.rx.count.val = 0 → final.host.exportBits.toNat = 0 →
    result.exported = trace.captured ∧ final.host.ackOffset.toNat = trace.captured.length := by
  intro final result drained acked
  have continued := reached.run pins ha runtime
  have hold := retained_trace image.program s.core trace (s.runtimeInputs image.program false pins)
    (by simp [fault,Phase.retained])
    (fun i member => ⟨runtime.runtimeInputs image.program false s pins i member,unreleased i member⟩)
  have emptyPartial : final.core.rxUsed = 0#6 := by
    dsimp only [final]
    rw [s.run_core,hold.2.1,flushed]
  have captured : result.captured = trace.captured := by
    dsimp only [result]
    rw [s.traceRun_runtimeInputs]
    exact hold.2.2
  have exactAck := continued.custody.acknowledged_capture final result drained emptyPartial acked
  exact ⟨exactAck.1.symm.trans captured,by rw [exactAck.2,captured]⟩

/-- Lift a complete read to the initialized package, the resolved public
    bus, and the host's acknowledged export. -/
theorem completed_read (actualBoot : Package.State a) (boot : Session.State a)
    (initialized : BootCorrespondence.Initialized image actualBoot boot)
    (before : List Session.Pins) (startPin : Session.Pins) (after : List Session.Pins)
    (releasePin : Session.Pins) (ha : a ≤ 3)
    (beforeRuntime : Session.RuntimeTrace image.program false boot before)
    (payload : List (BitVec 8)) (size : payload.length = 64)
    (peer : Nat → Pinwheel.I2C.Pins) :
    let p := image.program
    let ready := boot.run p false before
    let actualReady := actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)
    let started := ready.step p false startPin
    let actualStarted := actualReady.step (Package.Components.typed a) (SessionCorrespondence.pins startPin)
    let final := started.run p false after
    let actualFinal := actualStarted.run (Package.Components.typed a) (after.map SessionCorrespondence.pins)
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
    PublicPins.driveTrace actualStarted after = pinTrace p started.core inputs ∧
    StreamingI2CTrace.frameEvents started.core inputs =
      [.start] ++ List.replicate 585 .slot ++ [.stop] ∧
    StreamingI2CTrace.ResolvedFraming started.core inputs peer ∧
    trace.exported = StreamingI2CRead.wireBits payload ∧
    StreamingI2CRead.project trace.exported = some payload ∧
    final.host.ackOffset.toNat = 585 ∧ final.host.exportBits.toNat = 0 := by
  intro p ready actualReady started actualStarted final actualFinal inputs trace
  intro startRuntime start count runtime noRelease wire legal completed tx releaseRuntime release
  have initial := SessionProof.start image actualBoot boot initialized before startPin ha beforeRuntime startRuntime start
  have segment := SessionProof.advance initial.reached after ha runtime
  have released : SessionProof.Released final trace :=
    SessionProof.release segment.reached releasePin ha releaseRuntime release
  let command := (ready.command startPin).runtime
  have coreStart : started.core = ready.core.start p command := initial.coreStart
  have coreFinal : final.core = run p started.core inputs := started.run_core p false after
  have traceEq : trace = traceRun p started.core {} inputs := started.traceRun_runtimeInputs p false {} after
  have finished : (run p (ready.core.start p command) inputs).phase = .completed := by
    rw [← coreStart,← coreFinal]
    exact completed
  have ordinary : ∀ i ∈ inputs, StreamingI2CTrace.Unreleased i :=
    fun i member => ⟨runtime.runtimeInputs p false started after i member,noRelease i member⟩
  have initReach : Reached image actualStarted started {} := initial.reached
  have connected : StreamingI2CTrace.Connected started.core inputs peer := by
    intro pre i rest suffix
    exact connected_inputs actualStarted started {} initReach after ha runtime peer wire pre i rest suffix
  have positive : 0 < command.startCount.toNat := by
    change command.startCount = 585#16 at count
    simp [count]
  have txQualified := StreamingI2CTrace.started_tx_qualified ready.core command inputs
    positive ordinary finished
  have ordered : StreamingI2CTrace.txQualifiedRun (ready.core.start p command) inputs =
      StreamingI2CRead.hostBits := by
    calc
      _ = (traceRun p (ready.core.start p command) {} inputs).consumed := txQualified.symm
      _ = trace.consumed := by rw [traceEq,coreStart]
      _ = trace.accepted := released.accepted.symm
      _ = _ := tx
  have result := StreamingI2CTrace.completed_read ready.core command inputs ordinary finished
    count payload peer size (coreStart ▸ connected) (coreStart ▸ legal) ordered
  obtain ⟨frame,resolved,captured⟩ := result
  have exported : trace.exported = StreamingI2CRead.wireBits payload := by
    rw [← released.exported,traceEq,coreStart]
    exact captured
  refine ⟨segment.wire,?_,?_,exported,?_,?_,released.emptyExport⟩
  · rw [coreStart]
    exact frame
  · rw [coreStart]
    exact resolved
  · rw [exported]
    exact StreamingI2CRead.decode_wireBits payload size
  · rw [← released.ackOffset,exported,StreamingI2CRead.wireBits_length payload size]

end Pinwheel.Hardware.StreamingReady.I2CReadSession
