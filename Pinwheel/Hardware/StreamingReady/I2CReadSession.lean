import Pinwheel.Hardware.StreamingReady.InitializedCustody
import Pinwheel.Hardware.StreamingReady.PublicPins
import Pinwheel.Program.StreamingI2CDeadline
import Pinwheel.Program.StreamingI2CTx

/-! The standard read image and the public pads of the sampled-ready package. -/
namespace Pinwheel.Hardware.StreamingReady.I2CReadSession
open Pinwheel.Program Pinwheel.Program.StreamingReady
open Pinwheel.Hardware.StreamingReady.InitializedCustody

abbrev image := i2cImage .standard

/-- These are the words uploaded in the frozen RTL and gate replays. -/
theorem standard_words : image.words =
    [575334852396580868,545265688,5175770730129791001,817895448,564075853336543236,545265688,2] := by
  decide +kernel

def rawSamples (pins : List Session.Pins) : List (BitVec 2) :=
  pins.map (fun pin => (PublicPins.embed pin).ui.extractLsb' 3 2)

theorem public_trace (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached image actual s trace) (pins : List Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace image.program false s pins) :
    PublicPins.driveTrace actual pins =
      pinTrace image.program s.core (s.runtimeInputs image.program false pins) := by
  rw [reached.package]
  simpa only [compiled_pending] using PublicPins.driveTrace_eq (Initialization.compiledImage image)
    s pins ha (by simpa only [compiled_pending] using runtime) reached.custody.structural

theorem runtime_raw_at (s : Session.State a) (pins : List Session.Pins) (k : Nat) :
    ((s.runtimeInputs image.program false pins)[k]?).map Pinwheel.Program.Streaming.Input.rawInputs =
      (rawSamples pins)[k]? := by
  rw [← List.getElem?_map,PublicPins.rawTrace_eq]
  rfl

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

private theorem command_length (s : Session.State a) (pins : List Session.Pins) :
    (s.runtimeInputs image.program false pins).length = pins.length := by
  have same := congrArg List.length (PublicPins.rawTrace_eq s image.program false pins)
  simpa only [List.length_map] using same

theorem connected_inputs (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached image actual s trace) (pins : List Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace image.program false s pins)
    (peer : Nat → Pinwheel.I2C.Pins) (wire : PublicConnection actual pins peer)
    (pre : List Input) (i : Input) (rest : List Input)
    (suffix : s.runtimeInputs image.program false pins = pre ++ i :: rest) :
    i.rawInputs = StreamingI2CRead.resolvedRaw (run image.program s.core pre).pins (peer pre.length) := by
  have bound : pre.length < pins.length := by
    rw [← command_length s pins,suffix]
    simp
  have placed := wire pre.length bound
  rw [public_trace actual s trace reached pins ha runtime,suffix,drive_at_prefix,
    ← runtime_raw_at s pins pre.length,suffix,
    List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at placed
  exact Option.some.inj placed

theorem connected_at (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached image actual s trace) (pins : List Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace image.program false s pins)
    (peer : Nat → Pinwheel.I2C.Pins) (wire : PublicConnection actual pins peer)
    (k : Nat) (hk : k < (s.runtimeInputs image.program false pins).length) :
    let inputs := s.runtimeInputs image.program false pins
    inputs[k].rawInputs =
      StreamingI2CRead.resolvedRaw (run image.program s.core (inputs.take k)).pins (peer k) := by
  let inputs := s.runtimeInputs image.program false pins
  have split := List.take_append_drop k inputs
  rw [List.drop_eq_getElem_cons hk] at split
  have raw := connected_inputs actual s trace reached pins ha runtime peer wire
    (inputs.take k) inputs[k] (inputs.drop (k+1)) split.symm
  have length : (inputs.take k).length = k := by
    rw [List.length_take,Nat.min_eq_left (show k ≤ inputs.length from Nat.le_of_lt hk)]
  rw [length] at raw
  exact raw

theorem wait_stimulus (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached image actual s trace) (entry : StreamingI2CDeadline.WaitEntry s.core)
    (pins : List Session.Pins) (stretch : Nat) (sda : Pinwheel.I2C.Drive) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace image.program false s pins)
    (wire : PublicConnection actual pins (StreamingI2CDeadline.target stretch sda))
    (budget : pins.length ≤ 31) (delayed : pins.length ≤ stretch + 3) :
    StreamingI2CDeadline.Stimulus s.core stretch sda (s.runtimeInputs image.program false pins) := by
  apply StreamingI2CDeadline.Stimulus.of_runtime_resolved _ entry _ _ _
    (runtime.runtimeInputs image.program false s pins)
    (connected_at actual s trace reached pins ha runtime _ wire)
  · rwa [command_length]
  · rwa [command_length]

/-- The four driven-low clocks supply both initial low sampler values. -/
theorem enter_wait (actual : Package.State a) (s : Session.State a) (trace : BitTrace)
    (reached : Reached image actual s trace) (pins : List Session.Pins)
    (low : s.core.phase = .low) (countdown : s.core.countdown = 3#8)
    (row : s.core.current = StreamingI2CDeadline.streamRow)
    (sclDrive : (PublicPins.drive actual).enabled[0] = true)
    (length : pins.length = 4) (ha : a ≤ 3)
    (runtime : Session.RuntimeTrace image.program false s pins)
    (peer : Nat → Pinwheel.I2C.Pins) (wire : PublicConnection actual pins peer) :
    let final := s.run image.program false pins
    let finalActual := actual.run (Package.Components.typed a) (pins.map SessionCorrespondence.pins)
    Reached image finalActual final (s.traceRun image.program false trace pins) ∧
    StreamingI2CDeadline.WaitEntry final.core := by
  rw [reached.package,PublicPins.drive_eq] at sclDrive
  refine ⟨reached.run pins ha runtime,?_⟩
  rw [s.run_core]
  apply StreamingI2CDeadline.enter_wait_from_low _ _ low countdown row sclDrive
    ((command_length s pins).trans length) (runtime.runtimeInputs image.program false s pins)
  intro k bound
  let inputs := s.runtimeInputs image.program false pins
  have runtimeInputs := runtime.runtimeInputs image.program false s pins
  have within : (inputs.take k).length ≤ s.core.countdown.toNat := by
    have len : inputs.length = 4 := (command_length s pins).trans length
    simp only [countdown,BitVec.toNat_ofNat,List.length_take,len]
    have inside : k < inputs.length := bound
    omega
  have keep := (low_prefix image.program s.core (inputs.take k) low
    (fun i member => runtimeInputs i (List.mem_of_mem_take member)) within).2.2.1
  have raw := connected_at actual s trace reached pins ha runtime peer wire k bound
  change inputs[k].rawInputs =
    StreamingI2CRead.resolvedRaw (run image.program s.core (inputs.take k)).pins (peer k) at raw
  rw [keep] at raw
  exact ⟨peer k,raw⟩

/-- At the last allowed poll the package still captures one physical SDA sample. -/
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
        (StreamingI2CDeadline.target 28 sda 28))[1] := by
  have stimulus := wait_stimulus actual s trace reached entry pins 28 sda ha runtime resolved (by omega) (by omega)
  have timely := StreamingI2CDeadline.stretch_success s.core entry trace 28 sda
    (s.runtimeInputs image.program false pins) stimulus (by decide) ((command_length s pins).trans length)
  refine ⟨reached.run pins ha runtime,?_⟩
  rw [s.run_core,s.traceRun_runtimeInputs,reached.package,PublicPins.drive_eq]
  exact timely

/-- Raw SCL already rose on the public input. The sampler sees it too late
    to qualify a capture, so the earlier captured prefix remains owned. -/
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
      some (decide (29 ≤ k))) := by
  let inputs := s.runtimeInputs image.program false pins
  have stimulus := wait_stimulus actual s trace reached entry pins 29 sda ha runtime resolved (by omega) (by omega)
  have len : inputs.length = 31 := (command_length s pins).trans length
  have timeout := StreamingI2CDeadline.one_late s.core entry trace sda inputs stimulus len
    reached.custody.related reached.custody.structural
  refine ⟨reached.run pins ha runtime,?_,?_⟩
  · rw [s.run_core,s.traceRun_runtimeInputs]
    exact timeout
  · intro k hk
    have bound : k < inputs.length := len.symm ▸ hk
    rw [← runtime_raw_at s pins k,List.getElem?_eq_getElem bound]
    change some (inputs[k].rawInputs[0]) = _
    rw [stimulus.scl entry.release k bound]

private theorem fault_drain_trace (s : State a) (trace : BitTrace) (inputs : List Input)
    (fault : s.phase = .fault) (ordinary : ∀ i ∈ inputs, i.Runtime ∧ i.command ≠ 4#4) :
    let final := run image.program s inputs
    final.phase = .fault ∧ final.rxUsed = s.rxUsed ∧
      (traceRun image.program s trace inputs).captured = trace.captured := by
  induction inputs generalizing s trace with
  | nil => exact ⟨fault,rfl,rfl⟩
  | cons i rest ih =>
    obtain ⟨⟨cold,warm⟩,release⟩ := ordinary i List.mem_cons_self
    have next : step image.program i s = clock image.program i s := by
      simp [step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,fault]
    have phase : (step image.program i s).phase = .fault := by simp [next,clock,engine,fault]
    have usedStable : (step image.program i s).rxUsed = s.rxUsed := by simp [next,clock,engine,fault]
    have captures : (trace.step s i).captured = trace.captured := by
      simp [BitTrace.step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,fault,
        BitTrace.clock,State.rxEvent,State.captures]
    obtain ⟨last,used,bits⟩ := ih _ _ phase (fun j member => ordinary j (List.mem_cons_of_mem _ member))
    exact ⟨last,used.trans usedStable,bits.trans captures⟩

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
  have hold := fault_drain_trace s.core trace (s.runtimeInputs image.program false pins) fault
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
  have initial := started_run image actualBoot boot initialized before startPin [] ha
    beforeRuntime startRuntime start trivial
  have reached := started_run image actualBoot boot initialized before startPin after ha
    beforeRuntime startRuntime start runtime
  have released := reached.release_all_bits releasePin ha releaseRuntime release
  change trace.accepted = trace.consumed ∧ trace.captured = trace.exported ∧
    trace.exported.length = final.host.ackOffset.toNat ∧ final.host.exportBits.toNat = 0 at released
  have actualEq : actualReady = SessionCorrespondence.values (Initialization.compiledImage image) ready :=
    initialized_run_eq image actualBoot boot initialized before ha beforeRuntime
  have admission := start
  rw [actualEq] at admission
  have admitted := start_source (Initialization.compiledImage image) ready startPin startRuntime admission
  let command := (ready.command startPin).runtime
  have coreStart : started.core = ready.core.start p command :=
    ready.core_admitted_start p false startPin startRuntime admitted
  have coreFinal : final.core = run p started.core inputs := started.run_core p false after
  have traceEq : trace = traceRun p started.core {} inputs := started.traceRun_runtimeInputs p false {} after
  have finished : (run p (ready.core.start p command) inputs).phase = .completed := by
    rw [← coreStart,← coreFinal]
    exact completed
  have ordinary : ∀ i ∈ inputs, StreamingI2CTrace.Unreleased i :=
    fun i member => ⟨runtime.runtimeInputs p false started after i member,noRelease i member⟩
  have initReach : Reached image actualStarted started {} := initial
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
      _ = trace.accepted := released.1.symm
      _ = _ := tx
  have result := StreamingI2CTrace.completed_read ready.core command inputs ordinary finished
    count payload peer size (coreStart ▸ connected) (coreStart ▸ legal) ordered
  obtain ⟨frame,resolved,captured⟩ := result
  have exported : trace.exported = StreamingI2CRead.wireBits payload := by
    rw [← released.2.1,traceEq,coreStart]
    exact captured
  refine ⟨public_trace actualStarted started {} initReach after ha runtime,?_,?_,exported,?_,?_,released.2.2.2⟩
  · rw [coreStart]
    exact frame
  · rw [coreStart]
    exact resolved
  · rw [exported]
    exact StreamingI2CRead.decode_wireBits payload size
  · rw [← released.2.2.1,exported,StreamingI2CRead.wireBits_length payload size]

end Pinwheel.Hardware.StreamingReady.I2CReadSession
