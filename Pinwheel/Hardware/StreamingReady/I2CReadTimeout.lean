import Pinwheel.Hardware.StreamingReady.I2CReadSession

/-! A missed data deadline at the public I²C pins retains exactly the
earlier captures through a host drain and acknowledgment. -/
namespace Pinwheel.Hardware.StreamingReady.I2CReadTimeout
open Pinwheel.Program Pinwheel.Program.StreamingReady
open InitializedCustody

/-- Once the host has drained and acknowledged RX, the final ledger contains
the ordered bits captured strictly before the faulted cell. -/
structure FaultedRead (fault final : Session.State a) (prefixBits result : BitTrace) : Prop where
  faultAtDeadline : fault.core.phase = .fault
  faultRetained : final.core.phase = .fault
  partialFlushed : final.core.rxUsed = 0#6
  captured : result.captured = prefixBits.captured
  exported : result.exported = prefixBits.captured
  acknowledged : final.host.ackOffset.toNat = prefixBits.captured.length

/-- SCL held low through every eligible aperture forces a fault regardless of
the later wire levels. The host can drain and acknowledge without RELEASE. -/
theorem missed_data_deadline (profile : I2cProfile) (actual : Package.State a)
    (s : Session.State a) (trace : BitTrace)
    (reached : Reached (i2cImage profile) actual s trace)
    (entry : StreamingI2CDeadline.WaitEntry s.core profile)
    (waitPins drainPins : List Session.Pins) (ha : a ≤ 3)
    (length : waitPins.length = profile.budgetMinusOne.val + 1)
    (peer : Nat → Pinwheel.I2C.Pins)
    (resolved : I2CReadSession.PublicConnection actual waitPins peer)
    (heldLow : ∀ k, k + 2 < waitPins.length → (peer k).scl = .low)
    (runtime : Session.RuntimeTrace (i2cImage profile).program false s waitPins) :
    let p := (i2cImage profile).program
    let fault := s.run p false waitPins
    let faultActual := actual.run (Package.Components.typed a) (waitPins.map SessionCorrespondence.pins)
    let faultTrace := s.traceRun p false trace waitPins
    let final := fault.run p false drainPins
    let result := fault.traceRun p false faultTrace drainPins
    Session.RuntimeTrace p false fault drainPins →
    (∀ i ∈ fault.runtimeInputs p false drainPins, i.command ≠ 4#4) →
    final.core.rx.count.val = 0 → final.host.exportBits.toNat = 0 →
    SessionProof.Segment (i2cImage profile) actual s trace waitPins ∧
    SessionProof.Segment (i2cImage profile) faultActual fault faultTrace drainPins ∧
    FaultedRead fault final trace result := by
  intro p fault faultActual faultTrace final result drainRuntime noRelease drained acked
  have deadline := SessionProof.advance reached waitPins ha runtime
  have drain := SessionProof.advance deadline.reached drainPins ha drainRuntime
  let inputs := s.runtimeInputs p false waitPins
  have lengths : inputs.length = waitPins.length := I2CReadSession.command_length (profile := profile) s waitPins
  have rawLow (k : Nat) (inside : k < inputs.length) (early : k + 2 < inputs.length) :
      inputs[k].rawInputs[0] = false := by
    rw [I2CReadSession.connected_at actual s trace reached waitPins ha runtime peer resolved k inside]
    rw [← BitVec.getLsbD_eq_getElem (by decide : 0 < 2), StreamingI2CRead.resolvedRaw_scl]
    simp [heldLow k (lengths ▸ early)]
  have timeout := StreamingI2CDeadline.missed_guard_for profile s.core entry trace inputs
    (lengths.trans length) (runtime.runtimeInputs p false s waitPins) rawLow
  have faulted : fault.core.phase = .fault := by
    rw [s.run_core]
    exact timeout.phase
  have flushed : fault.core.rxUsed = 0#6 := by
    rw [s.run_core]
    exact timeout.partialFlushed
  have faultBits : faultTrace.captured = trace.captured := by
    dsimp only [faultTrace]
    rw [s.traceRun_runtimeInputs]
    exact timeout.captured
  have hold := retained_trace p fault.core faultTrace (fault.runtimeInputs p false drainPins)
    (by simp [faulted, Phase.retained])
    (fun i member => ⟨drainRuntime.runtimeInputs p false fault drainPins i member, noRelease i member⟩)
  have emptyPartial : final.core.rxUsed = 0#6 := by
    rw [fault.run_core, hold.2.1, flushed]
  have captured : result.captured = trace.captured := by
    dsimp only [result]
    rw [fault.traceRun_runtimeInputs]
    exact hold.2.2.trans faultBits
  have exactAck := drain.reached.custody.acknowledged_capture final result drained emptyPartial acked
  refine ⟨deadline, drain, ⟨faulted, ?_, emptyPartial, captured,
    exactAck.1.symm.trans captured, exactAck.2.trans (congrArg List.length captured)⟩⟩
  rw [fault.run_core, hold.1, faulted]

/-- Starting at an initialized image, an arbitrary missed data slot exports
exactly the corresponding prefix of the peer's read plan. The slot is
computed from the unqualified cell's remaining count. -/
theorem read_to_missed_deadline (profile : I2cProfile) (actualBoot : Package.State a)
    (boot : Session.State a)
    (initialized : BootCorrespondence.Initialized (i2cImage profile) actualBoot boot)
    (before : List Session.Pins) (startPin : Session.Pins)
    (prefixPins waitPins drainPins : List Session.Pins) (ha : a ≤ 3)
    (beforeRuntime : Session.RuntimeTrace (i2cImage profile).program false boot before)
    (payload : List (BitVec 8)) (size : payload.length = 64)
    (prefixPeer waitPeer : Nat → Pinwheel.I2C.Pins)
    (length : waitPins.length = profile.budgetMinusOne.val + 1)
    (heldLow : ∀ k, k + 2 < waitPins.length → (waitPeer k).scl = .low) :
    let p := (i2cImage profile).program
    let ready := boot.run p false before
    let actualReady := actualBoot.run (Package.Components.typed a) (before.map SessionCorrespondence.pins)
    let started := ready.step p false startPin
    let startActual := actualReady.step (Package.Components.typed a) (SessionCorrespondence.pins startPin)
    let wait := started.run p false prefixPins
    let waitActual := startActual.run (Package.Components.typed a) (prefixPins.map SessionCorrespondence.pins)
    let waitTrace := started.traceRun p false {} prefixPins
    let prefixInputs := started.runtimeInputs p false prefixPins
    let fault := wait.run p false waitPins
    let faultActual := waitActual.run (Package.Components.typed a) (waitPins.map SessionCorrespondence.pins)
    let faultTrace := wait.traceRun p false waitTrace waitPins
    let final := fault.run p false drainPins
    let result := fault.traceRun p false faultTrace drainPins
    let slot := 585 - wait.core.remaining.toNat
    Session.RuntimeInput ready startPin →
    ActualStart actualReady startPin → (ready.command startPin).runtime.startCount = 585#16 →
    Session.RuntimeTrace p false started prefixPins →
    (∀ i ∈ prefixInputs, i.command ≠ 4#4) →
    I2CReadSession.PublicConnection startActual prefixPins prefixPeer →
    StreamingI2CTrace.Profiled.ReadPeer profile started.core prefixInputs payload prefixPeer →
    waitTrace.accepted <+: StreamingI2CRead.hostBits →
    StreamingI2CDeadline.WaitEntry wait.core profile →
    I2CReadSession.PublicConnection waitActual waitPins waitPeer →
    Session.RuntimeTrace p false wait waitPins →
    Session.RuntimeTrace p false fault drainPins →
    (∀ i ∈ fault.runtimeInputs p false drainPins, i.command ≠ 4#4) →
    final.core.rx.count.val = 0 → final.host.exportBits.toNat = 0 →
    SessionProof.Segment (i2cImage profile) startActual started {} prefixPins ∧
    SessionProof.Segment (i2cImage profile) waitActual wait waitTrace waitPins ∧
    SessionProof.Segment (i2cImage profile) faultActual fault faultTrace drainPins ∧
    FaultedRead fault final waitTrace result ∧
    result.exported = (StreamingI2CRead.wireBits payload).take slot ∧
    final.host.ackOffset.toNat = slot ∧ slot < 585 := by
  intro p ready actualReady started startActual wait waitActual waitTrace prefixInputs fault faultActual
    faultTrace final result slot startRuntime admission count prefixRuntime prefixUnreleased prefixWire
    peerSetup hostPlan entry waitWire waitRuntime drainRuntime drainUnreleased drained acked
  have initial := SessionProof.start (i2cImage profile) actualBoot boot initialized before
    startPin ha beforeRuntime startRuntime admission
  have prefixSegment := SessionProof.advance initial.reached prefixPins ha prefixRuntime
  obtain ⟨deadline, drain, abort⟩ := missed_data_deadline profile waitActual wait waitTrace
    prefixSegment.reached entry waitPins drainPins ha length waitPeer waitWire heldLow waitRuntime
    drainRuntime drainUnreleased drained acked
  open StreamingI2CTrace.Profiled in
  have exactPrefix :
      waitTrace.captured = (StreamingI2CRead.wireBits payload).take slot ∧
        waitTrace.captured.length = slot ∧ slot < 585 := by
    let start := (ready.command startPin).runtime
    have positive : 0 < start.startCount.toNat := by
      change start.startCount = 585#16 at count
      simp [count]
    have ordinary (i : Input) (member : i ∈ prefixInputs) : Unreleased i :=
      ⟨prefixRuntime.runtimeInputs p false started prefixPins i member,prefixUnreleased i member⟩
    have connection : Connected profile started.core prefixInputs prefixPeer := by
      intro earlier i rest split
      exact I2CReadSession.connected_inputs startActual started {} initial.reached prefixPins ha
        prefixRuntime prefixPeer prefixWire earlier i rest split
    have shape : Positioned profile started.core := by
      rw [initial.coreStart]
      exact positioned_start profile ready.core start positive
    have atWait : (run p started.core prefixInputs).phase = .waiting := by
      rw [← started.run_core]
      exact entry.phase
    have safe : (run p started.core prefixInputs).phase ≠ .fault := by simp [atWait]
    have flow := tx_qualified_run profile started.core {} [] (by rw [initial.coreStart]; rfl)
      prefixInputs shape ordinary safe
    have qualified : txQualifiedRun profile started.core prefixInputs <+: waitTrace.consumed := by
      refine ⟨txFlightBits (run p started.core prefixInputs),?_⟩
      dsimp only [waitTrace]
      rw [started.traceRun_runtimeInputs]
      exact flow.symm
    have consumed : waitTrace.consumed <+: waitTrace.accepted := by
      refine ⟨wait.core.pendingTx ++ waitTrace.txQueued.flatMap Streaming.Chunk.txBits,?_⟩
      simpa only [List.append_assoc] using prefixSegment.reached.custody.related.txOrder.symm
    have bits := captured_read_prefix profile started.core prefixInputs shape ordinary safe
      payload prefixPeer size connection peerSetup (qualified.trans (consumed.trans hostPlan))
    have clockCount := slots_before_wait profile ready.core start prefixInputs positive ordinary
      (initial.coreStart ▸ atWait)
    rw [← (show started.core = ready.core.start (program profile) start from initial.coreStart)] at clockCount
    have remain : (run (program profile) started.core prefixInputs).remaining.toNat =
        wait.core.remaining.toNat := by
      exact (congrArg (fun core : State a => core.remaining.toNat)
        (started.run_core p false prefixPins)).symm
    rw [remain] at clockCount
    have count585 : start.startCount.toNat = 585 := by
      change start.startCount = 585#16 at count
      simp [count]
    have ordinal : (qualifiedStates profile started.core prefixInputs).length = slot := by
      dsimp only [slot]
      omega
    have stream : wait.core.current.isStream = true := by rw [entry.current]; rfl
    have remaining := prefixSegment.reached.custody.progress.active stream
      (Or.inr (Or.inr (Or.inr entry.phase)))
    have inside : slot < 585 := Nat.sub_lt (by decide) remaining
    have exactBits : waitTrace.captured = (StreamingI2CRead.wireBits payload).take slot := by
      dsimp only [waitTrace]
      rw [started.traceRun_runtimeInputs]
      exact ordinal ▸ bits
    refine ⟨exactBits,?_ ,inside⟩
    rw [exactBits,List.length_take,StreamingI2CRead.wireBits_length payload size,Nat.min_eq_left (by omega)]
  exact ⟨prefixSegment, deadline, drain, abort, abort.exported.trans exactPrefix.1,
    abort.acknowledged.trans exactPrefix.2.1, exactPrefix.2.2⟩

end Pinwheel.Hardware.StreamingReady.I2CReadTimeout
