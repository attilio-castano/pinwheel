import StreamingReadySessionD2
import ReadyCoreD2ShiftProof
import Pinwheel.Hardware.StreamingReady.TxShiftPackage
import Pinwheel.Hardware.StreamingReady.SPISession
import Pinwheel.Hardware.StreamingReady.I2CReadSuccess
import Pinwheel.Hardware.StreamingReady.I2CReadTimeout
import Pinwheel.Hardware.StreamingReady.EthernetRefill

/-! Relate independently reconstructed core register layouts through the same
certified package and top-level wiring. -/
namespace Pinwheel.Artifact.StreamingReadyTxShift

open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady
open Pinwheel.Hardware.StreamingReady.InitializedCustody
open Pinwheel.Program Pinwheel.Program.StreamingReady
open StreamingReadySessionD2
open StreamingReadyWrappersD2 (tiny_correct package_correct)

abbrev ring := StreamingReadySessionD2.components

def shift : Package.Components 1 :=
  TxShiftPackage.components ring.frontend StreamingReadyCoreD2Shift.behavior

private theorem shift_behavior :
    StreamingReadyCoreD2Shift.behavior = Package.Behavior.ofCircuit TxShiftCore.circuit := by
  have step :
      @StreamingReadyCoreD2Shift.behavior.step =
        @(Package.Behavior.ofCircuit TxShiftCore.circuit).step := by
    funext i s w reg
    exact StreamingReadyCoreD2Shift.step_correct i s reg
  have observe :
      @StreamingReadyCoreD2Shift.behavior.observe =
        @(Package.Behavior.ofCircuit TxShiftCore.circuit).observe := by
    funext i s w port
    exact StreamingReadyCoreD2Shift.observe_correct i s port
  cases h : StreamingReadyCoreD2Shift.behavior
  simp_all only [Package.Behavior.ofCircuit, Streaming.Package.Behavior.ofCircuit]

theorem ring_correct : ring = Package.Components.typed 1 := components_correct.eq_typed

theorem shift_correct : shift = TxShiftPackage.typed := by
  simp only [shift, ring_correct, shift_behavior]
  rfl

theorem simulates : PackageSimulation.Simulates shift ring TxShiftPackage.RelatedCore := by
  rw [shift_correct, ring_correct]
  exact TxShiftPackage.simulation

/-- One public initialization edge establishes the relation from independent
arbitrary register assignments in the two digital artifacts. -/
theorem cold_related (l r : Package.State 1) :
    let cold := PublicPins.embed BootPins.coldPin
    TxShiftPackage.Related (actualTiny.step actualPackage shift l cold)
      (actualTiny.step actualPackage ring r cold) := by
  simp only [tiny_correct.step_eq package_correct, PublicPins.engine_embed, shift_correct, ring_correct]
  exact TxShiftPackage.cold_related _ _ _ rfl

/-- Every pad value agrees at any observation following a cold edge and an
arbitrary finite public input prefix. The observation may use the same input
as the last edge or the next input in the trace. -/
theorem all_pads_after_cold (l r : Package.State 1) (history : List TinyWiring.Pins)
    (sample : TinyWiring.Pins) :
    let cold := PublicPins.embed BootPins.coldPin
    let afterShift := history.foldl (actualTiny.step actualPackage shift)
      (actualTiny.step actualPackage shift l cold)
    let afterRing := history.foldl (actualTiny.step actualPackage ring)
      (actualTiny.step actualPackage ring r cold)
    actualTiny.observe actualPackage shift afterShift sample =
      actualTiny.observe actualPackage ring afterRing sample :=
  simulates.physical_observe tiny_correct package_correct _
    (simulates.physical_run tiny_correct package_correct _ (cold_related l r))

theorem driveTrace_eq (l r : Package.State 1) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r) :
    PackageSimulation.driveTrace actualTiny actualPackage shift l pins = PublicPins.driveTrace r pins := by
  rw [simulates.driveTrace_eq tiny_correct package_correct pins related, ring_correct]
  exact PackageSimulation.driveTrace_typed tiny_correct package_correct _ _

theorem drive_eq (l r : Package.State 1) (related : TxShiftPackage.Related l r) :
    PackageSimulation.drive actualTiny actualPackage shift l = PublicPins.drive r := by
  have same : [PackageSimulation.drive actualTiny actualPackage shift l] = [PublicPins.drive r] :=
    driveTrace_eq l r [] related
  exact (List.cons.inj same).1

def shiftRun (l : Package.State 1) (pins : List Session.Pins) : Package.State 1 :=
  (pins.map PublicPins.embed).foldl (actualTiny.step actualPackage shift) l

theorem run_related (l r : Package.State 1) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r) :
    TxShiftPackage.Related (shiftRun l pins)
      (r.run (Package.Components.typed 1) (pins.map SessionCorrespondence.pins)) := by
  have next := simulates.physical_run tiny_correct package_correct (pins.map PublicPins.embed) related
  change TxShiftPackage.Related (shiftRun l pins) (physicalRun r (pins.map PublicPins.embed)) at next
  simpa only [physical_run_correct, embedded_engine_pins] using next

/-- The same replacement relation preserves the host reply pins as well as the
    protocol pads, at any cut of a supplied public history. -/
theorem observe_after (l r : Package.State 1) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r) (sample : TinyWiring.Pins) :
    actualTiny.observe actualPackage shift (shiftRun l pins) sample =
      physicalObserve (physicalRun r (pins.map PublicPins.embed)) sample :=
  simulates.physical_observe tiny_correct package_correct sample
    (simulates.physical_run tiny_correct package_correct (pins.map PublicPins.embed) related)

/-- Share a certified upload between the two layouts after arbitrary power-up. -/
theorem boot_i2c_profile (profile : I2cProfile) (l r : Package.State 1)
    (certified : BootPins.Certified (i2cImage profile).words ⟨0,0⟩ BootPins.initialControl 0 false
      (BootPins.compiled (i2cImage profile))) :
    let pins := BootPins.coldPin :: BootPins.compiled (i2cImage profile)
    ∃ boot, BootCorrespondence.Initialized (i2cImage profile)
      (physicalRun r (pins.map PublicPins.embed)) boot ∧
      TxShiftPackage.Related (shiftRun l pins) (physicalRun r (pins.map PublicPins.embed)) := by
  have related := simulates.physical_run tiny_correct package_correct
    ((BootPins.compiled (i2cImage profile)).map PublicPins.embed) (cold_related l r)
  obtain ⟨boot, initialized⟩ := BootCorrespondence.compiled_initialized (i2cImage profile)
    (BootPins.compiled (i2cImage profile)) certified r
  rw [← List.map_cons, ← embedded_engine_pins, ← physical_run_correct] at initialized
  refine ⟨boot, initialized, ?_⟩
  simp only [shiftRun, physicalRun, List.map_cons, List.foldl_cons]
  unfold physicalStep
  exact related

def ShiftPublicConnection (l : Package.State 1) (pins : List Session.Pins)
    (peer : Nat → Pinwheel.I2C.Pins) : Prop :=
  ∀ k < pins.length, (I2CReadSession.rawSamples pins)[k]? =
    ((PackageSimulation.driveTrace actualTiny actualPackage shift l pins)[k]?).map
      (fun drive => Pinwheel.Program.StreamingI2CRead.resolvedRaw drive (peer k))

theorem i2c_connection (l r : Package.State 1) (pins : List Session.Pins)
    (peer : Nat → Pinwheel.I2C.Pins) (related : TxShiftPackage.Related l r) :
    ShiftPublicConnection l pins peer ↔ I2CReadSession.PublicConnection r pins peer := by
  simp only [ShiftPublicConnection, I2CReadSession.PublicConnection, driveTrace_eq l r pins related]

/-- Observe both reconstructed wrappers through the same public history.
    The output equality includes the host's serial replies, even while stalled. -/
structure PublicRun (l r : Package.State 1) (pins : List Session.Pins) : Prop where
  ringWire : publicDriveTrace r (pins.map PublicPins.embed) = PublicPins.driveTrace r pins
  shiftWire : PackageSimulation.driveTrace actualTiny actualPackage shift l pins = PublicPins.driveTrace r pins
  ringState : physicalRun r (pins.map PublicPins.embed) =
    r.run (Package.Components.typed 1) (pins.map SessionCorrespondence.pins)
  related : TxShiftPackage.Related (shiftRun l pins) (physicalRun r (pins.map PublicPins.embed))
  pads : ∀ edges sample,
    actualTiny.observe actualPackage shift (shiftRun l (pins.take edges)) sample =
      physicalObserve (physicalRun r ((pins.take edges).map PublicPins.embed)) sample

theorem public_run (l r : Package.State 1) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r) : PublicRun l r pins := by
  have ringState := (physical_run_correct r (pins.map PublicPins.embed)).trans
    (congrArg _ (embedded_engine_pins pins))
  exact ⟨publicDriveTrace_correct r pins, driveTrace_eq l r pins related, ringState,
    ringState.symm ▸ run_related l r pins related,
    fun edges sample => observe_after l r (pins.take edges) related sample⟩

/-- Connect a public START after upload to the shared custody proof. -/
theorem start_i2c (profile : I2cProfile) (l r : Package.State 1) (boot : Session.State 1)
    (initialized : BootCorrespondence.Initialized (i2cImage profile) r boot)
    (related : TxShiftPackage.Related l r) (before : List Session.Pins) (startPin : Session.Pins)
    (beforeRuntime : Session.RuntimeTrace (i2cImage profile).program false boot before) :
    let p := (i2cImage profile).program
    let ready := boot.run p false before
    let ringReady := physicalRun r (before.map PublicPins.embed)
    let ringStarted := physicalStep ringReady (PublicPins.embed startPin)
    Session.RuntimeInput ready startPin → ActualStart ringReady startPin →
    SessionProof.Started (i2cImage profile) ringReady ready startPin ∧
      TxShiftPackage.Related (shiftRun l (before ++ [startPin])) ringStarted := by
  intro p ready ringReady ringStarted runtime start
  have readyEq : ringReady = r.run (Package.Components.typed 1) (before.map SessionCorrespondence.pins) := by
    simp only [ringReady, physical_run_correct, embedded_engine_pins]
  have started := SessionProof.start (i2cImage profile) r boot initialized before startPin (by decide)
    beforeRuntime runtime (readyEq ▸ start)
  refine ⟨readyEq.symm ▸ started, ?_⟩
  have continued := simulates.physical_run tiny_correct package_correct
    ((before ++ [startPin]).map PublicPins.embed) related
  rw [List.map_append, List.map_singleton] at continued
  simp only [shiftRun, List.map_append, List.map_singleton, ringStarted, ringReady, physicalRun]
  unfold physicalStep
  simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using continued

/-- Use the actual shift pad connection as the peer premise, then carry the
    derived completion cut, framing and acknowledged export on both artifacts. -/
theorem i2c_completed_from_service (profile : I2cProfile) (l r : Package.State 1)
    (s : Session.State 1) (related : TxShiftPackage.Related l r)
    (reached : Reached (i2cImage profile) r s {}) (before : State 1) (start : Input)
    (started : s.core = before.start (i2cImage profile).program start)
    (count : start.startCount = 585#16) (traffic : Nat → Session.Pins)
    (payload : List (BitVec 8)) (size : payload.length = 64) (peer : Nat → Pinwheel.I2C.Pins)
    (service : I2CReadSuccess.ServiceAssumptions profile s traffic payload peer)
    (connection : ∀ edges, ShiftPublicConnection l (SessionService.clocks traffic edges) peer)
    (drain : I2CReadSuccess.DrainService profile s traffic) :
    ∃ edges drainPins releasePin,
      let frame := SessionService.clocks traffic edges
      I2CReadSuccess.Result profile r s frame drainPins releasePin payload peer ∧
      PublicRun l r frame ∧ PublicRun l r (frame ++ drainPins) ∧
      PublicRun l r (frame ++ drainPins ++ [releasePin]) := by
  obtain ⟨edges, drainPins, releasePin, result⟩ := I2CReadSuccess.completed_from_service profile r s
    reached before start started count traffic payload size peer (by decide) service
    (fun edges => (i2c_connection l r (SessionService.clocks traffic edges) peer related).mp (connection edges)) drain
  exact ⟨edges, drainPins, releasePin, result, public_run _ _ _ related,
    public_run _ _ _ related, public_run _ _ _ related⟩

/-- The failed cell may occur at any reachable data WAIT. Its ordinal and
    the exact payload prefix are proved on the shared reference run. Both
    resolved peer connections are checked against the reconstructed shift RTL. -/
theorem i2c_read_to_missed_deadline (profile : I2cProfile) (l r : Package.State 1)
    (boot : Session.State 1) (initialized : BootCorrespondence.Initialized (i2cImage profile) r boot)
    (related : TxShiftPackage.Related l r) (before : List Session.Pins) (startPin : Session.Pins)
    (prefixPins waitPins drainPins : List Session.Pins)
    (beforeRuntime : Session.RuntimeTrace (i2cImage profile).program false boot before)
    (payload : List (BitVec 8)) (size : payload.length = 64)
    (prefixPeer waitPeer : Nat → Pinwheel.I2C.Pins)
    (length : waitPins.length = profile.budgetMinusOne.val + 1)
    (heldLow : ∀ k, k + 2 < waitPins.length → (waitPeer k).scl = .low) :
    let p := (i2cImage profile).program
    let ready := boot.run p false before
    let actualReady := r.run (Package.Components.typed 1) (before.map SessionCorrespondence.pins)
    let started := ready.step p false startPin
    let shiftStarted := shiftRun l (before ++ [startPin])
    let wait := started.run p false prefixPins
    let waitTrace := started.traceRun p false {} prefixPins
    let prefixInputs := started.runtimeInputs p false prefixPins
    let fault := wait.run p false waitPins
    let faultTrace := wait.traceRun p false waitTrace waitPins
    let final := fault.run p false drainPins
    let result := fault.traceRun p false faultTrace drainPins
    let slot := 585 - wait.core.remaining.toNat
    Session.RuntimeInput ready startPin → ActualStart actualReady startPin →
    (ready.command startPin).runtime.startCount = 585#16 →
    Session.RuntimeTrace p false started prefixPins →
    (∀ i ∈ prefixInputs, i.command ≠ 4#4) → ShiftPublicConnection shiftStarted prefixPins prefixPeer →
    StreamingI2CTrace.Profiled.ReadPeer profile started.core prefixInputs payload prefixPeer →
    waitTrace.accepted <+: StreamingI2CRead.hostBits → StreamingI2CDeadline.WaitEntry wait.core profile →
    ShiftPublicConnection (shiftRun shiftStarted prefixPins) waitPins waitPeer →
    Session.RuntimeTrace p false wait waitPins → Session.RuntimeTrace p false fault drainPins →
    (∀ i ∈ fault.runtimeInputs p false drainPins, i.command ≠ 4#4) →
    final.core.rx.count.val = 0 → final.host.exportBits.toNat = 0 →
    I2CReadTimeout.FaultedRead fault final waitTrace result ∧
    result.exported = (StreamingI2CRead.wireBits payload).take slot ∧
    final.host.ackOffset.toNat = slot ∧ slot < 585 ∧
    let pins := before ++ startPin :: (prefixPins ++ waitPins ++ drainPins)
    Reached (i2cImage profile) (physicalRun r (pins.map PublicPins.embed)) final result ∧
    PublicRun l r pins := by
  intro p ready actualReady started shiftStarted wait waitTrace prefixInputs fault faultTrace final result slot
    first admission count prefixRuntime prefixUnreleased prefixWire setup plan entry waitWire waitRuntime
    drainRuntime drainUnreleased drained acked
  have actualAdmission : ActualStart (physicalRun r (before.map PublicPins.embed)) startPin := by
    rwa [physical_run_correct, embedded_engine_pins]
  have startRelated := (start_i2c profile l r boot initialized related before startPin beforeRuntime
    first actualAdmission).2
  rw [physical_step_correct, PublicPins.engine_embed, physical_run_correct, embedded_engine_pins] at startRelated
  have waitRelated := run_related _ _ prefixPins startRelated
  obtain ⟨_, _, drain, abort, bits, ack, inside⟩ := I2CReadTimeout.read_to_missed_deadline profile r boot
    initialized before startPin prefixPins waitPins drainPins (by decide) beforeRuntime payload size
    prefixPeer waitPeer length heldLow first admission count prefixRuntime prefixUnreleased
    ((i2c_connection _ _ prefixPins prefixPeer startRelated).mp prefixWire) setup plan entry
    ((i2c_connection _ _ waitPins waitPeer waitRelated).mp waitWire) waitRuntime drainRuntime
    drainUnreleased drained acked
  have observations := public_run l r (before ++ startPin :: (prefixPins ++ waitPins ++ drainPins)) related
  refine ⟨abort, bits, ack, inside, ?_, observations⟩
  rw [observations.ringState]
  simpa only [List.map_append, List.map_cons, List.foldl_append, List.foldl_cons,
    Package.State.run, Streaming.Package.State.run] using drain.reached

theorem i2c_last_poll (profile : I2cProfile) (l r : Package.State 1)
    (s : Session.State 1) (trace : BitTrace) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r) (reached : Reached (i2cImage profile) r s trace)
    (entry : StreamingI2CDeadline.WaitEntry s.core profile)
    (length : pins.length = profile.budgetMinusOne.val + 1)
    (minimum : 2 ≤ profile.budgetMinusOne.val) (sda : Pinwheel.I2C.Drive)
    (runtime : Session.RuntimeTrace (i2cImage profile).program false s pins)
    (resolved : ShiftPublicConnection l pins (StreamingI2CDeadline.target (profile.budgetMinusOne.val - 2) sda)) :
    let stretch := profile.budgetMinusOne.val - 2
    let final := s.run (i2cImage profile).program false pins
    let ringFinal := r.run (Package.Components.typed 1) (pins.map SessionCorrespondence.pins)
    let result := s.traceRun (i2cImage profile).program false trace pins
    TxShiftPackage.Related (shiftRun l pins) ringFinal ∧
    Reached (i2cImage profile) ringFinal final result ∧
    StreamingI2CDeadline.CaptureResult s.core final.core trace result
      (StreamingI2CRead.resolvedRaw (PackageSimulation.drive actualTiny actualPackage shift l)
        (StreamingI2CDeadline.target stretch sda stretch))[1] profile := by
  refine ⟨run_related l r pins related, ?_⟩
  simpa only [drive_eq l r related] using
    I2CReadSession.last_poll_for profile r s trace reached entry pins length minimum sda (by decide)
      runtime ((i2c_connection l r pins _ related).mp resolved)

theorem i2c_one_poll_late (profile : I2cProfile) (l r : Package.State 1)
    (s : Session.State 1) (trace : BitTrace) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r) (reached : Reached (i2cImage profile) r s trace)
    (entry : StreamingI2CDeadline.WaitEntry s.core profile)
    (length : pins.length = profile.budgetMinusOne.val + 1)
    (minimum : 2 ≤ profile.budgetMinusOne.val) (sda : Pinwheel.I2C.Drive)
    (runtime : Session.RuntimeTrace (i2cImage profile).program false s pins)
    (resolved : ShiftPublicConnection l pins (StreamingI2CDeadline.target (profile.budgetMinusOne.val - 1) sda)) :
    let final := s.run (i2cImage profile).program false pins
    let ringFinal := r.run (Package.Components.typed 1) (pins.map SessionCorrespondence.pins)
    let result := s.traceRun (i2cImage profile).program false trace pins
    TxShiftPackage.Related (shiftRun l pins) ringFinal ∧
    Reached (i2cImage profile) ringFinal final result ∧
    StreamingI2CDeadline.TimeoutResult s.core final.core trace result ∧
    (∀ k < profile.budgetMinusOne.val + 1, ((I2CReadSession.rawSamples pins)[k]?).map (fun raw => raw.getLsbD 0) =
      some (decide (profile.budgetMinusOne.val - 1 ≤ k))) :=
  ⟨run_related l r pins related,
    I2CReadSession.one_poll_late_for profile r s trace reached entry pins length minimum sda (by decide)
      runtime ((i2c_connection l r pins _ related).mp resolved)⟩

/-- Any pin-trace property obtained from the original SPI, I²C, or Ethernet
theorem carries over at a related protocol state. -/
theorem transport (l r : Package.State 1) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r) (property : List Pins → Prop)
    (reference : property (PublicPins.driveTrace r pins)) :
    property (PackageSimulation.driveTrace actualTiny actualPackage shift l pins) := by
  rw [driveTrace_eq l r pins related]
  exact reference

theorem spi_trace (l : Package.State 1) {rows : List Instruction} (image : Compiled rows idle)
    (s : Session.State 1) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l (SessionCorrespondence.values (Initialization.compiledImage image) s))
    (runtime : Session.RuntimeTrace image.program false s pins) (structural : s.core.Structural) :
    PackageSimulation.driveTrace actualTiny actualPackage shift l pins =
      pinTrace image.program s.core (s.runtimeInputs image.program false pins) := by
  rw [driveTrace_eq _ _ _ related]
  exact SPISession.driveTrace_eq image s pins (by decide) runtime structural

theorem i2c_trace (l r : Package.State 1) (s : Session.State 1) (trace : BitTrace)
    (reached : Reached I2CReadSession.image r s trace) (pins : List Session.Pins)
    (related : TxShiftPackage.Related l r)
    (runtime : Session.RuntimeTrace I2CReadSession.image.program false s pins) :
    PackageSimulation.driveTrace actualTiny actualPackage shift l pins =
      pinTrace I2CReadSession.image.program s.core (s.runtimeInputs I2CReadSession.image.program false pins) := by
  rw [driveTrace_eq _ _ _ related]
  exact I2CReadSession.public_trace r s trace reached pins (by decide) runtime

theorem ethernet_wire (l startup : Package.State 1)
    (policy : Pinwheel.Program.StreamingEthernetRefill.Policy) (width : Nat)
    (execution : Pinwheel.Program.StreamingEthernetRefill.Executed policy width)
    (credit : Pinwheel.Program.StreamingEthernetRefill.checkCredit policy width = true)
    (related : TxShiftPackage.Related l
      ((EthernetSession.beforeWire startup).run (Package.Components.typed 1)
        ((Pinwheel.Program.StreamingEthernetRefill.alignmentPins policy width).map SessionCorrespondence.pins))) :
    PackageSimulation.driveTrace actualTiny actualPackage shift l
      (Pinwheel.Program.StreamingEthernetRefill.activePins policy width) =
      Pinwheel.Program.StreamingEthernetFrame.frameBits.flatMap
        Pinwheel.Program.StreamingEthernetCore.cellPins ++
      [Pinwheel.Program.StreamingEthernetCore.txPins false, Pinwheel.Program.StreamingEthernetCore.idlePins] := by
  rw [driveTrace_eq _ _ _ related]
  exact EthernetRefill.wire_exact startup policy width execution credit

end Pinwheel.Artifact.StreamingReadyTxShift
