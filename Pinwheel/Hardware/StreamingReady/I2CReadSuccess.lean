import Pinwheel.Hardware.StreamingReady.I2CReadSession
import Pinwheel.Program.StreamingI2CService
import Pinwheel.Program.StreamingReadySessionService

/-! Completion of a profiled I²C read on actual package pins. The peer and
the host supply separate service premises. The engine derives a finite
completion cut, then the host drains that transfer before RELEASE. -/
namespace Pinwheel.Hardware.StreamingReady.I2CReadSuccess
open Pinwheel.Hardware.Streaming Pinwheel.Program Pinwheel.Program.StreamingReady InitializedCustody

private abbrev program := StreamingI2CTrace.Profiled.program

/-- The host keeps the START owner, offers the prescribed TX plan and
eventually provides every needed TX/RX reservation. The peer supplies
timely sampled readiness and sets SDA from its own payload. -/
structure ServiceAssumptions (profile : I2cProfile) (s : Session.State a)
    (traffic : Nat → Session.Pins) (payload : List (BitVec 8)) (peer : Nat → Pinwheel.I2C.Pins) : Prop where
  runtime : SessionService.Runtime (program profile) false s traffic
  unreleased : ∀ n, (SessionService.coreInputs (program profile) false s traffic n).command ≠ 4#4
  deadlines : StreamingI2CService.Profiled.MeetsDeadlines profile s.core
    (SessionService.coreInputs (program profile) false s traffic) peer
  credits : ∀ n, (SessionService.state (program profile) false s traffic n).core.phase = .boundary →
    ∃ m, n ≤ m ∧ (SessionService.state (program profile) false s traffic m).core.canReserve = true
  peerSetup : ∀ edges, StreamingI2CTrace.Profiled.ReadPeer profile s.core
    (s.runtimeInputs (program profile) false (SessionService.clocks traffic edges)) payload peer
  hostPrefix : ∀ edges, (s.traceRun (program profile) false {} (SessionService.clocks traffic edges)).accepted
    <+: StreamingI2CRead.hostBits

/-- After completion the host supplies a finite, ordinary drain and an
admissible RELEASE. This is a host-service premise, independent of the
physical FIFO implementation and of the engine's progress theorem. -/
def DrainService (profile : I2cProfile) (s : Session.State a)
    (traffic : Nat → Session.Pins) : Prop :=
  ∀ edges, let cut := s.run (program profile) false (SessionService.clocks traffic edges)
    cut.core.phase = .completed →
    ∃ (drain : List Session.Pins) (releasePin : Session.Pins),
      let final := cut.run (program profile) false drain
      Session.RuntimeTrace (program profile) false cut drain ∧
      (∀ i ∈ cut.runtimeInputs (program profile) false drain, i.command ≠ 4#4) ∧
      Session.RuntimeInput final releasePin ∧
      (final.command releasePin).runtime.command = 4#4 ∧
      final.core.canRelease (final.command releasePin).runtime = true

structure Result (profile : I2cProfile) (actual : Package.State a) (s : Session.State a)
    (frame drain : List Session.Pins) (releasePin : Session.Pins)
    (payload : List (BitVec 8)) (peer : Nat → Pinwheel.I2C.Pins) : Prop where
  wire : PublicPins.driveTrace actual frame =
    pinTrace (program profile) s.core (s.runtimeInputs (program profile) false frame)
  complete : (s.run (program profile) false frame).core.phase = .completed
  events : StreamingI2CTrace.Profiled.frameEvents profile s.core (s.runtimeInputs (program profile) false frame) =
    [.start] ++ List.replicate 585 .slot ++ [.stop]
  framing : StreamingI2CTrace.Profiled.ResolvedFraming profile s.core
    (s.runtimeInputs (program profile) false frame) peer
  exported :
    let cut := s.run (program profile) false frame
    let captured := s.traceRun (program profile) false {} frame
    (cut.traceRun (program profile) false captured drain).exported = StreamingI2CRead.wireBits payload
  decoded :
    let cut := s.run (program profile) false frame
    let captured := s.traceRun (program profile) false {} frame
    StreamingI2CRead.project (cut.traceRun (program profile) false captured drain).exported = some payload
  acknowledged :
    (((s.run (program profile) false frame).run (program profile) false drain).host.ackOffset).toNat = 585
  emptyExport :
    (((s.run (program profile) false frame).run (program profile) false drain).host.exportBits).toNat = 0
  admitted :
    let cut := actual.run (Package.Components.typed a) (frame.map SessionCorrespondence.pins)
    ActualRelease (cut.run (Package.Components.typed a) (drain.map SessionCorrespondence.pins)) releasePin

private theorem commands_append (p : Program) (s : Session.State a) (xs ys : List Session.Pins) :
    s.runtimeInputs p false (xs ++ ys) =
      s.runtimeInputs p false xs ++ (s.run p false xs).runtimeInputs p false ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons pin rest ih =>
    change _ :: (s.step p false pin).runtimeInputs p false (rest ++ ys) = _
    simp only [Session.State.runtimeInputs,List.cons_append]
    exact congrArg (_ :: ·) (ih (s.step p false pin))

private theorem commands_eq (profile : I2cProfile) (s : Session.State a)
    (traffic : Nat → Session.Pins) (edges : Nat) :
    s.runtimeInputs (program profile) false (SessionService.clocks traffic edges) =
      EventualService.clocks (SessionService.coreInputs (program profile) false s traffic) edges := by
  induction edges with
  | zero => rfl
  | succ edges ih =>
    simp only [SessionService.clocks,EventualService.clocks,List.range_succ,List.map_append,
      List.map_singleton,commands_append]
    change s.runtimeInputs (program profile) false (SessionService.clocks traffic edges) ++
        (s.run (program profile) false (SessionService.clocks traffic edges)).runtimeInputs
          (program profile) false [traffic edges] = _
    rw [ih, ← SessionService.state_eq_run]
    rfl

private theorem release_of_source (profile : I2cProfile) (actual : Package.State a) (s : Session.State a)
    (reached : Reached (i2cImage profile) actual s trace) (pin : Session.Pins) (ha : a ≤ 3)
    (runtime : Session.RuntimeInput s pin) (command : (s.command pin).runtime.command = 4#4)
    (admitted : s.core.canRelease (s.command pin).runtime = true) :
    ActualRelease actual pin := by
  rw [reached.package]
  unfold ActualRelease
  rw [SessionCorrespondence.core_inputs]
  change Core.releasing.eval (HostCorrespondence.commandValues (s.command pin))
    (SourceRefinement.values (Initialization.compiledImage (i2cImage profile)) s.core) = 1#1
  rw [InputCorrespondence.command_eval _ InputCorrespondence.releasing_runtime,
    SourceRefinement.releasing_eval _ s.core (s.command pin).runtime ha runtime]
  simp [command,admitted]

/-- Derive a finite completed frame from peer timing and host credit, then
account for every receive bit at the admitted RELEASE supplied by the host. -/
theorem completed_from_service (profile : I2cProfile) (actual : Package.State a) (s : Session.State a)
    (reached : Reached (i2cImage profile) actual s {}) (before : State a) (start : Input)
    (started : s.core = before.start (program profile) start) (count : start.startCount = 585#16)
    (traffic : Nat → Session.Pins) (payload : List (BitVec 8)) (size : payload.length = 64)
    (peer : Nat → Pinwheel.I2C.Pins) (ha : a ≤ 3)
    (service : ServiceAssumptions profile s traffic payload peer)
    (connection : ∀ edges, I2CReadSession.PublicConnection actual (SessionService.clocks traffic edges) peer)
    (drain : DrainService profile s traffic) :
    ∃ edges drainPins releasePin,
      Result profile actual s (SessionService.clocks traffic edges) drainPins releasePin payload peer := by
  let incoming := SessionService.coreInputs (program profile) false s traffic
  have ordinary (k : Nat) : StreamingI2CTrace.Unreleased (incoming k) :=
    ⟨service.runtime.core_runtime (program profile) false s traffic k, service.unreleased k⟩
  have connected : StreamingI2CService.Profiled.Connected profile s.core incoming peer := by
    intro k
    rw [StreamingI2CService.Profiled.atClock, EventualService.state_eq_run]
    have split : s.runtimeInputs (program profile) false (SessionService.clocks traffic (k+1)) =
        EventualService.clocks incoming k ++ [incoming k] := by
      rw [commands_eq]
      simp only [incoming,EventualService.clocks,List.range_succ,List.map_append,List.map_singleton]
    have sample := I2CReadSession.connected_inputs actual s {} reached
      (SessionService.clocks traffic (k+1)) ha
      (service.runtime.runtimeTrace (program profile) false s traffic (k+1))
      peer (connection (k+1)) (EventualService.clocks incoming k) (incoming k) [] split
    simpa only [StreamingI2CTrace.Profiled.program, EventualService.clocks, List.length_range,
      List.length_map] using sample
  have credits (k : Nat) (boundary :
      (EventualService.state (program profile) s.core incoming k).phase = .boundary) :
      ∃ m, k ≤ m ∧ (EventualService.state (program profile) s.core incoming m).canReserve = true := by
    rw [← SessionService.core_state] at boundary
    obtain ⟨m, later, ready⟩ := service.credits k boundary
    exact ⟨m, later, by rw [← SessionService.core_state]; exact ready⟩
  have setup (edges : Nat) : StreamingI2CTrace.Profiled.ReadPeer profile s.core
      (EventualService.clocks incoming edges) payload peer := by
    rw [← commands_eq profile s traffic edges]
    exact service.peerSetup edges
  have offered (edges : Nat) :
      (traceRun (program profile) s.core {} (EventualService.clocks incoming edges)).accepted
        <+: StreamingI2CRead.hostBits := by
    rw [← commands_eq profile s traffic edges, ← s.traceRun_runtimeInputs]
    exact service.hostPrefix edges
  obtain ⟨edges, complete, events, framed, captured⟩ :=
    StreamingI2CService.Profiled.read_under_service_exact profile before start incoming count ordinary
      payload size peer (by rw [← started]; exact connected)
      (by rw [← started]; exact service.deadlines)
      (by rw [← started]; exact credits)
      (by rw [← started]; exact setup) (by rw [← started]; exact offered)
  rw [← started] at complete events framed captured
  let frame := SessionService.clocks traffic edges
  let cut := s.run (program profile) false frame
  let trace := s.traceRun (program profile) false {} frame
  have completeAtCut : cut.core.phase = .completed := by
    change (s.run (program profile) false frame).core.phase = .completed
    rw [s.run_core, commands_eq]
    exact complete
  have capturedAtCut : trace.captured = StreamingI2CRead.wireBits payload := by
    change (s.traceRun (program profile) false {} frame).captured = _
    rw [s.traceRun_runtimeInputs, commands_eq]
    exact captured
  obtain ⟨drainPins, releasePin, drainRuntime, noRelease, releaseRuntime, command, releaseAllowed⟩ :=
    drain edges completeAtCut
  have frameSegment := SessionProof.advance reached frame ha
    (service.runtime.runtimeTrace (program profile) false s traffic edges)
  have drainSegment := SessionProof.advance frameSegment.reached drainPins ha drainRuntime
  have admitted := release_of_source profile _ _ drainSegment.reached releasePin ha
    releaseRuntime command releaseAllowed
  have released := SessionProof.release drainSegment.reached releasePin ha releaseRuntime admitted
  have retained : cut.core.phase.retained = true := by
    rw [completeAtCut]
    rfl
  have held := retained_trace (program profile) cut.core trace
    (cut.runtimeInputs (program profile) false drainPins) retained
    (fun i member => ⟨drainRuntime.runtimeInputs _ _ _ _ i member, noRelease i member⟩)
  have captureAfterDrain : (cut.traceRun (program profile) false trace drainPins).captured =
      StreamingI2CRead.wireBits payload := by
    rw [cut.traceRun_runtimeInputs, held.2.2, capturedAtCut]
  have exported : (cut.traceRun (program profile) false trace drainPins).exported =
      StreamingI2CRead.wireBits payload :=
    released.exported.symm.trans captureAfterDrain
  refine ⟨edges, drainPins, releasePin, frameSegment.wire, completeAtCut, ?_, ?_, exported, ?_, ?_,
    released.emptyExport, admitted⟩
  · rw [commands_eq]
    exact events
  · rw [commands_eq]
    exact framed
  · exact (congrArg StreamingI2CRead.project exported).trans
      (StreamingI2CRead.decode_wireBits payload size)
  · exact released.ackOffset.symm.trans
      ((congrArg List.length exported).trans (StreamingI2CRead.wireBits_length payload size))

end Pinwheel.Hardware.StreamingReady.I2CReadSuccess
