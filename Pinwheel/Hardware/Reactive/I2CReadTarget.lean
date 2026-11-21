import Pinwheel.Hardware.Reactive.I2CReadConnected
import Pinwheel.I2C.RegisterReadPeerTiming

/-! Apply the closed-loop fetch refinement to the bounded causal I²C target
    and recover the first ACK window from both executions. -/
namespace Pinwheel.Hardware.Reactive.I2CReadTarget

open Pinwheel.Hardware Pinwheel.I2C RegisterReadFetch I2CReadConnected
open RegisterReadPeer (Target cfg request)

def peer (target : Target) : Peer RegisterReadPeer.State :=
  ⟨RegisterReadPeer.drive, RegisterReadPeer.step target⟩

private def referenceState (state : RegisterReadPeer.Pair) : Reference RegisterReadPeer.State :=
  ⟨state.1, state.2⟩

def reference : Reference RegisterReadPeer.State := referenceState RegisterReadPeer.start

def installed : Connected RegisterReadPeer.State where
  core := fun
    | .base r => I2CReadFetch.baseState cfg request reference.core r
    | .savedWord => 0
    | .response => 0
  target := RegisterReadPeer.initial

theorem installed_related : Related cfg request reference installed := by
  refine ⟨⟨rfl, ?_⟩, rfl⟩
  intro bus response
  change (0 : BitVec 1) = 1 at response
  contradiction

private theorem run_state (target : Target) (state : RegisterReadPeer.Pair) (clocks : Nat) :
    (referenceState state).run cfg request (peer target) clocks =
      referenceState (RegisterReadPeer.run cfg request target state clocks) := by
  induction clocks generalizing state with
  | zero => rfl
  | succ clocks ih => exact ih (RegisterReadPeer.edge cfg request target state)

theorem reference_run (target : Target) (clocks : Nat) :
    reference.run cfg request (peer target) clocks = referenceState (RegisterReadPeer.observe target clocks) :=
  run_state target RegisterReadPeer.start clocks

private theorem trace_state (target : Target) (state : RegisterReadPeer.Pair) (clocks : Nat) :
    trace cfg request state.1 ((referenceState state).schedule cfg request (peer target) clocks) =
      RegisterReadPeer.observationsFrom target state clocks := by
  induction clocks generalizing state with
  | zero => rfl
  | succ clocks ih =>
    exact congrArg (RegisterReadFetch.observe request state.1 (.step (RegisterReadPeer.drive state.2)) :: ·)
      (ih (RegisterReadPeer.edge cfg request target state))

def baselineTrace (target : Target) (clocks : Nat) : List Observation :=
  trace cfg request reference.core (reference.schedule cfg request (peer target) clocks)

theorem baselineTrace_eq (target : Target) (clocks : Nat) :
    baselineTrace target clocks = RegisterReadPeer.observations target clocks :=
  trace_state target RegisterReadPeer.start clocks

theorem safe (target : Target) (clocks : Nat) : reference.Safe cfg request (peer target) clocks := by
  apply Reference.safe_of_run
  intro i _
  rw [reference_run]
  dsimp only
  intro cut
  have atDispatch := RegisterReadPeer.firstDispatch_unique target i cut.1 cut.2
  subst i
  let reached := RegisterReadPeer.observe target target.firstDispatch
  obtain ⟨_, _, _, _, expired, steady, low⟩ := RegisterReadPeer.firstDispatch_spec target
  have stationary := RegisterReadPeer.stationary_low target reached.2 (RegisterReadPeer.bus request reached)
    low steady expired
  change RegisterReadPeer.drive (RegisterReadPeer.step target reached.2 (RegisterReadPeer.bus request reached)) =
      RegisterReadPeer.drive reached.2 ∧
    RegisterReadPeer.step target (RegisterReadPeer.step target reached.2 (RegisterReadPeer.bus request reached))
      (RegisterReadPeer.bus request reached) =
      RegisterReadPeer.step target reached.2 (RegisterReadPeer.bus request reached)
  rw [stationary]
  exact ⟨rfl, stationary⟩

private theorem schedule_length (target : Target) (state : Reference RegisterReadPeer.State) (clocks : Nat) :
    (state.schedule cfg request (peer target) clocks).length = clocks := by
  induction clocks generalizing state with
  | zero => rfl
  | succ clocks ih => simp only [Reference.schedule, List.length_cons, ih]

def registeredTrace (target : Target) (clocks : Nat) : List Observation :=
  let execution := installed.run (peer target) clocks
  trace cfg request reference.core (I2CReadFetch.schedule installed.core execution.inputs)

private theorem physical_split (target : Target) (clocks : Nat) (pastCut : target.firstDispatch < clocks) :
    let execution := installed.run (peer target) clocks
    ∃ (before after : List Tick) (pins : Pins),
      before.length = target.firstDispatch ∧
      reference.schedule cfg request (peer target) clocks = before ++ .step pins :: after ∧
      I2CReadFetch.schedule installed.core execution.inputs = before ++ [.pending pins] ++ .step pins :: after := by
  let rest := clocks - (target.firstDispatch + 1)
  have len : target.firstDispatch + 1 + rest = clocks := by dsimp only [rest]; omega
  have shape := reference.single_hold cfg request (peer target) target.firstDispatch rest (by
    rw [reference_run]
    exact ⟨(RegisterReadPeer.firstDispatch_spec target).1, (RegisterReadPeer.firstDispatch_spec target).2.1⟩)
    (by
      intro i _
      rw [reference_run]
      dsimp only
      intro cut
      exact RegisterReadPeer.firstDispatch_unique target i cut.1 cut.2)
  dsimp only at shape
  rw [len] at shape
  have exactSchedule := (I2CReadConnected.run_refines cfg request (peer target) reference installed clocks
    installed_related (safe target clocks)).2.2.2 rfl
  refine ⟨_, _, _, schedule_length target reference target.firstDispatch, shape.2, ?_⟩
  rw [exactSchedule, shape.1, List.append_assoc]
  rfl

/-- Both causal executions satisfy the first-ACK aperture. The registered
    circuit extends the observed low interval by exactly one physical edge. -/
theorem firstAck_timing (target : Target) (clocks : Nat) (enough : 134 ≤ clocks) :
    target.firstAckTiming.Observed (baselineTrace target clocks) 8 (target.nack == some 0) ∧
    target.firstAckTiming.Fits RegisterReadPeer.firstAckWindow ∧
    (target.firstAckTiming.holdLow 1).Observed (registeredTrace target clocks) 8 (target.nack == some 0) ∧
    (target.firstAckTiming.holdLow 1).Fits RegisterReadPeer.firstAckWindow := by
  have observed := RegisterReadPeer.firstAck_observed target clocks enough
  rw [← baselineTrace_eq] at observed
  have fits := RegisterReadPeer.firstAck_fits target
  have pastCut : target.firstDispatch < clocks := by
    have := target.initialStretch.isLt
    simp only [Target.firstDispatch, Target.extra]
    omega
  obtain ⟨before, after, pins, length, base, delayed⟩ := physical_split target clocks pastCut
  have cut : target.firstAckTiming.fall ≤ before.length ∧ before.length < target.firstAckTiming.nextRise := by
    rw [length]
    exact RegisterReadPeer.firstDispatch_within_ack_low target
  refine ⟨observed, fits, ?_⟩
  have physical := I2CReadFetch.matched_ack_hold cfg request reference.core installed.core
    (installed.run (peer target) clocks).inputs installed_related.core before after pins delayed
    target.firstAckTiming RegisterReadPeer.firstAckWindow fits
    (by rw [← base]; exact observed) cut (RegisterReadPeer.firstAck_low_slack target)
  exact physical.2.2.2.2

/-- For the same target parameters, both circuits complete the same read
    or early-NACK path. The independently observed frame, captures, and
    wire changes agree, and the one extra clock fits the first ACK window. -/
theorem read_completes (target : Target) :
    let clocks := target.completion
    let direct := (Direct.installed cfg request reference).run (peer target) clocks
    let retimed := installed.run (peer target) clocks
    let baseline := baselineTrace target clocks
    let registered := registeredTrace target clocks
    I2CReadFetch.directResult direct.1.core = some target.outcome ∧
      I2CReadFetch.result retimed.final.core = some target.outcome ∧
      direct.1.target.stopped = true ∧ direct.1.target.slots = target.stopAfter ∧
      direct.1.target.starts = target.startCount ∧ direct.1.target = retimed.final.target ∧
      baseline.map Observation.wire = direct.2 ∧
      registered.map Observation.wire = I2CReadFetch.wireTrace installed.core retimed.inputs ∧
      registered.filterMap Observation.capture = baseline.filterMap Observation.capture ∧
      wireChanges registered = wireChanges baseline ∧
      baseline.length = clocks ∧ registered.length = clocks + 1 ∧
      (target.firstAckTiming.Observed baseline 8 (target.nack == some 0) ∧
        target.firstAckTiming.Fits RegisterReadPeer.firstAckWindow ∧
        (target.firstAckTiming.holdLow 1).Observed registered 8 (target.nack == some 0) ∧
        (target.firstAckTiming.holdLow 1).Fits RegisterReadPeer.firstAckWindow) := by
  dsimp only
  have baseline := Direct.refines cfg request (peer target) reference target.completion
  have directEnd := baseline.1
  rw [reference_run] at directEnd
  have complete := RegisterReadPeer.baseline_correct target
  have directResult : I2CReadFetch.directResult
      ((Direct.installed cfg request reference).run (peer target) target.completion).1.core =
        some target.outcome := by
    rw [directEnd]
    exact (I2CReadFetch.directResult_eq cfg request _).trans complete.1
  have both := circuits_refine cfg request (peer target) reference installed target.completion
    installed_related (safe target target.completion)
  obtain ⟨agree, targets, baselineWire, registeredWire, captures, changes⟩ := both
  have enough : 134 ≤ target.completion := by
    unfold Target.completion
    split
    · omega
    · split
      · omega
      · split <;> omega
  have pastCut : target.firstDispatch < target.completion := by
    have := target.initialStretch.isLt
    simp only [Target.firstDispatch, Target.extra]
    omega
  have baseLength : (baselineTrace target target.completion).length = target.completion :=
    (trace_length _ _ _ _).trans (schedule_length target reference target.completion)
  obtain ⟨before, after, pins, _, base, delayed⟩ := physical_split target target.completion pastCut
  have extraClock : (registeredTrace target target.completion).length = target.completion + 1 := by
    have baseSteps := baseLength
    rw [baselineTrace, trace_length, base] at baseSteps
    rw [registeredTrace, trace_length, delayed]
    simp only [List.length_append, List.length_cons, List.length_nil] at baseSteps ⊢
    omega
  refine ⟨directResult, agree.symm.trans directResult, ?_, ?_, ?_, targets,
    baselineWire, registeredWire, captures, changes, baseLength, extraClock, firstAck_timing target _ enough⟩
  · rw [directEnd]
    exact complete.2.1
  · rw [directEnd]
    exact complete.2.2.1
  · rw [directEnd]
    exact complete.2.2.2

end Pinwheel.Hardware.Reactive.I2CReadTarget
