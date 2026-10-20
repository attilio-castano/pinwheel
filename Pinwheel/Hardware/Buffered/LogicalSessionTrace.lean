import Pinwheel.Hardware.Buffered.LogicalSessionRound
import Pinwheel.Hardware.Buffered.I2cUploadAdequacy

/-! One ordinary logical Transfer.State is threaded through arbitrary mixed
rounds and cold/warm reloads. Reload uses ordinary reset and rebases its wire
offset; rounds use ordinary prepare/start/execution/read/release. -/
namespace Pinwheel.Hardware.Buffered.LogicalSession
open Pinwheel.Hardware Pinwheel.Program Refinement

def resetLogical (logical : Transfer.State) : Transfer.State :=
  (Transfer.step capacity logical .reset).state

structure ReloadResult (actual : SramState.State) (logical : Transfer.State)
    (batch : I2cReloadSession.Batch) : Prop where
  hardware : I2cReloadSession.Result actual batch
  reset : Transfer.step capacity logical .reset = ⟨resetLogical logical, .reset⟩
  aligned : Aligned (batch.after actual) (resetLogical logical) ((batch.after actual).core .transfer).toNat
  epoch : (resetLogical logical).epoch = logical.epoch + 1
  sequence : (resetLogical logical).nextSequence = 1

theorem reload_result {actual : SramState.State} (logical : Transfer.State)
    {batch : I2cReloadSession.Batch} (admitted : I2cReloadSession.Admitted actual batch) :
    ReloadResult actual logical batch := by
  have hardware := I2cReloadSession.result admitted
  exact ⟨hardware, rfl, ⟨rfl, hardware.phase, hardware.retained, rfl⟩, rfl, rfl⟩

inductive Event where
  | round (value : CommandRound)
  | reload (value : I2cReloadSession.Batch)

structure State where
  actual : SramState.State
  logical : Transfer.State
  offset : Nat

def State.step (s : State) (event : Event) : State :=
  match event with
  | .round value =>
      ⟨value.after s.actual, value.logicalAfter I2cSource.source s.actual s.logical, s.offset⟩
  | .reload batch =>
      ⟨batch.after s.actual, resetLogical s.logical, ((batch.after s.actual).core .transfer).toNat⟩

def State.run (s : State) (events : List Event) : State := events.foldl State.step s

def Event.Admitted (s : State) : Event → Prop
  | .round value => RoundAdmitted s.actual value
  | .reload batch => I2cReloadSession.Admitted s.actual batch

def Event.Result (s : State) : Event → Prop
  | .round value => RoundResult I2cSource.source I2cCertificate.layout s.actual s.logical s.offset value
  | .reload batch => ReloadResult s.actual s.logical batch

theorem event_result {s : State} {event : Event}
    (installed : InstalledSram I2cSource.source I2cCertificate.layout s.actual)
    (aligned : Aligned s.actual s.logical s.offset) (admitted : event.Admitted s) : event.Result s := by
  cases event
  case round value => exact round_result installed aligned admitted
  case reload batch => exact reload_result s.logical admitted

theorem result_installed {s : State} {event : Event} (result : event.Result s) :
    InstalledSram I2cSource.source I2cCertificate.layout (s.step event).actual := by
  cases event
  case round value => exact result.installed
  case reload batch => exact result.hardware.installed

theorem result_aligned {s : State} {event : Event} (result : event.Result s) :
    Aligned (s.step event).actual (s.step event).logical (s.step event).offset := by
  cases event
  case round value => exact result.aligned
  case reload batch => exact result.aligned

structure Allocation where
  epoch : Nat
  nextSequence : Nat
  deriving DecidableEq

def allocation (logical : Transfer.State) : Allocation := ⟨logical.epoch, logical.nextSequence⟩

def Event.nextAllocation (event : Event) (old : Allocation) : Allocation :=
  match event with
  | .round _ => ⟨old.epoch, old.nextSequence + 1⟩
  | .reload _ => ⟨old.epoch + 1, 1⟩

def allocationAfter (initial : Allocation) (events : List Event) : Allocation :=
  events.foldl (fun current event => event.nextAllocation current) initial

theorem result_allocation {s : State} {event : Event} (result : event.Result s) :
    allocation (s.step event).logical = event.nextAllocation (allocation s.logical) := by
  cases event
  case round value =>
    simp only [allocation, State.step, Event.nextAllocation, Allocation.mk.injEq]
    exact ⟨result.epoch, result.sequence⟩
  case reload batch =>
    simp only [allocation, State.step, Event.nextAllocation, Allocation.mk.injEq]
    exact ⟨result.epoch, result.sequence⟩

abbrev Counters := I2cSessionTrace.Counters
abbrev counters := I2cSessionTrace.counters

def Event.nextCounters (event : Event) (s : State) (old : Counters) : Counters :=
  match event with
  | .round _ => ⟨old.generation, old.transfer + 1⟩
  | .reload batch =>
      ⟨(if batch.reset .initialize = 1#1 then 0 else min 65535 (old.generation + 1)) +
          LifecycleUpload.commitCount (s.actual.step batch.reset) batch.loading,
        if batch.reset .initialize = 1#1 then 0 else old.transfer⟩

def accounting (s : State) (initial : Counters) : List Event → Counters
  | [] => initial
  | event :: rest => accounting (s.step event) (event.nextCounters s initial) rest

theorem result_counters {s : State} {event : Event} (result : event.Result s) :
    counters (s.step event).actual = event.nextCounters s (counters s.actual) := by
  cases event
  case round value =>
    simp only [counters, I2cSessionTrace.counters, State.step, Event.nextCounters,
      I2cSessionTrace.Counters.mk.injEq]
    exact ⟨congrArg BitVec.toNat result.generation, result.transfer⟩
  case reload batch =>
    have transfer := congrArg BitVec.toNat result.hardware.transfer
    simp only [counters, I2cSessionTrace.counters, State.step, Event.nextCounters,
      I2cSessionTrace.Counters.mk.injEq]
    refine ⟨result.hardware.generation, ?_⟩
    by_cases cold : batch.reset .initialize = 1#1
    · simpa [cold] using transfer
    · simpa [cold] using transfer

inductive AdmittedTrace : State → List Event → Prop where
  | nil (s : State) : AdmittedTrace s []
  | cons {s : State} {event : Event} {rest : List Event} :
      event.Admitted s → AdmittedTrace (s.step event) rest → AdmittedTrace s (event :: rest)

def Results (s : State) : List Event → Prop
  | [] => True
  | event :: rest => event.Result s ∧ Results (s.step event) rest

structure TraceResult (s : State) (events : List Event) : Prop where
  results : Results s events
  installed : InstalledSram I2cSource.source I2cCertificate.layout (s.run events).actual
  aligned : Aligned (s.run events).actual (s.run events).logical (s.run events).offset
  allocation : allocation (s.run events).logical = allocationAfter (allocation s.logical) events
  counters : counters (s.run events).actual = accounting s (counters s.actual) events

theorem trace_result {s : State} {events : List Event} (admitted : AdmittedTrace s events)
    (installed : InstalledSram I2cSource.source I2cCertificate.layout s.actual)
    (aligned : Aligned s.actual s.logical s.offset) : TraceResult s events := by
  induction admitted
  case nil => exact ⟨True.intro, installed, aligned, rfl, rfl⟩
  case cons accepted tail ih =>
    rename_i before event restEvents
    have head := event_result installed aligned accepted
    have rest := ih (result_installed head) (result_aligned head)
    refine ⟨⟨head, rest.results⟩, rest.installed, rest.aligned, ?_, ?_⟩
    · change allocation ((before.step event).run restEvents).logical = _
      rw [rest.allocation]
      change allocationAfter (allocation (before.step event).logical) restEvents = _
      rw [result_allocation head]
      rfl
    · change counters ((before.step event).run restEvents).actual = _
      rw [rest.counters]
      change accounting (before.step event) (counters (before.step event).actual) restEvents = _
      rw [result_counters head]
      rfl

def Event.inputs : Event → List (Values Reactive.Input)
  | .round value => value.inputs
  | .reload batch => batch.inputs

theorem event_eq_inputs (s : State) (event : Event) :
    (s.step event).actual = s.actual.run event.inputs := by
  cases event
  case round value => exact value.after_eq_run s.actual
  case reload batch => exact batch.after_eq_run s.actual

theorem run_eq_inputs (s : State) (events : List Event) :
    (s.run events).actual = s.actual.run (events.flatMap Event.inputs) := by
  induction events generalizing s
  case nil => rfl
  case cons event rest ih =>
    change ((s.step event).run rest).actual = s.actual.run (event.inputs ++ rest.flatMap Event.inputs)
    rw [ih, event_eq_inputs]
    simp [SramState.State.run, List.foldl_append]

theorem boot_session {s : State} {batch : I2cReloadSession.Batch}
    (boot : I2cReloadSession.Admitted s.actual batch) {events : List Event}
    (admitted : AdmittedTrace (s.step (.reload batch)) events) :
    TraceResult s (.reload batch :: events) := by
  have head : Event.Result s (.reload batch) := reload_result s.logical boot
  have rest := trace_result admitted (result_installed head) (result_aligned head)
  refine ⟨⟨head, rest.results⟩, rest.installed, rest.aligned, ?_, ?_⟩
  · change allocation ((s.step (.reload batch)).run events).logical = _
    rw [rest.allocation]
    change allocationAfter (allocation (s.step (.reload batch)).logical) events = _
    rw [result_allocation head]
    rfl
  · change counters ((s.step (.reload batch)).run events).actual = _
    rw [rest.counters]
    change accounting (s.step (.reload batch)) (counters (s.step (.reload batch)).actual) events = _
    rw [result_counters head]
    rfl

theorem canonical_cold_session (s : State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 1) (events : List Event)
    (admitted : AdmittedTrace (s.step (.reload (I2cCanonicalUpload.batch reset))) events) :
    TraceResult s (.reload (I2cCanonicalUpload.batch reset) :: events) :=
  boot_session (I2cCanonicalUpload.cold_admitted s.actual reset cold) admitted

theorem canonical_warm_session (s : State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 0) (warm : reset .command = 7)
    (space : (s.actual.core .generation).toNat ≤ 65533) (events : List Event)
    (admitted : AdmittedTrace (s.step (.reload (I2cCanonicalUpload.batch reset))) events) :
    TraceResult s (.reload (I2cCanonicalUpload.batch reset) :: events) :=
  boot_session (I2cCanonicalUpload.warm_admitted s.actual reset cold warm space) admitted

end Pinwheel.Hardware.Buffered.LogicalSession
