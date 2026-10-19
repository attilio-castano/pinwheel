import Pinwheel.Hardware.Buffered.LogicalSessionAbort

/-! Arbitrary finite mixed sessions with completed transfers, active or retained
aborts, resets/reloads and free quiet clocks. Every event threads one ordinary
logical transfer state, and the theorem covers the flattened actual clock list. -/
namespace Pinwheel.Hardware.Buffered.LogicalSession.Mixed
open Pinwheel.Hardware Pinwheel.Program Refinement

inductive Event where
  | round (value : CommandRound)
  | reload (value : I2cReloadSession.Batch)
  | abort (value : AbortedRound)
  | quiet (inputs : List (Values Reactive.Input))

def step (s : LogicalSession.State) : Event → LogicalSession.State
  | .round value => ⟨value.after s.actual, value.logicalAfter I2cSource.source s.actual s.logical, s.offset⟩
  | .reload batch =>
      ⟨batch.after s.actual, resetLogical s.logical, ((batch.after s.actual).core .transfer).toNat⟩
  | .abort value => ⟨value.after s.actual, value.logicalAfter I2cSource.source s.actual s.logical,
      ((value.after s.actual).core .transfer).toNat⟩
  | .quiet inputs => ⟨s.actual.run inputs, s.logical, s.offset⟩

def run (s : LogicalSession.State) (events : List Event) : LogicalSession.State := events.foldl step s

def Event.Admitted (s : LogicalSession.State) : Event → Prop
  | .round value => RoundAdmitted s.actual value
  | .reload batch => I2cReloadSession.Admitted s.actual batch
  | .abort value => AbortAdmitted s.actual value
  | .quiet inputs => ∀ i ∈ inputs, SpiCircuit.Quiet i

def Event.Result (s : LogicalSession.State) : Event → Prop
  | .round value => RoundResult I2cSource.source I2cCertificate.layout s.actual s.logical s.offset value
  | .reload batch => ReloadResult s.actual s.logical batch
  | .abort value => AbortResult s.actual s.logical s.offset value
  | .quiet inputs => QuietResult I2cSource.source I2cCertificate.layout s.actual s.logical s.offset inputs

theorem event_result {s : LogicalSession.State} {event : Event}
    (installed : InstalledSram I2cSource.source I2cCertificate.layout s.actual)
    (aligned : Aligned s.actual s.logical s.offset) (admitted : event.Admitted s) : event.Result s := by
  cases event
  case round value => exact round_result installed aligned admitted
  case reload batch => exact reload_result s.logical admitted
  case abort value => exact abort_result installed aligned admitted
  case quiet inputs => exact quiet_result installed aligned inputs admitted

theorem result_installed {s : LogicalSession.State} {event : Event} (result : event.Result s) :
    InstalledSram I2cSource.source I2cCertificate.layout (step s event).actual := by
  cases event
  case round value => exact result.installed
  case reload batch => exact result.hardware.installed
  case abort value => exact result.hardware.installed
  case quiet inputs => exact result.installed

theorem result_aligned {s : LogicalSession.State} {event : Event} (result : event.Result s) :
    Aligned (step s event).actual (step s event).logical (step s event).offset := by
  cases event
  case round value => exact result.aligned
  case reload batch => exact result.aligned
  case abort value => exact result.aligned
  case quiet inputs => exact result.aligned

def Event.nextAllocation (event : Event) (old : Allocation) : Allocation :=
  match event with
  | .round _ => ⟨old.epoch, old.nextSequence + 1⟩
  | .reload _ | .abort _ => ⟨old.epoch + 1, 1⟩
  | .quiet _ => old

def allocationAfter (initial : Allocation) (events : List Event) : Allocation :=
  events.foldl (fun current event => event.nextAllocation current) initial

theorem result_allocation {s : LogicalSession.State} {event : Event} (result : event.Result s) :
    allocation (step s event).logical = event.nextAllocation (allocation s.logical) := by
  cases event
  case round value =>
    simpa only [allocation, step, Event.nextAllocation, Allocation.mk.injEq] using And.intro result.epoch result.sequence
  case reload batch =>
    simpa only [allocation, step, Event.nextAllocation, Allocation.mk.injEq] using And.intro result.epoch result.sequence
  case abort value =>
    simpa only [allocation, step, Event.nextAllocation, Allocation.mk.injEq] using And.intro result.epoch result.sequence
  case quiet inputs => rfl

def Event.nextCounters (event : Event) (s : LogicalSession.State) (old : Counters) : Counters :=
  match event with
  | .round _ => ⟨old.generation, old.transfer + 1⟩
  | .reload batch =>
      ⟨(if batch.reset .initialize = 1#1 then 0 else min 65535 (old.generation + 1)) +
          LifecycleUpload.commitCount (s.actual.step batch.reset) batch.loading,
        if batch.reset .initialize = 1#1 then 0 else old.transfer⟩
  | .abort value =>
      ⟨(if value.reload.reset .initialize = 1#1 then 0 else min 65535 (old.generation + 1)) +
          LifecycleUpload.commitCount ((value.execution.finished s.actual).step value.reload.reset) value.reload.loading,
        if value.reload.reset .initialize = 1#1 then 0 else old.transfer + 1⟩
  | .quiet _ => old

def accounting (s : LogicalSession.State) (initial : Counters) : List Event → Counters
  | [] => initial
  | event :: rest => accounting (step s event) (event.nextCounters s initial) rest

theorem result_counters {s : LogicalSession.State} {event : Event} (result : event.Result s) :
    counters (step s event).actual = event.nextCounters s (counters s.actual) := by
  cases event
  case round value =>
    simpa only [counters, I2cSessionTrace.counters, step, Event.nextCounters, I2cSessionTrace.Counters.mk.injEq]
      using And.intro (congrArg BitVec.toNat result.generation) result.transfer
  case reload batch =>
    simpa only [step, Event.nextCounters, LogicalSession.State.step, LogicalSession.Event.nextCounters] using
      (LogicalSession.result_counters (s := s) (event := .reload batch) result)
  case abort value =>
    simpa only [counters, I2cSessionTrace.counters, step, Event.nextCounters, I2cSessionTrace.Counters.mk.injEq]
      using And.intro result.generation result.transfer
  case quiet inputs =>
    simpa only [counters, I2cSessionTrace.counters, step, Event.nextCounters, I2cSessionTrace.Counters.mk.injEq]
      using And.intro (congrArg BitVec.toNat result.generation) (congrArg BitVec.toNat result.transfer)

inductive AdmittedTrace : LogicalSession.State → List Event → Prop where
  | nil (s : LogicalSession.State) : AdmittedTrace s []
  | cons {s : LogicalSession.State} {event : Event} {rest : List Event} :
      event.Admitted s → AdmittedTrace (step s event) rest → AdmittedTrace s (event :: rest)

def Results (s : LogicalSession.State) : List Event → Prop
  | [] => True
  | event :: rest => event.Result s ∧ Results (step s event) rest

structure TraceResult (s : LogicalSession.State) (events : List Event) : Prop where
  results : Results s events
  installed : InstalledSram I2cSource.source I2cCertificate.layout (run s events).actual
  aligned : Aligned (run s events).actual (run s events).logical (run s events).offset
  allocation : allocation (run s events).logical = allocationAfter (allocation s.logical) events
  counters : counters (run s events).actual = accounting s (counters s.actual) events

theorem trace_result {s : LogicalSession.State} {events : List Event} (admitted : AdmittedTrace s events)
    (installed : InstalledSram I2cSource.source I2cCertificate.layout s.actual)
    (aligned : Aligned s.actual s.logical s.offset) : TraceResult s events := by
  induction admitted
  case nil => exact ⟨True.intro, installed, aligned, rfl, rfl⟩
  case cons accepted tail ih =>
    rename_i before event restEvents
    have head := event_result installed aligned accepted
    have rest := ih (result_installed head) (result_aligned head)
    refine ⟨⟨head, rest.results⟩, rest.installed, rest.aligned, ?_, ?_⟩
    · change allocation (run (step before event) restEvents).logical = _
      rw [rest.allocation]
      change allocationAfter (allocation (step before event).logical) restEvents = _
      rw [result_allocation head]
      rfl
    · change counters (run (step before event) restEvents).actual = _
      rw [rest.counters]
      change accounting (step before event) (counters (step before event).actual) restEvents = _
      rw [result_counters head]
      rfl

def Event.inputs : Event → List (Values Reactive.Input)
  | .round value => value.inputs
  | .reload batch => batch.inputs
  | .abort value => value.inputs
  | .quiet inputs => inputs

theorem event_eq_inputs (s : LogicalSession.State) (event : Event) :
    (step s event).actual = s.actual.run event.inputs := by
  cases event
  case round value => exact value.after_eq_run s.actual
  case reload batch => exact batch.after_eq_run s.actual
  case abort value => exact value.after_eq_run s.actual
  case quiet inputs => rfl

theorem run_eq_inputs (s : LogicalSession.State) (events : List Event) :
    (run s events).actual = s.actual.run (events.flatMap Event.inputs) := by
  induction events generalizing s
  case nil => rfl
  case cons event rest ih =>
    change (run (step s event) rest).actual = s.actual.run (event.inputs ++ rest.flatMap Event.inputs)
    rw [ih, event_eq_inputs]
    simp [SramState.State.run, List.foldl_append]

theorem boot_session {s : LogicalSession.State} {batch : I2cReloadSession.Batch}
    (boot : I2cReloadSession.Admitted s.actual batch) {events : List Event}
    (admitted : AdmittedTrace (step s (.reload batch)) events) :
    TraceResult s (.reload batch :: events) := by
  have head : Event.Result s (.reload batch) := reload_result s.logical boot
  have rest := trace_result admitted (result_installed head) (result_aligned head)
  refine ⟨⟨head, rest.results⟩, rest.installed, rest.aligned, ?_, ?_⟩
  · change allocation (run (step s (.reload batch)) events).logical = _
    rw [rest.allocation]
    change allocationAfter (allocation (step s (.reload batch)).logical) events = _
    rw [result_allocation head]
    rfl
  · change counters (run (step s (.reload batch)) events).actual = _
    rw [rest.counters]
    change accounting (step s (.reload batch)) (counters (step s (.reload batch)).actual) events = _
    rw [result_counters head]
    rfl

theorem canonical_cold_session (s : LogicalSession.State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 1) (events : List Event)
    (admitted : AdmittedTrace (step s (.reload (I2cCanonicalUpload.batch reset))) events) :
    TraceResult s (.reload (I2cCanonicalUpload.batch reset) :: events) :=
  boot_session (I2cCanonicalUpload.cold_admitted s.actual reset cold) admitted

theorem canonical_warm_session (s : LogicalSession.State) (reset : Values Reactive.Input)
    (cold : reset .initialize = 0) (warm : reset .command = 7)
    (space : (s.actual.core .generation).toNat ≤ 65533) (events : List Event)
    (admitted : AdmittedTrace (step s (.reload (I2cCanonicalUpload.batch reset))) events) :
    TraceResult s (.reload (I2cCanonicalUpload.batch reset) :: events) :=
  boot_session (I2cCanonicalUpload.warm_admitted s.actual reset cold warm space) admitted

end Pinwheel.Hardware.Buffered.LogicalSession.Mixed
