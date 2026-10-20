import Pinwheel.Hardware.Buffered.I2cReloadSession
import Pinwheel.Hardware.Buffered.GenericSessionReuse
import Pinwheel.Hardware.Buffered.LifecycleEpochRelation

/-! An arbitrary finite mixture of complete transfers and cold/warm reloads.
Every event expands to actual sampled controller inputs. Logical epochs label
ownership histories; no epoch is added to the frozen wire format. -/
namespace Pinwheel.Hardware.Buffered.I2cSessionTrace
open Pinwheel.Hardware Pinwheel.Program

inductive Event where
  | round (value : GenericSession.Round)
  | reload (value : I2cReloadSession.Batch)

def Event.after (event : Event) (s : SramState.State) : SramState.State :=
  match event with
  | .round value => value.after s
  | .reload batch => batch.after s

def Event.inputs : Event → List (Values Reactive.Input)
  | .round value => value.inputs
  | .reload batch => batch.inputs

def Event.nextEpoch (event : Event) (epoch : Nat) : Nat :=
  match event with
  | .round _ => epoch
  | .reload _ => epoch + 1

def Event.Admitted (s : SramState.State) : Event → Prop
  | .round value => GenericSession.Admitted s value
  | .reload batch => I2cReloadSession.Admitted s batch

def Event.Result (epoch : Nat) (s : SramState.State) : Event → Prop
  | .round value => GenericSession.RoundResult I2cSource.source I2cCertificate.layout s value ∧
      Refinement.RelatedSram I2cSource.source I2cCertificate.layout (value.start .txData)
        (value.finished s) (Lifecycle.EpochView.buffered epoch (value.source I2cSource.source s))
  | .reload batch => I2cReloadSession.Result s batch

theorem event_result {s : SramState.State} {event : Event} (epoch : Nat)
    (installed : Refinement.InstalledSram I2cSource.source I2cCertificate.layout s)
    (admitted : event.Admitted s) : event.Result epoch s := by
  cases event
  case round round =>
    have result := GenericSession.round_result installed admitted
    exact ⟨result, Lifecycle.EpochView.relatedSram epoch result.related⟩
  case reload batch => exact I2cReloadSession.result admitted

theorem result_installed {s : SramState.State} {event : Event} {epoch : Nat}
    (result : event.Result epoch s) :
    Refinement.InstalledSram I2cSource.source I2cCertificate.layout (event.after s) := by
  cases event
  case round round => exact result.1.installed
  case reload batch => exact result.installed

theorem result_idle {s : SramState.State} {event : Event} {epoch : Nat}
    (result : event.Result epoch s) :
    (event.after s).core .phase = 0 ∧ (event.after s).core .retained = 0 := by
  cases event
  case round round => exact ⟨result.1.phase, result.1.retained⟩
  case reload batch => exact ⟨result.phase, result.retained⟩

structure Counters where
  generation : Nat
  transfer : Nat
  deriving DecidableEq

def counters (s : SramState.State) : Counters :=
  ⟨(s.core .generation).toNat, (s.core .transfer).toNat⟩

def Event.nextCounters (event : Event) (s : SramState.State) (old : Counters) : Counters :=
  match event with
  | .round _ => ⟨old.generation, old.transfer + 1⟩
  | .reload batch =>
    ⟨(if batch.reset .initialize = 1#1 then 0 else min 65535 (old.generation + 1)) +
        LifecycleUpload.commitCount (s.step batch.reset) batch.loading,
      if batch.reset .initialize = 1#1 then 0 else old.transfer⟩

theorem result_counters {s : SramState.State} {event : Event} {epoch : Nat}
    (result : event.Result epoch s) :
    counters (event.after s) = event.nextCounters s (counters s) := by
  cases event
  case round round =>
    have generation := congrArg BitVec.toNat result.1.generation
    simp only [counters, Event.after, Event.nextCounters, Counters.mk.injEq]
    exact ⟨generation, result.1.transfer⟩
  case reload batch =>
    have transfer := congrArg BitVec.toNat result.transfer
    simp only [counters, Event.after, Event.nextCounters, Counters.mk.injEq]
    refine ⟨result.generation, ?_⟩
    by_cases cold : batch.reset .initialize = 1#1
    · simpa [cold] using transfer
    · simpa [cold] using transfer

def run (s : SramState.State) (events : List Event) : SramState.State :=
  events.foldl (fun current event => event.after current) s

def epochAfter (epoch : Nat) (events : List Event) : Nat :=
  events.foldl (fun current event => event.nextEpoch current) epoch

def accounting (s : SramState.State) (old : Counters) : List Event → Counters
  | [] => old
  | event :: rest => accounting (event.after s) (event.nextCounters s old) rest

inductive AdmittedTrace : SramState.State → List Event → Prop where
  | nil (s : SramState.State) : AdmittedTrace s []
  | cons {s : SramState.State} {event : Event} {rest : List Event} :
      event.Admitted s → AdmittedTrace (event.after s) rest → AdmittedTrace s (event :: rest)

def Results (epoch : Nat) (s : SramState.State) : List Event → Prop
  | [] => True
  | event :: rest => event.Result epoch s ∧ Results (event.nextEpoch epoch) (event.after s) rest

theorem trace_result {s : SramState.State} {events : List Event}
    (admitted : AdmittedTrace s events) (epoch : Nat)
    (installed : Refinement.InstalledSram I2cSource.source I2cCertificate.layout s)
    (phase : s.core .phase = 0) (retained : s.core .retained = 0) :
    Results epoch s events ∧
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout (run s events) ∧
      (run s events).core .phase = 0 ∧ (run s events).core .retained = 0 ∧
      counters (run s events) = accounting s (counters s) events := by
  induction admitted generalizing epoch
  case nil => exact ⟨True.intro, installed, phase, retained, rfl⟩
  case cons accepted tail ih =>
    rename_i before event restEvents
    have head := event_result epoch installed accepted
    have idle := result_idle head
    have rest := ih (event.nextEpoch epoch) (result_installed head) idle.1 idle.2
    refine ⟨⟨head, rest.1⟩, rest.2.1, rest.2.2.1, rest.2.2.2.1, ?_⟩
    change counters (run (event.after before) restEvents) = _
    rw [rest.2.2.2.2]
    change accounting (event.after before) (counters (event.after before)) restEvents = _
    rw [result_counters head]
    rfl

theorem run_eq_inputs (s : SramState.State) (events : List Event) :
    run s events = s.run (events.flatMap Event.inputs) := by
  induction events generalizing s
  case nil => rfl
  case cons event rest ih =>
    have head : event.after s = s.run event.inputs := by
      cases event
      case round round => exact round.after_eq_run s
      case reload batch => exact batch.after_eq_run s
    change run (event.after s) rest = s.run (event.inputs ++ rest.flatMap Event.inputs)
    rw [ih, head]
    simp [SramState.State.run, List.foldl_append]

theorem boot_trace {s : SramState.State} {batch : I2cReloadSession.Batch}
    (boot : I2cReloadSession.Admitted s batch) {events : List Event}
    (admitted : AdmittedTrace (batch.after s) events) (epoch : Nat) :
    Results (epoch + 1) (batch.after s) events ∧
      Refinement.InstalledSram I2cSource.source I2cCertificate.layout (run (batch.after s) events) ∧
      (run (batch.after s) events).core .phase = 0 ∧
      (run (batch.after s) events).core .retained = 0 ∧
      counters (run (batch.after s) events) = accounting (batch.after s) (counters (batch.after s)) events :=
  trace_result admitted (epoch + 1) boot.installed boot.idle.1 boot.idle.2

end Pinwheel.Hardware.Buffered.I2cSessionTrace
