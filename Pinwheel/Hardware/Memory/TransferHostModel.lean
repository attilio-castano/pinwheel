import Pinwheel.Hardware.Memory.TransferModel

/-! Host loading and readback around the exclusively owned transfer model.
An offered start blocks new host requests immediately. Already pending host
responses remain visible until their host consumes them; start is accepted
only on a later edge with both pre-edge pending bits clear. Busy edges reserve
both memories for the controller. Reset cancels protocol work and preserves
every memory word and Q, including a partially committed transfer prefix.
-/
namespace Pinwheel.Hardware.Memory.TransferHostModel

open TransferModel (RawCommand Config Phase Session)

abbrev State := TransferModel.State

structure Input (a wi wo : Nat) where
  reset : Bool
  start : Option (RawCommand a)
  sourceRequest : Option (StreamModel.Request a wi)
  sourceResponseReady : Bool
  destinationRequest : Option (StreamModel.Request a wo)
  destinationResponseReady : Bool

structure Output (wi wo : Nat) where
  startReady : Bool
  busy : Bool
  done : Bool
  error : Bool
  source : StreamModel.Output wi
  destination : StreamModel.Output wo
  deriving DecidableEq, Repr

/-- Readiness uses pre-edge pending bits, even when both responses will retire
on this edge. It does not depend on whether a start or host request is offered. -/
def startReady (i : Input a wi wo) (s : State a wi wo) : Bool :=
  !i.reset && s.control.phase == .idle && !s.source.pending && !s.destination.pending

def acceptedStart (i : Input a wi wo) (s : State a wi wo) : Bool :=
  startReady i s && i.start.isSome

def controllerInput (i : Input a wi wo) (s : State a wi wo) : TransferModel.HostInput a :=
  ⟨i.reset, if startReady i s then i.start else none⟩

/-- These gated inputs are used only while idle without an accepted start.
Response readiness remains connected when an offered start blocks requests. -/
def sourceInput (i : Input a wi wo) : StreamModel.Input a wi :=
  ⟨i.reset, if i.start.isSome then none else i.sourceRequest, i.sourceResponseReady⟩

def destinationInput (i : Input a wi wo) : StreamModel.Input a wo :=
  ⟨i.reset, if i.start.isSome then none else i.destinationRequest, i.destinationResponseReady⟩

def observe (i : Input a wi wo) (s : State a wi wo) : Output wi wo :=
  if i.reset then ⟨false, false, false, false, ⟨false, none⟩, ⟨false, none⟩⟩
  else
    let idle := s.control.phase == .idle
    ⟨startReady i s, !idle, s.control.done, s.control.error,
      if idle then
        ⟨!i.start.isSome && StreamModel.ready i.sourceResponseReady s.source, StreamModel.offer s.source⟩
      else ⟨false, none⟩,
      if idle then
        ⟨!i.start.isSome && StreamModel.ready i.destinationResponseReady s.destination,
          StreamModel.offer s.destination⟩
      else ⟨false, none⟩⟩

def step (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo) : State a wi wo :=
  if i.reset || s.control.phase != .idle || acceptedStart i s then
    TransferModel.closedStep m (controllerInput i s) s
  else
    ⟨TransferModel.step (TransferModel.feedback (controllerInput i s) s) s.control,
      StreamModel.step (sourceInput i) s.source,
      StreamModel.step (destinationInput i) s.destination⟩

def component (m : Hardware.Stream.Map wi wo) :
    Timed.Component (Input a wi wo) (State a wi wo) (Output wi wo) := ⟨step m, observe⟩

theorem start_ready_iff (i : Input a wi wo) (s : State a wi wo) :
    startReady i s = true ↔ i.reset = false ∧ s.control.phase = .idle ∧
      s.source.pending = false ∧ s.destination.pending = false := by
  simp [startReady, Bool.and_eq_true, and_assoc]

theorem accepted_eq_closed (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo)
    (ha : acceptedStart i s = true) :
    step m i s = TransferModel.closedStep m ⟨i.reset, i.start⟩ s := by
  have hr : startReady i s = true := (Bool.and_eq_true_iff.mp ha).1
  simp [step, ha, controllerInput, hr]

theorem busy_eq_closed (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo)
    (hb : s.control.phase ≠ .idle) :
    step m i s = TransferModel.closedStep m ⟨i.reset, none⟩ s := by
  simp [step, controllerInput, startReady, hb]

theorem busy_hides_host (i : Input a wi wo) (s : State a wi wo) (hb : s.control.phase ≠ .idle) :
    (observe i s).source = ⟨false, none⟩ ∧ (observe i s).destination = ⟨false, none⟩ := by
  cases hr : i.reset <;> simp [observe, hr, hb]

theorem start_blocks_requests (i : Input a wi wo) (s : State a wi wo)
    (command : RawCommand a) (hi : i.start = some command) :
    (observe i s).source.ready = false ∧ (observe i s).destination.ready = false := by
  cases hr : i.reset <;> cases hp : s.control.phase <;> simp [observe, hr, hp, hi]

theorem idle_responses_visible (i : Input a wi wo) (s : State a wi wo)
    (hr : i.reset = false) (hp : s.control.phase = .idle) :
    (observe i s).source.offered = StreamModel.offer s.source ∧
      (observe i s).destination.offered = StreamModel.offer s.destination := by
  simp [observe, hr, hp]

theorem idle_host_observe (i : Input a wi wo) (s : State a wi wo)
    (hr : i.reset = false) (hp : s.control.phase = .idle) (hi : i.start = none) :
    (observe i s).source = (StreamModel.component a wi).observe (sourceInput i) s.source ∧
    (observe i s).destination = (StreamModel.component a wo).observe (destinationInput i) s.destination := by
  simp [observe, sourceInput, destinationInput, StreamModel.component, StreamModel.machine,
    Hardware.Stream.Machine.component, hr, hp, hi]

theorem idle_host_step (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo)
    (hr : i.reset = false) (hp : s.control.phase = .idle) (ha : acceptedStart i s = false) :
    step m i s =
      ⟨{ s.control with done := false, error := false },
        StreamModel.step (sourceInput i) s.source, StreamModel.step (destinationInput i) s.destination⟩ := by
  have hi : (controllerInput i s).start = none := by
    cases hc : startReady i s <;> cases ho : i.start <;>
      simp_all [acceptedStart, controllerInput]
  have hir : (controllerInput i s).reset = false := hr
  simp [step, hr, hp, ha, TransferModel.step, TransferModel.feedback, hi, hir]

theorem reset_state (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo)
    (hr : i.reset = true) :
    step m i s = TransferModel.initialState s.source.memory s.destination.memory := by
  simpa [step, hr] using TransferModel.reset_state m (controllerInput i s) s hr

theorem reset_observe (i : Input a wi wo) (s : State a wi wo) (hr : i.reset = true) :
    observe i s = ⟨false, false, false, false, ⟨false, none⟩, ⟨false, none⟩⟩ := by
  simp [observe, hr]

theorem started_session (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo)
    (command : RawCommand a) (config : Config a) (ha : acceptedStart i s = true)
    (hi : i.start = some command) (hc : TransferModel.decode command = some config) :
    Session m config s.source.memory.contents s.destination.memory.contents (step m i s) := by
  have hr := (start_ready_iff i s).mp (Bool.and_eq_true_iff.mp ha).1
  rw [accepted_eq_closed m i s ha]
  exact TransferModel.started_session m ⟨i.reset, i.start⟩ s command config hr.1 hr.2.1 hr.2.2.1 hi hc

theorem abort_preserves_prefix (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo)
    (i : Input a wi wo) (h : Session m config source initialDestination s) (hr : i.reset = true) :
    (step m i s).source.memory = s.source.memory ∧
    (step m i s).destination.memory = s.destination.memory ∧
    TransferRange.Patched config.destinationRange initialDestination
      (TransferRange.copyValue config.sourceRange source m.function) s.control.index
      (step m i s).destination.memory.contents := by
  rw [reset_state m i s hr]
  exact ⟨rfl, rfl, h.2.2.2.1⟩

private theorem no_request_memory (i : StreamModel.Input a w) (s : StreamModel.State a w)
    (hi : i.offered = none) : (StreamModel.step i s).memory = s.memory := by
  cases hr : i.reset <;> cases hc : StreamModel.ready i.ready s <;>
    simp [StreamModel.step, StreamModel.command, SinglePort.step, hr, hc, hi]

/-- A host request to one memory cannot modify the other memory, including Q.
The other protocol pending bit may still clear when its response is consumed. -/
theorem idle_memory_separation (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo)
    (hr : i.reset = false) (hp : s.control.phase = .idle) (ha : acceptedStart i s = false) :
    (i.sourceRequest = none → (step m i s).source.memory = s.source.memory) ∧
    (i.destinationRequest = none → (step m i s).destination.memory = s.destination.memory) := by
  rw [idle_host_step m i s hr hp ha]
  exact ⟨fun h => no_request_memory (sourceInput i) s.source (by simp [sourceInput, h]),
    fun h => no_request_memory (destinationInput i) s.destination (by simp [destinationInput, h])⟩

/-- A blocked start does not discard host responses: it can proceed on the
following edge after both hosts consume their pending responses. -/
theorem waiting_drains (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo)
    (command : RawCommand a) (hr : i.reset = false) (hp : s.control.phase = .idle)
    (ha : acceptedStart i s = false) (hi : i.start = some command)
    (hs : i.sourceResponseReady = true) (hd : i.destinationResponseReady = true) :
    (step m i s).source.memory = s.source.memory ∧
    (step m i s).destination.memory = s.destination.memory ∧
    startReady i (step m i s) = true := by
  rw [idle_host_step m i s hr hp ha]
  simp [startReady, sourceInput, destinationInput, StreamModel.step, StreamModel.command,
    StreamModel.ready, SinglePort.step, hr, hp, hi, hs, hd]

/-- With both memories drained, invalid commands change only controller status
and configuration. The entire source and destination memory states are retained. -/
theorem invalid_start_preserves_memory (m : Hardware.Stream.Map wi wo) (i : Input a wi wo)
    (s : State a wi wo) (command : RawCommand a) (ha : acceptedStart i s = true)
    (hi : i.start = some command) (hc : TransferModel.decode command = none) :
    step m i s = ⟨{ TransferModel.initialControl a with error := true }, s.source, s.destination⟩ := by
  have hr := (start_ready_iff i s).mp (Bool.and_eq_true_iff.mp ha).1
  rw [accepted_eq_closed m i s ha]
  simp [TransferModel.closedStep, TransferModel.step, TransferModel.feedback,
    TransferModel.sourceInput, TransferModel.destinationInput, TransferModel.observe,
    StreamModel.step, StreamModel.command, StreamModel.ready, StreamModel.offer,
    SinglePort.step, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hi, hc]
  exact ⟨by rw [← hr.2.2.1], by rw [← hr.2.2.2]⟩

private theorem idle_empty_eq_closed (m : Hardware.Stream.Map wi wo) (i : Input a wi wo)
    (s : State a wi wo) (hr : i.reset = false) (hp : s.control.phase = .idle)
    (hs : s.source.pending = false) (hd : s.destination.pending = false)
    (hi : i.start = none) (his : i.sourceRequest = none) (hid : i.destinationRequest = none) :
    step m i s = TransferModel.closedStep m ⟨i.reset, none⟩ s := by
  rw [idle_host_step m i s hr hp (by simp [acceptedStart, hi]),
    TransferModel.closed_idle m ⟨i.reset, none⟩ s hr hp rfl]
  simp [sourceInput, destinationInput, TransferModel.idleAdvance, StreamModel.step,
    StreamModel.command, StreamModel.ready, SinglePort.step, hr, hi, his, hid, hs, hd]
  rw [← hs]

/-- During a session, arbitrary host offers are ignored while busy. At the
completed idle boundary the caller must withhold new starts and host requests
to continue treating the memories as reserved by that same session. -/
theorem session_eq_closed (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo)
    (i : Input a wi wo) (h : Session m config source initialDestination s)
    (hr : i.reset = false)
    (hi : s.control.phase = .idle →
      i.start = none ∧ i.sourceRequest = none ∧ i.destinationRequest = none) :
    step m i s = TransferModel.closedStep m ⟨i.reset, none⟩ s := by
  by_cases hp : s.control.phase = .idle
  · have hs : s.source.pending = false := by
      simpa only [hp, show (Phase.idle == Phase.transfer) = false from rfl] using h.2.2.2.2.1
    exact idle_empty_eq_closed m i s hr hp hs h.2.2.2.2.2.1 (hi hp).1 (hi hp).2.1 (hi hp).2.2
  · exact busy_eq_closed m i s hp

theorem session_step (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo)
    (i : Input a wi wo) (h : Session m config source initialDestination s)
    (hr : i.reset = false)
    (hi : s.control.phase = .idle →
      i.start = none ∧ i.sourceRequest = none ∧ i.destinationRequest = none) :
    Session m config source initialDestination (step m i s) := by
  rw [session_eq_closed m config source initialDestination s i h hr hi]
  exact TransferModel.session_step m config source initialDestination s ⟨i.reset, none⟩ h hr (fun _ => rfl)

theorem completed_patch (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo)
    (h : Session m config source initialDestination s) (hd : s.control.done = true) :
    TransferRange.Patched config.destinationRange initialDestination
      (TransferRange.copyValue config.sourceRange source m.function) config.length s.destination.memory.contents :=
  TransferModel.completed_patch m config source initialDestination s h hd

/-- Arbitrary host requests, start offers, and response backpressure cannot
delay active transfer progress. This requires a coherent accepted session,
not just an arbitrary busy control valuation. -/
theorem busy_progress (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo)
    (i : Input a wi wo) (h : Session m config source initialDestination s)
    (hr : i.reset = false) (hb : s.control.phase ≠ .idle) :
    (step m i s).control.work + 1 = s.control.work := by
  rw [busy_eq_closed m i s hb]
  exact TransferModel.work_step (TransferModel.feedback ⟨i.reset, none⟩ s) s.control h.2.1 hr hb
    (TransferModel.closed_service m config source initialDestination s ⟨i.reset, none⟩ h)

def quiet : Input a wi wo := ⟨false, none, none, true, none, true⟩

def advance (m : Hardware.Stream.Map wi wo) : Nat → State a wi wo → State a wi wo
  | 0, s => s
  | edges+1, s => advance m edges (step m quiet s)

theorem advance_eq_closed (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo)
    (h : Session m config source initialDestination s) (edges : Nat) :
    advance m edges s = TransferModel.advance m edges s := by
  induction edges generalizing s with
  | zero => rfl
  | succ n ih =>
    change advance m n (step m quiet s) = TransferModel.advance m n (TransferModel.closedStep m TransferModel.quiet s)
    rw [ih _ (session_step m config source initialDestination s quiet h rfl (fun _ => ⟨rfl, rfl, rfl⟩))]
    rw [session_eq_closed m config source initialDestination s quiet h rfl (fun _ => ⟨rfl, rfl, rfl⟩)]
    rfl

/-- The accepted edge excludes host requests and establishes the source-pending
precondition needed by the closed transfer theorem. Completion then takes two
further edges per word; zero length completes at acceptance. -/
theorem started_complete (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo)
    (command : RawCommand a) (config : Config a) (ha : acceptedStart i s = true)
    (hi : i.start = some command) (hc : TransferModel.decode command = some config) :
    let result := advance m (2*config.length) (step m i s)
    result.control.done = true ∧ result.control.phase = .idle ∧
      TransferRange.Patched config.destinationRange s.destination.memory.contents
        (TransferRange.copyValue config.sourceRange s.source.memory.contents m.function)
        config.length result.destination.memory.contents := by
  have hr := (start_ready_iff i s).mp (Bool.and_eq_true_iff.mp ha).1
  have hsession := started_session m i s command config ha hi hc
  dsimp only
  rw [advance_eq_closed m config _ _ _ hsession, accepted_eq_closed m i s ha]
  exact TransferModel.started_complete m ⟨i.reset, i.start⟩ s command config hr.1 hr.2.1 hr.2.2.1 hi hc

theorem control_valid (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo)
    (hv : s.control.Valid) : (step m i s).control.Valid := by
  unfold step
  split <;> exact TransferModel.step_valid (TransferModel.feedback (controllerInput i s) s) s.control hv

/-- Host commands cannot start the controller. After an abort, host loading and
readback may continue, but old transfer reads and writes cannot reappear. -/
theorem idle_without_start (m : Hardware.Stream.Map wi wo) (i : Input a wi wo) (s : State a wi wo)
    (hp : s.control.phase = .idle) (hi : i.start = none) :
    (step m i s).control.phase = .idle := by
  cases hr : i.reset
  · rw [idle_host_step m i s hr hp (by simp [acceptedStart, hi])]
    exact hp
  · rw [reset_state m i s hr]
    rfl

def run (m : Hardware.Stream.Map wi wo) (s : State a wi wo) (inputs : List (Input a wi wo)) : State a wi wo :=
  (component m).run s inputs

theorem no_start_stays_idle (m : Hardware.Stream.Map wi wo) (s : State a wi wo)
    (inputs : List (Input a wi wo)) (hp : s.control.phase = .idle)
    (hi : ∀ i ∈ inputs, i.start = none) : (run m s inputs).control.phase = .idle := by
  induction inputs generalizing s with
  | nil => exact hp
  | cons i rest ih =>
    change (run m (step m i s) rest).control.phase = .idle
    exact ih _ (idle_without_start m i s hp (hi i (by simp)))
      (fun j hj => hi j (by simp [hj]))

theorem no_stale_after_reset (m : Hardware.Stream.Map wi wo) (i : Input a wi wo)
    (s : State a wi wo) (inputs : List (Input a wi wo)) (hr : i.reset = true)
    (hi : ∀ j ∈ inputs, j.start = none) : (run m (step m i s) inputs).control.phase = .idle := by
  rw [reset_state m i s hr]
  exact no_start_stays_idle m _ inputs rfl hi

theorem initial_quiet (m : Hardware.Stream.Map wi wo) (source : Sram.State a wi)
    (destination : Sram.State a wo) :
    step m quiet (TransferModel.initialState source destination) = TransferModel.initialState source destination := by
  rw [idle_empty_eq_closed m quiet _ rfl rfl rfl rfl rfl rfl rfl]
  exact TransferModel.initial_no_start m _ source destination rfl

/-- Quiescent edges after reset retain words and Q exactly; reset is not an
initialization assumption or a rollback of the committed prefix. -/
theorem quiet_after_reset (m : Hardware.Stream.Map wi wo) (i : Input a wi wo)
    (s : State a wi wo) (hr : i.reset = true) (edges : Nat) :
    advance m edges (step m i s) = TransferModel.initialState s.source.memory s.destination.memory := by
  rw [reset_state m i s hr]
  induction edges with
  | zero => rfl
  | succ n ih => simpa only [advance, initial_quiet] using ih

end Pinwheel.Hardware.Memory.TransferHostModel
