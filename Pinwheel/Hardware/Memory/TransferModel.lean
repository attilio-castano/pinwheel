import Pinwheel.Hardware.Memory.StreamModel
import Pinwheel.Hardware.Memory.TransferRange
import Pinwheel.Hardware.Stream.ElasticCircuit

/-! Serial, non-overlapping-in-flight transfer control for separate exclusively
owned source and destination memories. The open controller has no payload
register: the source response holds the word while the combinational `Map`
drives the destination write. Reset cancels protocol work without initializing
or rolling back memory. Statements about source values use an explicit fixed
snapshot, never a reset-based initialization assumption.
-/
namespace Pinwheel.Hardware.Memory.TransferModel

structure RawCommand (a : Nat) where
  sourceBase : BitVec a
  destinationBase : BitVec a
  length : BitVec (a+1)
  deriving DecidableEq, Repr

structure Config (a : Nat) where
  sourceBase : BitVec a
  destinationBase : BitVec a
  length : Nat
  sourceFits : length ≤ 2^a - sourceBase.toNat
  destinationFits : length ≤ 2^a - destinationBase.toNat

def Config.sourceRange (c : Config a) : TransferRange.Range a := ⟨c.sourceBase, c.length, c.sourceFits⟩
def Config.destinationRange (c : Config a) : TransferRange.Range a :=
  ⟨c.destinationBase, c.length, c.destinationFits⟩

def decode (c : RawCommand a) : Option (Config a) :=
  if hs : c.length.toNat ≤ 2^a - c.sourceBase.toNat then
    if hd : c.length.toNat ≤ 2^a - c.destinationBase.toNat then
      some ⟨c.sourceBase, c.destinationBase, c.length.toNat, hs, hd⟩
    else none
  else none

def emptyConfig (a : Nat) : Config a := ⟨0, 0, 0, Nat.zero_le _, Nat.zero_le _⟩

inductive Phase where
  | idle | issueRead | transfer
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- Only configuration, progress, phase, and one-cycle status pulses are stored.
In particular this type has no payload-width parameter or payload register. -/
structure Control (a : Nat) where
  phase : Phase
  config : Config a
  index : Nat
  done : Bool
  error : Bool

def initialControl (a : Nat) : Control a := ⟨.idle, emptyConfig a, 0, false, false⟩

def Control.Valid (s : Control a) : Prop :=
  s.index ≤ s.config.length ∧ (s.phase = .idle ↔ s.index = s.config.length) ∧
    (s.done = true → s.phase = .idle) ∧ (s.error = true → s.phase = .idle)

structure Input (a wi : Nat) where
  reset : Bool
  start : Option (RawCommand a)
  sourceReady : Bool
  sourceResponse : Option (BitVec wi)
  destinationReady : Bool

structure Output (a wo : Nat) where
  startReady : Bool
  busy : Bool
  done : Bool
  error : Bool
  sourceRead : Option (BitVec a)
  sourceResponseReady : Bool
  destinationWrite : Option (BitVec a × BitVec wo)
  deriving DecidableEq, Repr

def observe (m : Hardware.Stream.Map wi wo) (i : Input a wi) (s : Control a) : Output a wo :=
  if i.reset then ⟨false, false, false, false, none, false, none⟩
  else ⟨s.phase == .idle, s.phase != .idle, s.done, s.error,
    if s.phase = .issueRead then some (s.config.sourceRange.index s.index) else none,
    s.phase == .transfer && i.destinationReady,
    if s.phase = .transfer then
      i.sourceResponse.map (fun value => (s.config.destinationRange.index s.index, m.function value))
    else none⟩

def step (i : Input a wi) (s : Control a) : Control a :=
  if i.reset then initialControl a
  else
    let cleared := { s with done := false, error := false }
    match s.phase with
    | .idle => match i.start with
      | none => cleared
      | some command => match decode command with
        | none => { initialControl a with error := true }
        | some config =>
          ⟨if config.length = 0 then .idle else .issueRead, config, 0, config.length == 0, false⟩
    | .issueRead => if i.sourceReady then { cleared with phase := .transfer } else cleared
    | .transfer =>
      if i.sourceResponse.isSome && i.destinationReady then
        ⟨if s.index+1 < s.config.length then .issueRead else .idle,
          s.config, s.index+1, decide (s.index+1 ≥ s.config.length), false⟩
      else cleared

def committed (i : Input a wi) (s : Control a) : Bool :=
  !i.reset && s.phase == .transfer && i.sourceResponse.isSome && i.destinationReady

def openComponent (m : Hardware.Stream.Map wi wo) : Timed.Component (Input a wi) (Control a) (Output a wo) :=
  ⟨step, observe m⟩

structure HostInput (a : Nat) where
  reset : Bool
  start : Option (RawCommand a)

structure State (a wi wo : Nat) where
  control : Control a
  source : StreamModel.State a wi
  destination : StreamModel.State a wo

def initialState (source : Sram.State a wi) (destination : Sram.State a wo) : State a wi wo :=
  ⟨initialControl a, ⟨source, false⟩, ⟨destination, false⟩⟩

/-- The destination response channel is always drained. No host can issue
requests to either memory in this closed composition. -/
def feedback (i : HostInput a) (s : State a wi wo) : Input a wi :=
  let destinationReady := StreamModel.ready true s.destination
  ⟨i.reset, i.start,
    StreamModel.ready (s.control.phase == .transfer && destinationReady) s.source,
    StreamModel.offer s.source, destinationReady⟩

def sourceInput (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo) : StreamModel.Input a wi :=
  let o := observe m (feedback i s) s.control
  ⟨i.reset, o.sourceRead.map StreamModel.Request.read, o.sourceResponseReady⟩

def destinationInput (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo) :
    StreamModel.Input a wo :=
  let o := observe m (feedback i s) s.control
  ⟨i.reset, o.destinationWrite.map (fun (address, value) => .write address value), true⟩

def closedStep (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo) : State a wi wo :=
  ⟨step (feedback i s) s.control,
    StreamModel.step (sourceInput m i s) s.source,
    StreamModel.step (destinationInput m i s) s.destination⟩

def component (m : Hardware.Stream.Map wi wo) :
    Timed.Component (HostInput a) (State a wi wo) (Output a wo) :=
  ⟨closedStep m, fun i s => observe m (feedback i s) s.control⟩

def idleAdvance (s : State a wi wo) : State a wi wo :=
  ⟨{ s.control with done := false, error := false }, s.source, ⟨s.destination.memory, false⟩⟩

def readAdvance (s : State a wi wo) : State a wi wo :=
  ⟨{ s.control with phase := .transfer, done := false, error := false },
    ⟨⟨s.source.memory.contents,
      s.source.memory.contents (s.control.config.sourceRange.index s.control.index)⟩, true⟩,
    ⟨s.destination.memory, false⟩⟩

def writeAdvance (m : Hardware.Stream.Map wi wo) (s : State a wi wo) : State a wi wo :=
  ⟨⟨if s.control.index+1 < s.control.config.length then .issueRead else .idle,
      s.control.config, s.control.index+1, decide (s.control.index+1 ≥ s.control.config.length), false⟩,
    ⟨s.source.memory, false⟩,
    ⟨SinglePort.step s.destination.memory
      (.write (s.control.config.destinationRange.index s.control.index) (m.function s.source.memory.q)), false⟩⟩

theorem closed_idle (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo)
    (hr : i.reset = false) (hp : s.control.phase = .idle) (hi : i.start = none) :
    closedStep m i s = idleAdvance s := by
  cases hs : s.source.pending <;>
    simp [closedStep, idleAdvance, feedback, step, sourceInput, destinationInput, observe,
      StreamModel.step, StreamModel.command, StreamModel.ready, StreamModel.offer,
      SinglePort.step, hr, hp, hi, hs]
  all_goals rw [← hs]

theorem closed_read (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo)
    (hr : i.reset = false) (hp : s.control.phase = .issueRead) (hs : s.source.pending = false) :
    closedStep m i s = readAdvance s := by
  simp [closedStep, readAdvance, feedback, step, sourceInput, destinationInput, observe,
    StreamModel.step, StreamModel.command, StreamModel.ready, StreamModel.offer,
    StreamModel.Request.command, StreamModel.Request.isRead, SinglePort.step, Sram.State.step,
    hr, hp, hs]

theorem closed_write (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo)
    (hr : i.reset = false) (hp : s.control.phase = .transfer) (hs : s.source.pending = true) :
    closedStep m i s = writeAdvance m s := by
  simp [closedStep, writeAdvance, feedback, step, sourceInput, destinationInput, observe,
    StreamModel.step, StreamModel.command, StreamModel.ready, StreamModel.offer,
    StreamModel.Request.command, StreamModel.Request.isRead, SinglePort.step, Sram.State.step,
    hr, hp, hs]

def startAdvance (config : Config a) (s : State a wi wo) : State a wi wo :=
  ⟨⟨if config.length = 0 then .idle else .issueRead, config, 0, config.length == 0, false⟩,
    s.source, ⟨s.destination.memory, false⟩⟩

theorem closed_start (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo)
    (command : RawCommand a) (config : Config a) (hr : i.reset = false)
    (hp : s.control.phase = .idle) (hi : i.start = some command) (hc : decode command = some config) :
    closedStep m i s = startAdvance config s := by
  cases hs : s.source.pending <;>
    simp [closedStep, startAdvance, feedback, step, sourceInput, destinationInput, observe,
      StreamModel.step, StreamModel.command, StreamModel.ready, StreamModel.offer,
      SinglePort.step, hr, hp, hi, hc, hs]
  all_goals rw [← hs]

/-- A session retains the accepted configuration and fixed memory snapshots.
Idle is included only at full completion. Starting a new command begins a new
session, while reset preserves this prefix physically but discards control. -/
def Session (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo) : Prop :=
  s.control.config = config ∧ s.control.Valid ∧
  s.source.memory.contents = source ∧
  TransferRange.Patched config.destinationRange initialDestination
    (TransferRange.copyValue config.sourceRange source m.function) s.control.index s.destination.memory.contents ∧
  s.source.pending = (s.control.phase == .transfer) ∧ s.destination.pending = false ∧
  (s.control.phase = .transfer → s.source.memory.q = source (config.sourceRange.index s.control.index))

/-- A new accepted start belongs to a new session; busy start offers are ignored.
Reset is handled separately because it preserves the old committed prefix
while discarding the active controller configuration. -/
theorem session_step (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo)
    (i : HostInput a) (h : Session m config source initialDestination s)
    (hr : i.reset = false) (hi : s.control.phase = .idle → i.start = none) :
    Session m config source initialDestination (closedStep m i s) := by
  rcases h with ⟨hc, hv, hsource, hpatch, hpending, hdestination, hq⟩
  cases hp : s.control.phase with
  | idle =>
    rw [closed_idle m i s hr hp (hi hp)]
    simp [Session, idleAdvance, Control.Valid, hp, hc, hsource, hpatch, hpending]
    exact ⟨by simpa [hc] using hv.1, by simpa [hp, hc] using hv.2.1⟩
  | issueRead =>
    have hs : s.source.pending = false := by
      simpa only [hp, show (Phase.issueRead == Phase.transfer) = false from rfl] using hpending
    rw [closed_read m i s hr hp hs]
    simp [Session, readAdvance, Control.Valid, hc, hsource, hpatch]
    simp [Control.Valid, hp, hc] at hv
    exact ⟨hv.1, hv.2.1⟩
  | transfer =>
    have hs : s.source.pending = true := by simpa [hp] using hpending
    have hk : s.control.index < config.length := by
      simp [Control.Valid, hp, hc] at hv
      omega
    have hqv := hq hp
    have nextPatch := TransferRange.copy_patch_step config.sourceRange config.destinationRange
      source initialDestination s.destination.memory.contents m.function rfl s.control.index hk hpatch
    rw [closed_write m i s hr hp hs]
    by_cases hn : s.control.index+1 < config.length
    all_goals simp [Session, writeAdvance, Control.Valid, hc, hsource, hqv,
      SinglePort.step, Sram.State.step, hn, nextPatch]
    all_goals omega

theorem started_session (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo)
    (command : RawCommand a) (config : Config a) (hr : i.reset = false)
    (hp : s.control.phase = .idle) (hs : s.source.pending = false)
    (hi : i.start = some command) (hc : decode command = some config) :
    Session m config s.source.memory.contents s.destination.memory.contents (closedStep m i s) := by
  rw [closed_start m i s command config hr hp hi hc]
  by_cases hz : config.length = 0
  all_goals simp [Session, startAdvance, Control.Valid, hs, hz, TransferRange.patched_zero,
    show (Phase.issueRead == Phase.transfer) = false from rfl]
  omega

/-- Completion means the entire checked destination range has been patched,
including the zero-length session accepted directly into Idle. -/
theorem completed_patch (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo)
    (h : Session m config source initialDestination s) (hd : s.control.done = true) :
    TransferRange.Patched config.destinationRange initialDestination
      (TransferRange.copyValue config.sourceRange source m.function) config.length s.destination.memory.contents := by
  have hk := h.2.1.2.1.mp (h.2.1.2.2.1 hd)
  simpa only [h.1, hk] using h.2.2.2.1

theorem reset_state (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo)
    (hr : i.reset = true) : closedStep m i s = initialState s.source.memory s.destination.memory := by
  simp [closedStep, initialState, feedback, step, sourceInput, destinationInput, observe,
    StreamModel.step, StreamModel.command, SinglePort.step, hr]

theorem reset_observe (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo)
    (hr : i.reset = true) : (component m).observe i s = ⟨false, false, false, false, none, false, none⟩ := by
  simp [component, observe, feedback, hr]

/-- The old session's ghost configuration and committed count still describe
memory after abort, even though control returns to its empty configuration. -/
theorem abort_preserves_prefix (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo)
    (i : HostInput a) (h : Session m config source initialDestination s) (hr : i.reset = true) :
    (closedStep m i s).source.memory = s.source.memory ∧
    (closedStep m i s).destination.memory = s.destination.memory ∧
    TransferRange.Patched config.destinationRange initialDestination
      (TransferRange.copyValue config.sourceRange source m.function) s.control.index
      (closedStep m i s).destination.memory.contents := by
  rw [reset_state m i s hr]
  exact ⟨rfl, rfl, h.2.2.2.1⟩

def run (m : Hardware.Stream.Map wi wo) (s : State a wi wo) (inputs : List (HostInput a)) : State a wi wo :=
  (component m).run s inputs

theorem initial_no_start (m : Hardware.Stream.Map wi wo) (i : HostInput a)
    (source : Sram.State a wi) (destination : Sram.State a wo) (hi : i.start = none) :
    closedStep m i (initialState source destination) = initialState source destination := by
  cases hr : i.reset
  · rw [closed_idle m i _ hr rfl hi]
    rfl
  · exact reset_state m i _ hr

/-- Once reset aborts a transfer, no old read or write can reappear before a
new start. Repeated resets are allowed, and neither memory nor Q is cleared. -/
theorem no_start_run (m : Hardware.Stream.Map wi wo) (source : Sram.State a wi)
    (destination : Sram.State a wo) (inputs : List (HostInput a))
    (hi : ∀ i ∈ inputs, i.start = none) :
    run m (initialState source destination) inputs = initialState source destination := by
  induction inputs with
  | nil => rfl
  | cons i rest ih =>
    change run m (closedStep m i (initialState source destination)) rest = _
    rw [initial_no_start m i source destination (hi i (by simp))]
    exact ih (fun j hj => hi j (by simp [hj]))

def quiet : HostInput a := ⟨false, none⟩

/-- Clock the exclusively owned two-memory composition without issuing a new
command or reset. No external memory-service assumption is needed here. -/
def advance (m : Hardware.Stream.Map wi wo) : Nat → State a wi wo → State a wi wo
  | 0, s => s
  | edges+1, s => advance m edges (closedStep m quiet s)

theorem complete_after (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo)
    (remaining : Nat) (s : State a wi wo)
    (h : Session m config source initialDestination s)
    (hb : s.control.phase ≠ .transfer) (hk : s.control.index + remaining = config.length) :
    let result := advance m (2*remaining) s
    Session m config source initialDestination result ∧ result.control.phase = .idle ∧
      result.control.index = config.length ∧ (0 < remaining → result.control.done = true) := by
  induction remaining generalizing s with
  | zero =>
    simp only [advance]
    have he : s.control.index = config.length := by omega
    have hp : s.control.phase = .idle := h.2.1.2.1.mpr (by simpa only [h.1] using he)
    exact ⟨h, hp, he, by omega⟩
  | succ n ih =>
    have hp : s.control.phase = .issueRead := by
      cases he : s.control.phase with
      | idle =>
        have hfinish := h.2.1.2.1.mp he
        rw [h.1] at hfinish
        omega
      | issueRead => rfl
      | transfer => exact False.elim (hb he)
    have hs : s.source.pending = false := by
      simpa only [hp, show (Phase.issueRead == Phase.transfer) = false from rfl] using h.2.2.2.2.1
    let t := writeAdvance m (readAdvance s)
    have ht : closedStep m quiet (closedStep m quiet s) = t := by
      rw [closed_read m quiet s rfl hp hs, closed_write m quiet (readAdvance s) rfl rfl rfl]
    have htSession : Session m config source initialDestination t := by
      rw [← ht]
      exact session_step m config source initialDestination _ quiet
        (session_step m config source initialDestination s quiet h rfl (fun _ => rfl))
        rfl (fun _ => rfl)
    have htPhase : t.control.phase ≠ .transfer := by
      dsimp [t, writeAdvance, readAdvance]
      split <;> decide
    have htIndex : t.control.index = s.control.index+1 := rfl
    have result := ih t htSession htPhase (by rw [htIndex]; omega)
    rw [show 2*(n+1) = 2*n+2 by omega]
    simp only [advance]
    rw [ht]
    refine ⟨result.1, result.2.1, result.2.2.1, ?_⟩
    intro _
    by_cases hn : n = 0
    · subst n
      change t.control.done = true
      simp [t, writeAdvance, readAdvance, h.1]
      omega
    · exact result.2.2.2 (by omega)

/-- A successfully accepted command completes after exactly two further edges
per word. Zero length already has its done pulse at the acceptance edge. -/
theorem started_complete (m : Hardware.Stream.Map wi wo) (i : HostInput a) (s : State a wi wo)
    (command : RawCommand a) (config : Config a) (hr : i.reset = false)
    (hp : s.control.phase = .idle) (hs : s.source.pending = false)
    (hi : i.start = some command) (hc : decode command = some config) :
    let result := advance m (2*config.length) (closedStep m i s)
    result.control.done = true ∧ result.control.phase = .idle ∧
      TransferRange.Patched config.destinationRange s.destination.memory.contents
        (TransferRange.copyValue config.sourceRange s.source.memory.contents m.function)
        config.length result.destination.memory.contents := by
  have hsession := started_session m i s command config hr hp hs hi hc
  have hphase : (closedStep m i s).control.phase ≠ .transfer := by
    rw [closed_start m i s command config hr hp hi hc]
    dsimp [startAdvance]
    split <;> decide
  have hindex : (closedStep m i s).control.index = 0 := by
    rw [closed_start m i s command config hr hp hi hc]
    rfl
  have hcomplete := complete_after m config s.source.memory.contents s.destination.memory.contents
    config.length (closedStep m i s) hsession hphase (by rw [hindex]; omega)
  have hdone : (advance m (2*config.length) (closedStep m i s)).control.done = true := by
    by_cases hz : config.length = 0
    · simp [hz, advance, closed_start m i s command config hr hp hi hc, startAdvance]
    · exact hcomplete.2.2.2 (by omega)
  exact ⟨hdone, hcomplete.2.1, completed_patch m config _ _ _ hcomplete.1 hdone⟩

/-- Open-controller progress requires these explicit services. This predicate
does not assert that an arbitrary environment eventually supplies them. -/
def Service (i : Input a wi) (s : Control a) : Prop :=
  match s.phase with
  | .idle => True
  | .issueRead => i.sourceReady = true
  | .transfer => i.sourceResponse.isSome = true ∧ i.destinationReady = true

def Control.work (s : Control a) : Nat :=
  match s.phase with
  | .idle => 0
  | .issueRead => 2 * (s.config.length - s.index)
  | .transfer => 2 * (s.config.length - s.index) - 1

theorem work_step (i : Input a wi) (s : Control a) (hv : s.Valid)
    (hr : i.reset = false) (ha : s.phase ≠ .idle) (hs : Service i s) :
    (step i s).work + 1 = s.work := by
  cases hp : s.phase <;> simp_all [Service, Control.work, step, Control.Valid]
  all_goals first | omega | (by_cases hn : s.index + 1 < s.config.length <;> simp [hn] <;> omega)

theorem step_valid (i : Input a wi) (s : Control a) (hv : s.Valid) : (step i s).Valid := by
  cases hr : i.reset <;> simp [step, Control.Valid, initialControl, emptyConfig, hr]
  cases hp : s.phase <;> simp [hp, Control.Valid] at hv ⊢
  all_goals split <;> try simp_all
  all_goals first | omega | (split <;> simp_all)
  omega

theorem work_step_lt (i : Input a wi) (s : Control a) (hv : s.Valid)
    (hr : i.reset = false) (ha : s.phase ≠ .idle) (hs : Service i s) :
    (step i s).work < s.work := by
  have h := work_step i s hv hr ha hs
  omega

theorem work_zero_iff (s : Control a) (hv : s.Valid) :
    s.work = 0 ↔ s.phase = .idle := by
  cases hp : s.phase <;> simp [Control.work, Control.Valid, hp] at * <;> omega

theorem work_stalled (i : Input a wi) (s : Control a)
    (hr : i.reset = false) (hs : ¬Service i s) :
    (step i s).work = s.work := by
  cases hp : s.phase <;> simp_all [Service, Control.work, step]
  cases hv : i.sourceResponse.isSome <;> simp_all

/-- The concrete memory wiring supplies service in every active phase. This
uses the coherent pending-response invariant, not a power-up assumption. -/
theorem closed_service (m : Hardware.Stream.Map wi wo) (config : Config a)
    (source : Contents a wi) (initialDestination : Contents a wo) (s : State a wi wo)
    (i : HostInput a) (h : Session m config source initialDestination s) :
    Service (feedback i s) s.control := by
  have hs := h.2.2.2.2.1
  cases hp : s.control.phase <;>
    simp [Service, feedback, StreamModel.ready, StreamModel.offer, hp, hs]

theorem busy_start_ignored (i : Input a wi) (s : Control a) (h : s.phase ≠ .idle) :
    step i s = step { i with start := none } s := by
  cases hp : s.phase <;> simp_all [step]

theorem invalid_start (i : Input a wi) (s : Control a) (command : RawCommand a)
    (hr : i.reset = false) (hp : s.phase = .idle) (hi : i.start = some command)
    (hc : decode command = none) : step i s = { initialControl a with error := true } := by
  simp [step, hr, hp, hi, hc]

theorem idle_no_requests (m : Hardware.Stream.Map wi wo) (i : Input a wi) (s : Control a)
    (hp : s.phase = .idle) : (observe m i s).sourceRead = none ∧ (observe m i s).destinationWrite = none := by
  cases hr : i.reset <;> simp [observe, hr, hp]

theorem idle_clear_status (i : Input a wi) (s : Control a) (hr : i.reset = false)
    (hp : s.phase = .idle) (hi : i.start = none) :
    (step i s).done = false ∧ (step i s).error = false := by
  simp [step, hr, hp, hi]

end Pinwheel.Hardware.Memory.TransferModel
