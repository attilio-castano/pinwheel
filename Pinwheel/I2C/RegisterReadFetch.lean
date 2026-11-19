import Pinwheel.I2C.RegisterRead

/-! A timed observation of the existing combined I²C read. A pending fetch
holds the controller state and publishes its drive on a real wire clock,
but does not retire a protocol step or sample data. -/
namespace Pinwheel.I2C.RegisterReadFetch
open RegisterRead

inductive Tick where
  | step (peer : Pins)
  | pending (peer : Pins)
  deriving DecidableEq, Repr

def Tick.peer : Tick → Pins
  | .step peer | .pending peer => peer

def Tick.advance (cfg : Config) (request : RegisterRead.Request) (state : State) : Tick → State
  | .step peer => RegisterRead.step cfg state (resolve (pins request state.phase) peer)
  | .pending _ => state

structure Wire where
  drive : Pins
  bus : Bus
  deriving DecidableEq, Repr

structure Observation where
  wire : Wire
  capture : Option (Fin 16 × Bool)
  deriving DecidableEq, Repr

/-- The existing read specification samples on the closing edge of HIGH.
    A capture is indexed by that pre-edge observation, including the ACKs. -/
def observe (request : RegisterRead.Request) (state : State) (tick : Tick) : Observation :=
  let drive := pins request state.phase
  let bus := resolve drive tick.peer
  let capture := match tick, state.phase with
    | .step _, .high slot =>
      if bus.scl && state.remaining.val == 0 then (sampleAt slot).map (·, bus.sda) else none
    | _, _ => none
  ⟨⟨drive, bus⟩, capture⟩

/-- A reported capture is the bit written by the reference transition. -/
theorem capture_written (cfg : Config) (request : RegisterRead.Request) (state : State) (tick : Tick)
    (slot : Fin 16) (value : Bool) (captured : (observe request state tick).capture = some (slot, value)) :
    (tick.advance cfg request state).samples[slot.val] = value := by
  cases tick with
  | pending peer => simp [observe] at captured
  | step peer =>
    cases phase : state.phase <;> simp [observe, phase, Tick.peer] at captured
    case high cell =>
      obtain ⟨⟨clock, last⟩, ⟨index, atSlot, rfl, data⟩⟩ := captured
      simp [Tick.advance, RegisterRead.step, phase, clock, last, move, latch, atSlot, data]

def run (cfg : Config) (request : RegisterRead.Request) (state : State) (ticks : List Tick) : State :=
  ticks.foldl (Tick.advance cfg request) state

def trace (cfg : Config) (request : RegisterRead.Request) (state : State) : List Tick → List Observation
  | [] => []
  | tick :: more => observe request state tick :: trace cfg request (tick.advance cfg request state) more

theorem trace_length (cfg : Config) (request : RegisterRead.Request) (state : State) (ticks : List Tick) :
    (trace cfg request state ticks).length = ticks.length := by
  induction ticks generalizing state with
  | nil => rfl
  | cons tick more ih => simp only [trace, List.length_cons, ih]

/-- Keep each drive or resolved wire transition. Identical consecutive samples
    carry elapsed time but add no event to this projection. -/
def wireChangesFrom (before : Wire) : List Wire → List Wire
  | [] => []
  | current :: rest => if before = current then wireChangesFrom current rest
    else current :: wireChangesFrom current rest

def wireChanges (observations : List Observation) : List Wire :=
  match observations.map Observation.wire with
  | [] => []
  | first :: rest => first :: wireChangesFrom first rest

theorem trace_append (cfg : Config) (request : RegisterRead.Request) (state : State) (before after : List Tick) :
    trace cfg request state (before ++ after) =
      trace cfg request state before ++ trace cfg request (run cfg request state before) after := by
  induction before generalizing state with
  | nil => rfl
  | cons tick before ih =>
    rw [List.cons_append, trace, trace, List.cons_append, ih]
    rfl

private theorem run_pending (cfg : Config) (request : RegisterRead.Request) (state : State) (peer : Pins) (n : Nat) :
    run cfg request state (List.replicate n (.pending peer)) = state := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem trace_pending (cfg : Config) (request : RegisterRead.Request) (state : State) (peer : Pins) (n : Nat) :
    trace cfg request state (List.replicate n (.pending peer)) =
      List.replicate n (observe request state (.pending peer)) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (_ :: ·) ih

private theorem wireChangesFrom_insert (previous current : Wire) (before after : List Wire) (n : Nat) :
    wireChangesFrom previous (before ++ List.replicate n current ++ current :: after) =
      wireChangesFrom previous (before ++ current :: after) := by
  induction before generalizing previous with
  | nil =>
    induction n generalizing previous with
    | zero => rfl
    | succ n ih =>
      simp only [List.nil_append, List.replicate_succ, List.cons_append, wireChangesFrom]
      have repeated := ih current
      simp only [List.nil_append] at repeated
      rw [repeated]
      simp only [wireChangesFrom, ↓reduceIte]
  | cons first before ih =>
    simp only [List.cons_append, wireChangesFrom]
    rw [ih first]

private theorem wireChanges_insert (before after : List Observation) (next hold : Observation)
    (same : hold.wire = next.wire) (n : Nat) :
    wireChanges (before ++ List.replicate n hold ++ next :: after) =
      wireChanges (before ++ next :: after) := by
  simp only [wireChanges, List.map_append, List.map_cons, List.map_replicate, same]
  cases before with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.replicate_succ, List.cons_append]
      simpa only [List.nil_append, wireChangesFrom, ↓reduceIte] using
        congrArg (next.wire :: ·) (wireChangesFrom_insert next.wire next.wire [] (after.map Observation.wire) n)
  | cons first before =>
    simp only [List.map_cons, List.cons_append]
    rw [wireChangesFrom_insert]

private theorem no_capture_pending (sample : Observation) (n : Nat) (empty : sample.capture = none) :
    (List.replicate n sample).filterMap Observation.capture = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, empty, ih]

/-- Inserting real pending-fetch edges before resuming with the same peer
    drive duplicates just the observation at that cut. The later protocol
    steps see the same stage-aligned peer drives. -/
theorem insert_fetch_hold (cfg : Config) (request : RegisterRead.Request) (state : State)
    (before after : List Tick) (peer : Pins) (n : Nat) :
    let original := before ++ .step peer :: after
    let delayed := before ++ List.replicate n (.pending peer) ++ .step peer :: after
    let cut := run cfg request state before
    run cfg request state delayed = run cfg request state original ∧
    trace cfg request state delayed = trace cfg request state before ++
      List.replicate n (observe request cut (.pending peer)) ++
        trace cfg request cut (.step peer :: after) ∧
    wireChanges (trace cfg request state delayed) = wireChanges (trace cfg request state original) ∧
    (trace cfg request state delayed).filterMap Observation.capture =
      (trace cfg request state original).filterMap Observation.capture := by
  dsimp only
  have traceEq :
      trace cfg request state (before ++ List.replicate n (.pending peer) ++ .step peer :: after) =
        trace cfg request state before ++
          List.replicate n (observe request (run cfg request state before) (.pending peer)) ++
            trace cfg request (run cfg request state before) (.step peer :: after) := by
    rw [List.append_assoc, trace_append, trace_append, trace_pending, run_pending, List.append_assoc]
  refine ⟨?_, traceEq, ?_, ?_⟩
  · simp only [run, List.foldl_append]
    have stalled := run_pending cfg request (run cfg request state before) peer n
    simp only [run] at stalled
    rw [stalled]
  · rw [traceEq, trace_append, trace]
    exact wireChanges_insert _ _ (observe request (run cfg request state before) (.step peer))
      (observe request (run cfg request state before) (.pending peer)) rfl n
  · rw [traceEq, trace_append]
    simp only [List.filterMap_append,
      no_capture_pending (observe request (run cfg request state before) (.pending peer)) n rfl,
      List.append_nil]

/-- While dispatch is pending after an ACK-high sample, the controller
    holds SCL low regardless of the peer's drive. -/
theorem pending_after_ack_is_low (request : RegisterRead.Request) (state : State) (slot : Fin 36) (peer : Pins)
    (phase : state.phase = .fall slot) :
    (observe request state (.pending peer)).wire.bus.scl = false ∧
    (observe request state (.pending peer)).capture = none := by
  simp [observe, phase, pins, resolve, low_dominates]

structure AckWindow where
  earliestSample : Nat
  latestSample : Nat
  lowLimit : Nat
  deriving DecidableEq, Repr

/-- Clock coordinates come from public rising and falling edges. `sample`
    is the controller's capture edge, so it may coincide with the fall. -/
structure AckTiming where
  rise : Nat
  sample : Nat
  fall : Nat
  nextRise : Nat
  deriving DecidableEq, Repr

def AckTiming.Fits (timing : AckTiming) (window : AckWindow) : Prop :=
  timing.rise + window.earliestSample ≤ timing.sample ∧
  timing.sample ≤ timing.rise + window.latestSample ∧
  timing.sample ≤ timing.fall ∧ timing.fall ≤ timing.nextRise ∧
  timing.nextRise ≤ timing.fall + window.lowLimit

instance (timing : AckTiming) (window : AckWindow) : Decidable (timing.Fits window) := by
  unfold AckTiming.Fits
  infer_instance

def AckTiming.holdLow (timing : AckTiming) (cycles : Nat) : AckTiming :=
  { timing with nextRise := timing.nextRise + cycles }

def AckTiming.holdHigh (timing : AckTiming) (cycles : Nat) : AckTiming :=
  ⟨timing.rise, timing.sample + cycles, timing.fall + cycles, timing.nextRise + cycles⟩

theorem after_ack_fetch_preserves (timing : AckTiming) (window : AckWindow) (cycles : Nat)
    (fits : timing.Fits window) (slack : timing.nextRise + cycles ≤ timing.fall + window.lowLimit) :
    (timing.holdLow cycles).Fits window :=
  ⟨fits.1, fits.2.1, fits.2.2.1, Nat.le_trans fits.2.2.2.1 (Nat.le_add_right _ _), slack⟩

/-- Matching payload and untimed transitions cannot repair an ACK capture
    that has moved past the declared physical aperture. -/
theorem late_ack_fetch_rejected (timing : AckTiming) (window : AckWindow) (cycles : Nat)
    (late : timing.rise + window.latestSample < timing.sample + cycles) :
    ¬ (timing.holdHigh cycles).Fits window :=
  fun fits => Nat.not_le_of_lt late fits.2.1

def sclAt (samples : List Observation) (clock : Nat) : Option Bool :=
  (samples[clock]?).map (·.wire.bus.scl)

def sclEdge (samples : List Observation) (before after : Bool) (clock : Nat) : Prop :=
  ∃ previous, clock = previous + 1 ∧ sclAt samples previous = some before ∧ sclAt samples clock = some after

/-- Capture uses the observation immediately preceding the physical edge. -/
def captureAt (samples : List Observation) (slot : Fin 16) (value : Bool) (clock : Nat) : Prop :=
  ∃ previous, clock = previous + 1 ∧
    (samples[previous]?).bind Observation.capture = some (slot, value)

/-- Witnesses are tied to a physical waveform and sampled value. The ACK
    slot is the index in the reference capture vector (8, 9, or 10). -/
structure AckTiming.Observed (timing : AckTiming) (samples : List Observation)
    (slot : Fin 16) (value : Bool) : Prop where
  rise : sclEdge samples false true timing.rise
  sample : captureAt samples slot value timing.sample
  fall : sclEdge samples true false timing.fall
  nextRise : sclEdge samples false true timing.nextRise
  high : ∀ clock, timing.rise ≤ clock → clock < timing.fall → sclAt samples clock = some true
  low : ∀ clock, timing.fall ≤ clock → clock < timing.nextRise → sclAt samples clock = some false

private theorem sample_before (before after : List Observation) (next hold : Observation)
    (cycles clock : Nat) (earlier : clock < before.length) :
    (before ++ List.replicate cycles hold ++ next :: after)[clock]? = (before ++ next :: after)[clock]? := by
  rw [List.append_assoc, List.getElem?_append_left earlier, List.getElem?_append_left earlier]

private theorem sample_shifted (before after : List Observation) (next hold : Observation)
    (cycles clock : Nat) (later : before.length ≤ clock) :
    (before ++ List.replicate cycles hold ++ next :: after)[clock + cycles]? =
      (before ++ next :: after)[clock]? := by
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right later]
  congr 1
  simp only [List.length_append, List.length_replicate]
  omega

private theorem scl_before_or_at (before after : List Observation) (next hold : Observation)
    (same : hold.wire = next.wire) (cycles clock : Nat) (earlier : clock ≤ before.length) :
    sclAt (before ++ List.replicate cycles hold ++ next :: after) clock =
      sclAt (before ++ next :: after) clock := by
  rcases Nat.lt_or_eq_of_le earlier with strictly | atCut
  · simp only [sclAt, sample_before before after next hold cycles clock strictly]
  · subst clock
    rw [sclAt, sclAt, List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    cases cycles <;> simp [List.replicate_succ, same]

private theorem edge_before_or_at (before after : List Observation) (next hold : Observation)
    (same : hold.wire = next.wire) (cycles clock : Nat) (earlier : clock ≤ before.length)
    (edge : sclEdge (before ++ next :: after) low high clock) :
    sclEdge (before ++ List.replicate cycles hold ++ next :: after) low high clock := by
  obtain ⟨previous, atClock, fromLevel, toLevel⟩ := edge
  refine ⟨previous, atClock, ?_, ?_⟩
  · rw [scl_before_or_at before after next hold same cycles previous (by omega)]
    exact fromLevel
  · rw [scl_before_or_at before after next hold same cycles clock earlier]
    exact toLevel

private theorem edge_shifted (before after : List Observation) (next hold : Observation) (cycles clock : Nat)
    (later : before.length < clock) (edge : sclEdge (before ++ next :: after) low high clock) :
    sclEdge (before ++ List.replicate cycles hold ++ next :: after) low high (clock + cycles) := by
  obtain ⟨previous, atClock, fromLevel, toLevel⟩ := edge
  refine ⟨previous + cycles, by omega, ?_, ?_⟩
  · simp only [sclAt, sample_shifted before after next hold cycles previous (by omega)]
    exact fromLevel
  · simp only [sclAt, sample_shifted before after next hold cycles clock (Nat.le_of_lt later)]
    exact toLevel

private theorem capture_before_or_at (before after : List Observation) (next hold : Observation)
    (cycles clock : Nat) (earlier : clock ≤ before.length)
    (sample : captureAt (before ++ next :: after) slot value clock) :
    captureAt (before ++ List.replicate cycles hold ++ next :: after) slot value clock := by
  obtain ⟨previous, atClock, captured⟩ := sample
  exact ⟨previous, atClock, by rw [sample_before before after next hold cycles previous (by omega)]; exact captured⟩

private theorem capture_shifted (before after : List Observation) (next hold : Observation) (cycles clock : Nat)
    (later : before.length < clock) (sample : captureAt (before ++ next :: after) slot value clock) :
    captureAt (before ++ List.replicate cycles hold ++ next :: after) slot value (clock + cycles) := by
  obtain ⟨previous, atClock, captured⟩ := sample
  exact ⟨previous + cycles, by omega,
    by rw [sample_shifted before after next hold cycles previous (by omega)]; exact captured⟩

private theorem scl_interval_insert (before after : List Observation) (next hold : Observation)
    (same : hold.wire = next.wire) (cycles start stop : Nat)
    (cut : start ≤ before.length ∧ before.length < stop)
    (stable : ∀ clock, start ≤ clock → clock < stop → sclAt (before ++ next :: after) clock = some level)
    (clock : Nat) (started : start ≤ clock) (beforeStop : clock < stop + cycles) :
    sclAt (before ++ List.replicate cycles hold ++ next :: after) clock = some level := by
  by_cases beforeCut : clock ≤ before.length
  · rw [scl_before_or_at before after next hold same cycles clock beforeCut]
    exact stable clock started (Nat.lt_of_le_of_lt beforeCut cut.2)
  by_cases afterCut : before.length + cycles ≤ clock
  · rw [← Nat.sub_add_cancel (show cycles ≤ clock by omega), sclAt,
      sample_shifted before after next hold cycles (clock - cycles) (by omega)]
    exact stable (clock - cycles) (by omega) (by omega)
  have atCut := stable before.length cut.1 cut.2
  simp only [sclAt, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
    Option.map_some] at atCut
  unfold sclAt
  rw [List.append_assoc, List.getElem?_append_right (by omega : before.length ≤ clock),
    List.getElem?_append_left (by simp only [List.length_replicate]; omega),
    List.getElem?_replicate_of_lt (by omega)]
  simpa only [Option.map_some, same] using atCut

/-- A fetch hold at or after the ACK fall preserves the earlier aperture
    and moves the following rise by the actual number of added clocks. -/
theorem observe_after_ack_fetch (timing : AckTiming) (window : AckWindow)
    (before after : List Observation) (next hold : Observation) (cycles : Nat)
    (same : hold.wire = next.wire) (observed : timing.Observed (before ++ next :: after) slot value)
    (fits : timing.Fits window) (cut : timing.fall ≤ before.length ∧ before.length < timing.nextRise)
    (slack : timing.nextRise + cycles ≤ timing.fall + window.lowLimit) :
    (timing.holdLow cycles).Observed (before ++ List.replicate cycles hold ++ next :: after) slot value ∧
    (timing.holdLow cycles).Fits window := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, after_ack_fetch_preserves timing window cycles fits slack⟩
  · exact edge_before_or_at before after next hold same cycles timing.rise (by unfold AckTiming.Fits at fits; omega) observed.rise
  · exact capture_before_or_at before after next hold cycles timing.sample (Nat.le_trans fits.2.2.1 cut.1) observed.sample
  · exact edge_before_or_at before after next hold same cycles timing.fall cut.1 observed.fall
  · exact edge_shifted before after next hold cycles timing.nextRise cut.2 observed.nextRise
  · intro clock started beforeFall
    rw [scl_before_or_at before after next hold same cycles clock (Nat.le_trans (Nat.le_of_lt beforeFall) cut.1)]
    exact observed.high clock started beforeFall
  · exact scl_interval_insert before after next hold same cycles timing.fall timing.nextRise cut observed.low

/-- A hold on ACK-high before sampling moves the observed capture past a
    tight deadline, even when the unchanged ACK value is eventually read. -/
theorem observe_late_ack_fetch (timing : AckTiming) (window : AckWindow)
    (before after : List Observation) (next hold : Observation) (cycles : Nat)
    (same : hold.wire = next.wire) (observed : timing.Observed (before ++ next :: after) slot value)
    (fits : timing.Fits window) (cut : timing.rise ≤ before.length ∧ before.length < timing.sample)
    (late : timing.rise + window.latestSample < timing.sample + cycles) :
    (timing.holdHigh cycles).Observed (before ++ List.replicate cycles hold ++ next :: after) slot value ∧
    ¬ (timing.holdHigh cycles).Fits window := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, late_ack_fetch_rejected timing window cycles late⟩
  · exact edge_before_or_at before after next hold same cycles timing.rise cut.1 observed.rise
  · exact capture_shifted before after next hold cycles timing.sample cut.2 observed.sample
  · exact edge_shifted before after next hold cycles timing.fall (Nat.lt_of_lt_of_le cut.2 fits.2.2.1) observed.fall
  · exact edge_shifted before after next hold cycles timing.nextRise
      (Nat.lt_of_lt_of_le cut.2 (Nat.le_trans fits.2.2.1 fits.2.2.2.1)) observed.nextRise
  · exact scl_interval_insert before after next hold same cycles timing.rise timing.fall
      ⟨cut.1, Nat.lt_of_lt_of_le cut.2 fits.2.2.1⟩ observed.high
  · intro clock afterFall beforeRise
    change timing.fall + cycles ≤ clock at afterFall
    change clock < timing.nextRise + cycles at beforeRise
    have shifted : clock = (clock - cycles) + cycles := by omega
    have afterCut : before.length ≤ clock - cycles := by have := fits.2.2.1; omega
    rw [shifted, sclAt, sample_shifted before after next hold cycles (clock - cycles) afterCut]
    exact observed.low (clock - cycles) (by omega) (by omega)

end Pinwheel.I2C.RegisterReadFetch
