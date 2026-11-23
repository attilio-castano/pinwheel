import Pinwheel.Hardware.Timed.Events

/-! Sampled synchronous 8N1 UART, independent of MMIO buffering.

A TX offer is accepted only while idle. Acceptance immediately installs the
start bit; the ten symbols each occupy D complete periods. The closing edge
emits completion, without accepting a replacement. A still-held offer can be
accepted on the next idle edge: its owner must remove it when completion is
consumed. MMIO integration must prove this ownership and use an accepted-write
bypass to start on the same edge as the MMIO write.

RX detects a sampled low, validates it D/2 edges later, samples eight data bits
D edges apart and checks stop after another D edges. A high start midpoint is
an ignored glitch. A low stop emits framing error and waits for sampled high
before rearming. RX arrival is independent of a downstream slot's acceptance.

Inputs are already synchronous digital samples. Analog synchronization,
metastability, baud tolerance and physical qualification are outside this model.
Reset aborts control and suppresses completion; historical line bits are not
rolled back.
-/
namespace Pinwheel.Hardware.Uart

abbrev Byte := BitVec 8

structure Timing where
  divisor : Nat
  minimum : 4 ≤ divisor
  even : divisor % 2 = 0
  deriving DecidableEq, Repr

def Timing.half (d : Timing) : Nat := d.divisor / 2
def Timing.frame (d : Timing) : Nat := 10*d.divisor
def Timing.stopSample (d : Timing) : Nat := d.half + 9*d.divisor
def Timing.dataSample (d : Timing) (k : Fin 8) : Nat := d.half + (k.val+1)*d.divisor

theorem Timing.positive (d : Timing) : 0 < d.divisor := by have := d.minimum; omega
theorem Timing.half_positive (d : Timing) : 0 < d.half := by have := d.minimum; unfold Timing.half; omega
theorem Timing.half_twice (d : Timing) : d.half*2 = d.divisor := by
  have := d.even; unfold Timing.half; omega

def pack (bits : Fin 8 → Bool) : Byte :=
  (BitVec.ofBool (bits 7)) ++ ((BitVec.ofBool (bits 6)) ++
  ((BitVec.ofBool (bits 5)) ++ ((BitVec.ofBool (bits 4)) ++
  ((BitVec.ofBool (bits 3)) ++ ((BitVec.ofBool (bits 2)) ++
  ((BitVec.ofBool (bits 1)) ++ (BitVec.ofBool (bits 0))))))))

@[simp] theorem pack_get (bits : Fin 8 → Bool) (k : Fin 8) :
    (pack bits).getLsbD k.val = bits k := by
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ => simp only [pack, BitVec.getLsbD_append]; simp
  | ⟨k+8, h⟩ => omega

theorem pack_byte (byte : Byte) : pack (fun k => byte.getLsbD k.val) = byte := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  exact pack_get _ ⟨k, hk⟩

inductive TxState where
  | idle
  | active (byte : Byte) (elapsed : Nat)
  deriving DecidableEq, Repr

inductive RxState where
  | idle
  | receiving (elapsed : Nat) (data : Byte)
  | waitHigh
  deriving DecidableEq, Repr

structure State where
  tx : TxState
  rx : RxState
  deriving DecidableEq, Repr

def initial : State := ⟨.idle, .idle⟩

structure Input where
  reset : Bool := false
  offer : Option Byte := none
  rx : Bool := true
  deriving DecidableEq, Repr

structure Output where
  line : Bool
  ready : Bool
  complete : Bool
  arrival : Option Byte
  framingError : Bool
  deriving DecidableEq, Repr

def frameBit (byte : Byte) (symbol : Nat) : Bool :=
  if symbol = 0 then false else if symbol < 9 then byte.getLsbD (symbol-1) else true

def txReady (i : Input) (s : TxState) : Bool := !i.reset && s matches .idle

def accepted (i : Input) (s : TxState) : Option Byte := if txReady i s then i.offer else none

def txPending : TxState → Option Byte
  | .idle => none | .active byte _ => some byte

def completed (d : Timing) (i : Input) (s : TxState) : Option Byte :=
  if i.reset then none else match s with
  | .idle => none
  | .active byte elapsed => if d.frame ≤ elapsed+1 then some byte else none

def txLine (d : Timing) (i : Input) (s : TxState) : Bool :=
  if i.reset then true else match s with
  | .idle => true
  | .active byte elapsed => frameBit byte (elapsed / d.divisor)

def txStep (d : Timing) (i : Input) (s : TxState) : TxState :=
  if i.reset then .idle else match s with
  | .idle => match i.offer with | none => .idle | some byte => .active byte 0
  | .active byte elapsed => if d.frame ≤ elapsed+1 then .idle else .active byte (elapsed+1)

def rxUpdate (d : Timing) (time : Nat) (sample : Bool) (byte : Byte) : Byte :=
  pack (fun k => if d.dataSample k = time then sample else byte.getLsbD k.val)

def rxStep (d : Timing) (i : Input) (s : RxState) : RxState :=
  if i.reset then .idle else match s with
  | .idle => if i.rx then .idle else .receiving 0 0
  | .waitHigh => if i.rx then .idle else .waitHigh
  | .receiving elapsed byte =>
    if elapsed+1 = d.half && i.rx then .idle
    else if d.stopSample ≤ elapsed+1 then if i.rx then .idle else .waitHigh
    else .receiving (elapsed+1) (rxUpdate d (elapsed+1) i.rx byte)

def arrival (d : Timing) (i : Input) (s : RxState) : Option Byte :=
  if i.reset then none else match s with
  | .receiving elapsed byte => if d.stopSample ≤ elapsed+1 && i.rx then some byte else none
  | _ => none

def framingError (d : Timing) (i : Input) (s : RxState) : Bool :=
  !i.reset && match s with
  | .receiving elapsed _ => decide (d.stopSample ≤ elapsed+1) && !i.rx
  | _ => false

def step (d : Timing) (i : Input) (s : State) : State := ⟨txStep d i s.tx, rxStep d i s.rx⟩
def observe (d : Timing) (i : Input) (s : State) : Output :=
  ⟨txLine d i s.tx, txReady i s.tx, (completed d i s.tx).isSome, arrival d i s.rx, framingError d i s.rx⟩
def component (d : Timing) : Timed.Component Input State Output := ⟨step d, observe d⟩

def Valid (d : Timing) (s : State) : Prop :=
  (match s.tx with | .idle => True | .active _ elapsed => elapsed < d.frame) ∧
  (match s.rx with | .receiving elapsed _ => elapsed < d.stopSample | _ => True)


theorem Timing.sample_positive (d : Timing) (k : Fin 8) : 0 < d.dataSample k := by
  have := d.half_positive
  simp only [Timing.dataSample]
  omega

theorem Timing.sample_before_stop (d : Timing) (k : Fin 8) : d.dataSample k < d.stopSample := by
  have h := Nat.mul_lt_mul_of_pos_right (show k.val+1 < 9 by omega) d.positive
  simp only [Timing.dataSample, Timing.stopSample]
  omega

theorem Timing.stop_positive (d : Timing) : 0 < d.stopSample := by
  have := d.half_positive
  simp only [Timing.stopSample]
  omega

def captured (d : Timing) (byte : Byte) (time : Nat) : Byte :=
  pack (fun k => if d.dataSample k ≤ time then byte.getLsbD k.val else false)

@[simp] theorem captured_get (d : Timing) (byte : Byte) (time : Nat) (k : Fin 8) :
    (captured d byte time).getLsbD k.val = if d.dataSample k ≤ time then byte.getLsbD k.val else false :=
  pack_get _ k

theorem captured_zero (d : Timing) (byte : Byte) : captured d byte 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hp := d.sample_positive ⟨k, hk⟩
  rw [captured_get d byte 0 ⟨k, hk⟩]
  simp [show ¬d.dataSample ⟨k, hk⟩ ≤ 0 by omega]

theorem captured_complete (d : Timing) (byte : Byte) : captured d byte (d.stopSample-1) = byte := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hp := d.sample_before_stop ⟨k, hk⟩
  exact (captured_get d byte _ ⟨k, hk⟩).trans (if_pos (by omega))

theorem captured_update (d : Timing) (byte : Byte) (time : Nat) (sample : Bool)
    (hline : ∀ k, d.dataSample k = time+1 → sample = byte.getLsbD k.val) :
    rxUpdate d (time+1) sample (captured d byte time) = captured d byte (time+1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  change (pack _).getLsbD (⟨k, hk⟩ : Fin 8).val = _
  rw [pack_get, captured_get d byte (time+1) ⟨k, hk⟩, captured_get d byte time ⟨k, hk⟩]
  by_cases hs : d.dataSample ⟨k, hk⟩ = time+1
  · simp [hs, hline ⟨k, hk⟩ hs]
  · have he : d.dataSample ⟨k, hk⟩ ≤ time+1 ↔ d.dataSample ⟨k, hk⟩ ≤ time := by omega
    simp [hs, he]

/-- These are line-sample assumptions, not an assumption about a decoded byte.
Samples away from detection/start/data/stop instants may vary arbitrarily. -/
structure RxSchedule (d : Timing) (byte : Byte) (line : Nat → Bool) : Prop where
  detected : line 0 = false
  start : line d.half = false
  data : ∀ k : Fin 8, line (d.dataSample k) = byte.getLsbD k.val
  stop : line d.stopSample = true

def sampledInput (line : Nat → Bool) (time : Nat) : Input := ⟨false, none, line time⟩

def rxRun (d : Timing) (line : Nat → Bool) : Nat → RxState
  | 0 => .idle
  | n+1 => rxStep d (sampledInput line n) (rxRun d line n)

theorem rx_prefix (d : Timing) (byte : Byte) (line : Nat → Bool) (schedule : RxSchedule d byte line)
    (time : Nat) (ht : time < d.stopSample) :
    rxRun d line (time+1) = .receiving time (captured d byte time) := by
  induction time with
  | zero => simp [rxRun, rxStep, sampledInput, schedule.detected, captured_zero]
  | succ time ih =>
    rw [rxRun, ih (by omega)]
    have hs : ¬(time+1 = d.half ∧ line (time+1) = true) := by
      intro ⟨same, high⟩
      rw [same, schedule.start] at high
      contradiction
    simp only [rxStep, sampledInput, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
    rw [if_neg hs, if_neg (by omega : ¬d.stopSample ≤ time+1)]
    rw [captured_update d byte time (line (time+1)) (by intro k h; rw [← h]; exact schedule.data k)]

theorem rx_stop_state (d : Timing) (byte : Byte) (line : Nat → Bool) (schedule : RxSchedule d byte line) :
    rxRun d line d.stopSample = .receiving (d.stopSample-1) byte := by
  have hp := d.stop_positive
  have h := rx_prefix d byte line schedule (d.stopSample-1) (by omega)
  simpa [captured_complete, show d.stopSample-1+1 = d.stopSample by omega] using h

theorem rx_decode (d : Timing) (byte : Byte) (line : Nat → Bool) (schedule : RxSchedule d byte line) :
    arrival d (sampledInput line d.stopSample) (rxRun d line d.stopSample) = some byte := by
  rw [rx_stop_state d byte line schedule]
  have hp := d.stop_positive
  simp [arrival, sampledInput, schedule.stop, show d.stopSample ≤ d.stopSample-1+1 by omega]

theorem rx_no_early_arrival (d : Timing) (byte : Byte) (line : Nat → Bool) (schedule : RxSchedule d byte line)
    (time : Nat) (ht : time < d.stopSample) :
    arrival d (sampledInput line time) (rxRun d line time) = none := by
  cases time with
  | zero => rfl
  | succ t =>
    rw [rx_prefix d byte line schedule t (by omega)]
    simp [arrival, sampledInput, show ¬d.stopSample ≤ t+1 by omega]


theorem Timing.frame_positive (d : Timing) : 0 < d.frame := by
  have := d.positive
  simp only [Timing.frame]
  omega

theorem Timing.half_lt (d : Timing) : d.half < d.divisor := by
  have := d.minimum
  unfold Timing.half
  omega

theorem initial_valid (d : Timing) : Valid d initial := ⟨trivial, trivial⟩

theorem txStep_bounded (d : Timing) (i : Input) (s : TxState) :
    (match txStep d i s with | .idle => True | .active _ elapsed => elapsed < d.frame) := by
  cases hr : i.reset
  · cases s with
    | idle => cases ho : i.offer <;> simp [txStep, hr, ho, d.frame_positive]
    | active byte elapsed =>
      by_cases h : d.frame ≤ elapsed+1 <;> simp [txStep, hr, h]
      omega
  · simp [txStep, hr]

theorem rxStep_bounded (d : Timing) (i : Input) (s : RxState) :
    (match rxStep d i s with | .receiving elapsed _ => elapsed < d.stopSample | _ => True) := by
  cases hr : i.reset
  · cases s with
    | idle => cases hx : i.rx <;> simp [rxStep, hr, hx, d.stop_positive]
    | waitHigh => cases hx : i.rx <;> simp [rxStep, hr, hx]
    | receiving elapsed byte =>
      by_cases h : elapsed+1 = d.half ∧ i.rx = true
      · simp [rxStep, hr, h.1, h.2]
      · by_cases ht : d.stopSample ≤ elapsed+1
        · cases hx : i.rx <;> simp [rxStep, hr, hx, ht]
        · simp [rxStep, hr, Bool.and_eq_true, h, ht]
          omega
  · simp [rxStep, hr]

theorem step_valid (d : Timing) (i : Input) (s : State) : Valid d (step d i s) :=
  ⟨txStep_bounded d i s.tx, rxStep_bounded d i s.rx⟩

/-- Acceptance uses pre-edge idle state; the accepted byte immediately drives
start-low after the edge. Offers during a frame cannot replace its byte. -/
theorem accept_start (d : Timing) (i : Input) (s : TxState) (byte : Byte)
    (h : accepted i s = some byte) :
    txStep d i s = .active byte 0 ∧ txLine d i (txStep d i s) = false := by
  cases s <;> cases hr : i.reset <;> simp [accepted, txReady, hr] at h
  cases ho : i.offer <;> simp [ho] at h
  subst byte
  simp [txStep, hr, ho, txLine, frameBit]

theorem busy_not_ready (i : Input) (byte : Byte) (elapsed : Nat) :
    txReady i (.active byte elapsed) = false := by simp [txReady]

theorem busy_not_accepted (i : Input) (byte : Byte) (elapsed : Nat) :
    accepted i (.active byte elapsed) = none := by simp [accepted, txReady]

def txRun (d : Timing) (byte : Byte) (offers : Nat → Option Byte) : Nat → TxState
  | 0 => .active byte 0
  | time+1 => txStep d ⟨false, offers time, true⟩ (txRun d byte offers time)

theorem tx_prefix (d : Timing) (byte : Byte) (offers : Nat → Option Byte)
    (time : Nat) (ht : time < d.frame) : txRun d byte offers time = .active byte time := by
  induction time with
  | zero => rfl
  | succ time ih => simp [txRun, ih (by omega), txStep, show ¬d.frame ≤ time+1 by omega]

theorem tx_duration (d : Timing) (byte : Byte) (offers : Nat → Option Byte) :
    txRun d byte offers d.frame = .idle := by
  have hf := d.frame_positive
  have he : d.frame = (d.frame-1)+1 := by omega
  rw [he, txRun, tx_prefix d byte offers (d.frame-1) (by omega)]
  simp [txStep, ← he]

/-- The output is constant throughout each of the ten D-period symbols. -/
theorem tx_symbol (d : Timing) (byte : Byte) (offers : Nat → Option Byte)
    (symbol tick : Nat) (hs : symbol < 10) (ht : tick < d.divisor) :
    txLine d ⟨false, none, true⟩ (txRun d byte offers (symbol*d.divisor+tick)) = frameBit byte symbol := by
  have hm := Nat.mul_le_mul_right d.divisor (show symbol+1 ≤ 10 by omega)
  have htime : symbol*d.divisor+tick < d.frame := by simp only [Timing.frame]; rw [Nat.add_mul] at hm; omega
  rw [tx_prefix d byte offers _ htime]
  simp only [txLine, Bool.false_eq_true, ↓reduceIte]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ d.positive, Nat.div_eq_of_lt ht, Nat.zero_add]

theorem tx_data_order (d : Timing) (byte : Byte) (offers : Nat → Option Byte)
    (bit : Fin 8) (tick : Nat) (ht : tick < d.divisor) :
    txLine d ⟨false, none, true⟩ (txRun d byte offers ((bit.val+1)*d.divisor+tick)) = byte.getLsbD bit.val := by
  rw [tx_symbol d byte offers _ tick (by omega) ht]
  simp [frameBit, show bit.val+1 < 9 by omega]

theorem tx_completion_exact (d : Timing) (byte : Byte) (offers : Nat → Option Byte)
    (time : Nat) (ht : time < d.frame) :
    completed d ⟨false, offers time, true⟩ (txRun d byte offers time) =
      if time+1 = d.frame then some byte else none := by
  rw [tx_prefix d byte offers time ht]
  simp [completed, show d.frame ≤ time+1 ↔ time+1 = d.frame by omega]

theorem completion_idle (d : Timing) (i : Input) (s : TxState) (byte : Byte)
    (h : completed d i s = some byte) : txStep d i s = .idle := by
  cases hr : i.reset <;> cases s <;> simp [completed, hr] at h
  simp [txStep, hr, h.1]

theorem no_double_completion (d : Timing) (i next : Input) (s : TxState) (byte : Byte)
    (h : completed d i s = some byte) : completed d next (txStep d i s) = none := by
  rw [completion_idle d i s byte h]
  simp [completed]

theorem idle_without_offer (d : Timing) (i : Input) (h : i.offer = none) : txStep d i .idle = .idle := by
  simp [txStep, h]

def txHistory (d : Timing) (s : TxState) : List Input → TxState
  | [] => s
  | i :: rest => txHistory d (txStep d i s) rest

def completionHistory (d : Timing) (s : TxState) : List Input → List Byte
  | [] => []
  | i :: rest => (completed d i s).toList ++ completionHistory d (txStep d i s) rest

/-- Removing the owned offer on completion prevents any restart or duplicate
completion. A later new accepted offer is a new transaction, not a repeat. -/
theorem quiet_without_offer (d : Timing) (traffic : List Input)
    (h : ∀ i ∈ traffic, i.offer = none) :
    txHistory d .idle traffic = .idle ∧ completionHistory d .idle traffic = [] := by
  induction traffic with
  | nil => exact ⟨rfl, rfl⟩
  | cons i rest ih =>
    have hi := h i (by simp)
    have tail := ih (by intro j hj; exact h j (by simp [hj]))
    simpa [txHistory, completionHistory, idle_without_offer d i hi, completed] using tail

theorem completion_then_quiet (d : Timing) (i : Input) (s : TxState) (byte : Byte)
    (hc : completed d i s = some byte) (traffic : List Input)
    (ho : ∀ j ∈ traffic, j.offer = none) :
    completionHistory d (txStep d i s) traffic = [] := by
  rw [completion_idle d i s byte hc]
  exact (quiet_without_offer d traffic ho).2

theorem reset_state (d : Timing) (s : State) (offer : Option Byte) (rx : Bool) :
    step d ⟨true, offer, rx⟩ s = initial := rfl

theorem reset_output (d : Timing) (s : State) (offer : Option Byte) (rx : Bool) :
    observe d ⟨true, offer, rx⟩ s = ⟨true, false, false, none, false⟩ := by
  simp [observe, txLine, txReady, completed, arrival, framingError]

theorem reset_no_accept (s : TxState) (offer : Option Byte) (rx : Bool) :
    accepted ⟨true, offer, rx⟩ s = none := by simp [accepted, txReady]


/-- The ideal sampled digital waveform, with a whole D-period start symbol,
eight LSB-first data symbols and an indefinitely high stop/idle tail. -/
def periodicLine (d : Timing) (byte : Byte) (time : Nat) : Bool := frameBit byte (time/d.divisor)

theorem midpoint_quotient (d : Timing) (symbol : Nat) :
    (d.half+symbol*d.divisor)/d.divisor = symbol := by
  rw [Nat.add_mul_div_right _ _ d.positive, Nat.div_eq_of_lt d.half_lt, Nat.zero_add]

theorem periodic_schedule (d : Timing) (byte : Byte) : RxSchedule d byte (periodicLine d byte) where
  detected := by simp [periodicLine, frameBit]
  start := by simp [periodicLine, Nat.div_eq_of_lt d.half_lt, frameBit]
  data := by
    intro k
    simp [periodicLine, Timing.dataSample, midpoint_quotient, frameBit, show k.val+1 < 9 by omega]
  stop := by simp [periodicLine, Timing.stopSample, midpoint_quotient, frameBit]

theorem periodic_decode (d : Timing) (byte : Byte) :
    arrival d (sampledInput (periodicLine d byte) d.stopSample)
      (rxRun d (periodicLine d byte) d.stopSample) = some byte :=
  rx_decode d byte _ (periodic_schedule d byte)

theorem rx_finish (d : Timing) (byte : Byte) (line : Nat → Bool) (schedule : RxSchedule d byte line) :
    rxRun d line (d.stopSample+1) = .idle := by
  rw [rxRun, rx_stop_state d byte line schedule]
  have hp := d.stop_positive
  have hd := d.positive
  have hne : d.stopSample ≠ d.half := by unfold Timing.stopSample; omega
  simp [rxStep, sampledInput, schedule.stop, show d.stopSample-1+1 = d.stopSample by omega, hne]

theorem rx_false_start (d : Timing) (byte : Byte) :
    rxStep d ⟨false, none, true⟩ (.receiving (d.half-1) byte) = .idle ∧
    arrival d ⟨false, none, true⟩ (.receiving (d.half-1) byte) = none ∧
    framingError d ⟨false, none, true⟩ (.receiving (d.half-1) byte) = false := by
  have hp := d.half_positive
  have hd := d.positive
  have hs : d.half < d.stopSample := by unfold Timing.stopSample; omega
  simp [rxStep, arrival, framingError, show d.half-1+1 = d.half by omega, show ¬d.stopSample ≤ d.half by omega]

theorem rx_bad_stop (d : Timing) (byte : Byte) :
    rxStep d ⟨false, none, false⟩ (.receiving (d.stopSample-1) byte) = .waitHigh ∧
    arrival d ⟨false, none, false⟩ (.receiving (d.stopSample-1) byte) = none ∧
    framingError d ⟨false, none, false⟩ (.receiving (d.stopSample-1) byte) = true := by
  have hp := d.stop_positive
  simp [rxStep, arrival, framingError, show d.stopSample-1+1 = d.stopSample by omega]

theorem rx_break_quiet (d : Timing) :
    rxStep d ⟨false, none, false⟩ .waitHigh = .waitHigh ∧
    arrival d ⟨false, none, false⟩ .waitHigh = none ∧
    framingError d ⟨false, none, false⟩ .waitHigh = false := by
  simp [rxStep, arrival, framingError]

theorem rx_rearm (d : Timing) : rxStep d ⟨false, none, true⟩ .waitHigh = .idle := rfl

def canceled (i : Input) (s : TxState) : Option Byte := if i.reset then txPending s else none

/-- A frame is accepted, pending, completed or canceled exactly once. Reset
removes its pending control; it cannot remove already observed line samples. -/
theorem tx_balance (d : Timing) (i : Input) (s : TxState) :
    (txPending s).toList ++ (accepted i s).toList =
      (completed d i s).toList ++ (canceled i s).toList ++ (txPending (txStep d i s)).toList := by
  cases hr : i.reset <;> cases s with
  | idle => cases ho : i.offer <;> simp [txPending, accepted, txReady, completed, canceled, txStep, hr, ho]
  | active byte elapsed =>
    by_cases hc : d.frame ≤ elapsed+1 <;>
      simp [txPending, accepted, txReady, completed, canceled, txStep, hr, hc]

def acceptedHistory (d : Timing) (s : TxState) : List Input → List Byte
  | [] => []
  | i :: rest => (accepted i s).toList ++ acceptedHistory d (txStep d i s) rest

def retiredHistory (d : Timing) (s : TxState) : List Input → List Byte
  | [] => []
  | i :: rest => (completed d i s).toList ++ (canceled i s).toList ++ retiredHistory d (txStep d i s) rest

theorem tx_history_balance (d : Timing) (s : TxState) (traffic : List Input) :
    (txPending s).toList ++ acceptedHistory d s traffic =
      retiredHistory d s traffic ++ (txPending (txHistory d s traffic)).toList := by
  induction traffic generalizing s with
  | nil => simp [acceptedHistory, retiredHistory, txHistory]
  | cons i rest ih =>
    simp only [acceptedHistory, retiredHistory, txHistory]
    rw [← List.append_assoc, tx_balance]
    simp only [List.append_assoc]
    rw [ih]


/-- A runtime parameter check, also usable by elaboration/CLI frontends. -/
def Timing.check (divisor : Nat) : Option Timing :=
  if h : 4 ≤ divisor ∧ divisor % 2 = 0 then some ⟨divisor, h.1, h.2⟩ else none

theorem Timing.check_admitted (divisor : Nat) :
    (Timing.check divisor).isSome = decide (4 ≤ divisor ∧ divisor % 2 = 0) := by
  unfold Timing.check
  split <;> simp_all

theorem rx_no_double_arrival (d : Timing) (i next : Input) (s : RxState) (byte : Byte)
    (h : arrival d i s = some byte) : arrival d next (rxStep d i s) = none := by
  cases hr : i.reset <;> cases s <;> simp [arrival, hr] at h
  rcases h with ⟨⟨ht, hx⟩, _⟩
  simp [rxStep, hr, hx, ht]
  simp [arrival]

end Pinwheel.Hardware.Uart
