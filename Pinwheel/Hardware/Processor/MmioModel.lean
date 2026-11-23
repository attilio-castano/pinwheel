import Pinwheel.Hardware.Timed.Events

/-! Atomic word MMIO for the first processor EEI. AddressMap has already
checked region, direction-independent word width, alignment and bounds.
Serial completion/arrival/error inputs are frontend events, not a claim about
UART wire decoding. There is no response backpressure or pending CPU request.
-/
namespace Pinwheel.Hardware.Processor.MmioModel

abbrev Word := BitVec 32
abbrev Byte := BitVec 8

inductive Device where
  | gpio | timer | uart
  deriving DecidableEq, Repr

structure Request where
  device : Device
  word : BitVec 6
  write : Bool
  data : Word
  deriving DecidableEq, Repr

inductive Fault where
  | registerHole | direction | txBusy | rxEmpty
  deriving DecidableEq, Repr

inductive Response where
  | read (value : Word)
  | stored
  | fault (reason : Fault)
  deriving DecidableEq, Repr

structure State where
  gpioOut : Word
  timer : Word
  tx : Option Byte
  rx : Option Byte
  overrun : Bool
  framing : Bool
  deriving DecidableEq, Repr

def initial : State := ⟨0, 0, none, none, false, false⟩

structure Input where
  reset : Bool
  operation : Option Request
  gpioInput : Word
  txComplete : Bool
  rxArrival : Option Byte
  framingError : Bool
  deriving DecidableEq, Repr

def status (s : State) : Word :=
  BitVec.ofNat 32 ((if s.tx.isNone then 1 else 0) + (if s.rx.isSome then 2 else 0) +
    (if s.overrun then 4 else 0) + (if s.framing then 8 else 0))

/-- Only CPU-requested effects; a fault returns the entire supplied state. -/
def access (gpioInput : Word) (r : Request) (s : State) : Response × State :=
  match r.device with
  | .gpio =>
    if r.word = 0 then
      if r.write then (.fault .direction, s) else (.read gpioInput, s)
    else if r.word = 1 then
      if r.write then (.stored, { s with gpioOut := r.data }) else (.read s.gpioOut, s)
    else (.fault .registerHole, s)
  | .timer =>
    if r.word = 0 then
      if r.write then (.fault .direction, s) else (.read s.timer, s)
    else (.fault .registerHole, s)
  | .uart =>
    if r.word = 0 then
      if r.write then (.fault .direction, s) else (.read (status s), s)
    else if r.word = 1 then
      if r.write then
        if s.tx.isNone then (.stored, { s with tx := some (r.data.extractLsb' 0 8) })
        else (.fault .txBusy, s)
      else (.fault .direction, s)
    else if r.word = 2 then
      if r.write then (.fault .direction, s)
      else match s.rx with
        | none => (.fault .rxEmpty, s)
        | some byte => (.read (byte.setWidth 32), { s with rx := none })
    else if r.word = 3 then
      if r.write then (.stored, { s with
        overrun := s.overrun && !r.data.getLsbD 2
        framing := s.framing && !r.data.getLsbD 3 })
      else (.fault .direction, s)
    else (.fault .registerHole, s)

def cpuState (i : Input) (s : State) : State :=
  match i.operation with
  | none => s
  | some r => (access i.gpioInput r s).2

def observe (i : Input) (s : State) : Option Response :=
  if i.reset then none else i.operation.map (fun r => (access i.gpioInput r s).1)

/-- Only a frame present before the edge may complete. A spurious completion
input while idle is ignored, including an edge that starts a new frame. -/
def completedTx (i : Input) (s : State) : Option Byte :=
  if i.txComplete then s.tx else none

def receive (arrival : Option Byte) (s : State) : State :=
  match arrival with
  | none => s
  | some byte => if s.rx.isNone then { s with rx := some byte }
      else { s with overrun := true }

def autonomous (i : Input) (before current : State) : State :=
  let serial := receive i.rxArrival { current with
    timer := before.timer + 1
    tx := if (completedTx i before).isSome then none else current.tx }
  { serial with framing := serial.framing || i.framingError }

def step (i : Input) (s : State) : State :=
  if i.reset then initial else autonomous i s (cpuState i s)

def component : Timed.Component Input State (Option Response) := ⟨step, observe⟩

inductive Event where
  | cpu (request : Request) (sampledGPIO : Word) (response : Response)
  | tick
  | txComplete (byte : Byte)
  | receive (byte : Byte) (accepted : Bool)
  | framingError
  | reset
  deriving DecidableEq, Repr

def autonomousEvents (i : Input) (before current : State) : List Event :=
  [.tick] ++ (completedTx i before).toList.map Event.txComplete ++
    i.rxArrival.toList.map (fun byte => .receive byte current.rx.isNone) ++
    (if i.framingError then [.framingError] else [])

/-- Fixed extraction retains the actual request, sampled GPIO and response;
faults are not discarded. RX arrival records acceptance versus overflow drop. -/
def events (i : Input) (s : State) : List Event :=
  if i.reset then [.reset] else
    i.operation.toList.map (fun r => .cpu r i.gpioInput (access i.gpioInput r s).1) ++
      autonomousEvents i s (cpuState i s)

/-- Replay checks CPU responses and autonomous preconditions, rather than
trusting a friendlier response or a claimed RX acceptance. -/
def applyEvent (s : State) : Event → Option State
  | .cpu r gpio response =>
    if (access gpio r s).1 = response then some (access gpio r s).2 else none
  | .tick => some { s with timer := s.timer + 1 }
  | .txComplete byte => if s.tx = some byte then some { s with tx := none } else none
  | .receive byte accepted =>
    if s.rx.isNone = accepted then some (receive (some byte) s) else none
  | .framingError => some { s with framing := true }
  | .reset => some initial

def replay (s : State) : List Event → Option State
  | [] => some s
  | e :: rest => (applyEvent s e).bind (fun next => replay next rest)

theorem access_fault (gpio : Word) (r : Request) (s : State) (fault : Fault)
    (h : (access gpio r s).1 = .fault fault) : (access gpio r s).2 = s := by
  unfold access at *
  repeat' split at *
  all_goals simp_all

theorem access_timer (gpio : Word) (r : Request) (s : State) :
    (access gpio r s).2.timer = s.timer := by
  unfold access
  repeat' split
  all_goals rfl

theorem access_busy_tx (gpio : Word) (r : Request) (s : State) (byte : Byte)
    (h : s.tx = some byte) : (access gpio r s).2.tx = some byte := by
  unfold access
  repeat' split
  all_goals simp_all

theorem replay_autonomous (i : Input) (before current : State)
    (timer : current.timer = before.timer)
    (tx : ∀ byte, before.tx = some byte → current.tx = some byte) :
    replay current (autonomousEvents i before current) = some (autonomous i before current) := by
  cases hc : i.txComplete <;> cases ht : before.tx <;>
    cases hr : current.rx <;> cases hi : i.rxArrival <;> cases hf : i.framingError <;>
    simp_all [autonomousEvents, autonomous, completedTx, replay, applyEvent, receive]

theorem replay_append (s : State) (first rest : List Event) :
    replay s (first ++ rest) = (replay s first).bind (fun middle => replay middle rest) := by
  induction first generalizing s with
  | nil => rfl
  | cons event tail ih =>
    simp only [List.cons_append, replay]
    cases he : applyEvent s event <;> simp [ih]

/-- Every extracted edge replays exactly, including faulting operations,
autonomous changes, and reset. No initialization invariant is needed. -/
theorem replay_events (i : Input) (s : State) : replay s (events i s) = some (step i s) := by
  cases hr : i.reset
  · cases ho : i.operation with
    | none =>
      simpa [events, step, cpuState, hr, ho] using
        replay_autonomous i s s rfl (fun _ h => h)
    | some r =>
      simpa [events, step, cpuState, hr, ho, replay, applyEvent] using
        replay_autonomous i s (access i.gpioInput r s).2 (access_timer _ _ _)
          (fun byte h => access_busy_tx _ _ _ byte h)
  · simp [events, step, hr, replay, applyEvent]

theorem replay_history (s : State) (traffic : List Input) :
    replay s (component.eventTrace events s traffic) = some (component.run s traffic) := by
  induction traffic generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [Timed.Component.eventTrace, Timed.Component.run, component, replay_append,
      replay_events, Option.bind_some]
    exact ih _

def eventSpec : Timed.EventSpec State Event := ⟨fun before event after =>
  applyEvent before event = some after⟩

theorem replay_path {s t : State} {es : List Event} (h : replay s es = some t) :
    eventSpec.Path s es t := by
  induction es generalizing s with
  | nil =>
    have same : s = t := by simpa [replay] using h
    subst t
    exact .nil _
  | cons e rest ih =>
    cases he : applyEvent s e with
    | none => simp [replay, he] at h
    | some middle =>
      exact .cons he (ih (by simpa [replay, he] using h))

/-- This is a device-event refinement, not processor retirement or UART-wire
correctness. Every state is admitted and every frontend event sequence is legal. -/
def refinement : Timed.EventRefinement component eventSpec events (fun _ _ => True) where
  Rel concrete abstract := concrete = abstract
  edge i s a related _ := by
    subst a
    exact ⟨step i s, replay_path (replay_events i s), rfl⟩

theorem coverage : refinement.InitialCoverage (fun _ => True) (fun _ => True) where
  nonempty := ⟨initial, trivial⟩
  covered s _ := ⟨s, trivial, rfl⟩

def Event.request : Event → Option Request
  | .cpu r _ _ => some r
  | _ => none

def Event.response : Event → Option Response
  | .cpu _ _ response => some response
  | _ => none

def accepted (i : Input) : List Request := if i.reset then [] else i.operation.toList

theorem event_requests (i : Input) (s : State) :
    (events i s).filterMap Event.request = accepted i := by
  cases hr : i.reset <;> cases ho : i.operation <;>
    cases ht : completedTx i s <;> cases hx : i.rxArrival <;> cases hf : i.framingError <;>
    simp [events, autonomousEvents, accepted, Event.request, hr, ho, ht, hx, hf]

theorem event_responses (i : Input) (s : State) :
    (events i s).filterMap Event.response = (observe i s).toList := by
  cases hr : i.reset <;> cases ho : i.operation <;>
    cases ht : completedTx i s <;> cases hx : i.rxArrival <;> cases hf : i.framingError <;>
    simp [events, autonomousEvents, observe, Event.response, hr, ho, ht, hx, hf]

theorem response_count (i : Input) (s : State) :
    (observe i s).toList.length = (accepted i).length := by
  cases hr : i.reset <;> cases ho : i.operation <;> simp [observe, accepted, hr, ho]

theorem bounded_response (i : Input) (s : State) (r : Request)
    (hr : i.reset = false) (ho : i.operation = some r) :
    observe i s = some (access i.gpioInput r s).1 := by
  simp [observe, hr, ho]

theorem request_history (s : State) (traffic : List Input) :
    (component.eventTrace events s traffic).filterMap Event.request = traffic.flatMap accepted := by
  induction traffic generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [Timed.Component.eventTrace, List.filterMap_append, event_requests, List.flatMap_cons]
    rw [ih]

theorem response_history_count (s : State) (traffic : List Input) :
    ((component.eventTrace events s traffic).filterMap Event.response).length =
      (traffic.flatMap accepted).length := by
  induction traffic generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [Timed.Component.eventTrace, List.filterMap_append, event_responses,
      List.length_append, response_count, List.flatMap_cons]
    rw [ih]

theorem reset_step (i : Input) (s : State) (hr : i.reset = true) : step i s = initial := by
  simp [step, hr]

theorem reset_observe (i : Input) (s : State) (hr : i.reset = true) : observe i s = none := by
  simp [observe, hr]

theorem reset_events (i : Input) (s : State) (hr : i.reset = true) : events i s = [.reset] := by
  simp [events, hr]

theorem fault_step (i : Input) (s : State) (r : Request) (reason : Fault)
    (hr : i.reset = false) (ho : i.operation = some r)
    (hf : (access i.gpioInput r s).1 = .fault reason) :
    step i s = autonomous i s s := by
  simp [step, hr, cpuState, ho, access_fault _ _ _ _ hf]

theorem idle_response (i : Input) (s : State) (ho : i.operation = none) : observe i s = none := by
  simp [observe, ho]

@[simp] theorem receive_timer (arrival : Option Byte) (s : State) :
    (receive arrival s).timer = s.timer := by
  cases arrival <;> simp [receive]
  split <;> rfl

@[simp] theorem receive_gpio (arrival : Option Byte) (s : State) :
    (receive arrival s).gpioOut = s.gpioOut := by
  cases arrival <;> simp [receive]
  split <;> rfl

@[simp] theorem receive_tx (arrival : Option Byte) (s : State) :
    (receive arrival s).tx = s.tx := by
  cases arrival <;> simp [receive]
  split <;> rfl

@[simp] theorem receive_framing (arrival : Option Byte) (s : State) :
    (receive arrival s).framing = s.framing := by
  cases arrival <;> simp [receive]
  split <;> rfl

theorem timer_ticks (i : Input) (s : State) (hr : i.reset = false) :
    (step i s).timer = s.timer + 1 := by
  simp [step, hr, autonomous]

theorem gpio_sample (i : Input) (s : State) (data : Word)
    (hr : i.reset = false) (ho : i.operation = some ⟨.gpio, 0, false, data⟩) :
    observe i s = some (.read i.gpioInput) := by
  simp [observe, access, hr, ho]

theorem gpio_write (i : Input) (s : State) (data : Word)
    (hr : i.reset = false) (ho : i.operation = some ⟨.gpio, 1, true, data⟩) :
    observe i s = some .stored ∧ (step i s).gpioOut = data := by
  simp [observe, step, access, autonomous, cpuState, hr, ho]

theorem timer_sample (i : Input) (s : State) (data : Word)
    (hr : i.reset = false) (ho : i.operation = some ⟨.timer, 0, false, data⟩) :
    observe i s = some (.read s.timer) ∧ (step i s).timer = s.timer + 1 := by
  simp [observe, access, hr, ho, timer_ticks i s hr]

theorem tx_start (i : Input) (s : State) (data : Word)
    (hr : i.reset = false) (ho : i.operation = some ⟨.uart, 1, true, data⟩)
    (ht : s.tx = none) :
    observe i s = some .stored ∧ (step i s).tx = some (data.extractLsb' 0 8) := by
  cases hc : i.txComplete <;>
    simp [observe, step, access, autonomous, cpuState, completedTx, hr, ho, ht, hc]

theorem tx_busy_complete (i : Input) (s : State) (data : Word) (byte : Byte)
    (hr : i.reset = false) (ho : i.operation = some ⟨.uart, 1, true, data⟩)
    (ht : s.tx = some byte) (hc : i.txComplete = true) :
    observe i s = some (.fault .txBusy) ∧ (step i s).tx = none := by
  simp [observe, step, access, autonomous, cpuState, completedTx, hr, ho, ht, hc]

theorem rx_consume_arrival (i : Input) (s : State) (data : Word) (old new : Byte)
    (hr : i.reset = false) (ho : i.operation = some ⟨.uart, 2, false, data⟩)
    (hx : s.rx = some old) (ha : i.rxArrival = some new) :
    observe i s = some (.read (old.setWidth 32)) ∧
      (step i s).rx = some new ∧ (step i s).overrun = s.overrun := by
  simp [observe, step, access, autonomous, cpuState, receive, hr, ho, hx, ha]

theorem rx_empty_arrival (i : Input) (s : State) (data : Word) (new : Byte)
    (hr : i.reset = false) (ho : i.operation = some ⟨.uart, 2, false, data⟩)
    (hx : s.rx = none) (ha : i.rxArrival = some new) :
    observe i s = some (.fault .rxEmpty) ∧
      (step i s).rx = some new ∧ (step i s).overrun = s.overrun := by
  simp [observe, step, access, autonomous, cpuState, receive, hr, ho, hx, ha]

theorem errors_override_clear (i : Input) (s : State) (data : Word) (old new : Byte)
    (hr : i.reset = false) (ho : i.operation = some ⟨.uart, 3, true, data⟩)
    (hx : s.rx = some old) (ha : i.rxArrival = some new) (hf : i.framingError = true) :
    observe i s = some .stored ∧ (step i s).rx = some old ∧
      (step i s).overrun = true ∧ (step i s).framing = true := by
  simp [observe, step, access, autonomous, cpuState, receive, hr, ho, hx, ha, hf]

theorem autonomous_no_cpu_response (i : Input) (s : State)
    (hr : i.reset = false) (ho : i.operation = none) :
    observe i s = none ∧ (step i s).timer = s.timer + 1 ∧
      (events i s).filterMap Event.response = [] := by
  simp [idle_response i s ho, timer_ticks i s hr, event_responses]

end Pinwheel.Hardware.Processor.MmioModel
