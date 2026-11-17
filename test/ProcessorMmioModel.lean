import Lean
import Pinwheel.Hardware.Processor.MmioModel

open Lean Elab
open Pinwheel.Hardware.Processor.MmioModel

namespace ProcessorMmioModelTests

structure RefState where
  gpio : Nat
  timer : Nat
  tx : Option Nat
  rx : Option Nat
  overrun : Bool
  framing : Bool
  deriving BEq, Repr

inductive RefResponse where
  | read (data : Nat) | stored | fault (reason : Nat)
  deriving BEq, Repr

inductive RefEvent where
  | cpu (request : Request) (gpio : Nat) (response : RefResponse)
  | tick | complete (byte : Nat) | receive (byte : Nat) (accepted : Bool)
  | framing | reset
  deriving BEq, Repr

def snapshot (s : State) : RefState :=
  ⟨s.gpioOut.toNat, s.timer.toNat, s.tx.map BitVec.toNat, s.rx.map BitVec.toNat,
    s.overrun, s.framing⟩

def response : Response → RefResponse
  | .read v => .read v.toNat
  | .stored => .stored
  | .fault f => .fault (match f with | .registerHole => 0 | .direction => 1 | .txBusy => 2 | .rxEmpty => 3)

def captureEvent : Event → RefEvent
  | .cpu r g result => .cpu r g.toNat (response result)
  | .tick => .tick
  | .txComplete byte => .complete byte.toNat
  | .receive byte accepted => .receive byte.toNat accepted
  | .framingError => .framing
  | .reset => .reset

def refInitial : RefState := ⟨0, 0, none, none, false, false⟩

/-- Integer/option oracle, with a numeric register dispatch independent of the
production bitvector decoder. No production access/step/event helper is used. -/
def refAccess (gpio : Nat) (r : Request) (s : RefState) : RefResponse × RefState := Id.run do
  let word := r.word.toNat
  let data := r.data.toNat
  match r.device with
  | .gpio =>
    if word > 1 then return (.fault 0, s)
    if word == 0 then return (if r.write then .fault 1 else .read gpio, s)
    if r.write then return (.stored, { s with gpio := data })
    return (.read s.gpio, s)
  | .timer =>
    if word != 0 then return (.fault 0, s)
    return (if r.write then .fault 1 else .read s.timer, s)
  | .uart =>
    if word > 3 then return (.fault 0, s)
    if word == 0 then
      let status := (if s.tx == none then 1 else 0) + (if s.rx != none then 2 else 0) +
        (if s.overrun then 4 else 0) + (if s.framing then 8 else 0)
      return (if r.write then .fault 1 else .read status, s)
    if word == 1 then
      if !r.write then return (.fault 1, s)
      if s.tx != none then return (.fault 2, s)
      return (.stored, { s with tx := some (data % 256) })
    if word == 2 then
      if r.write then return (.fault 1, s)
      if let some byte := s.rx then return (.read byte, { s with rx := none })
      return (.fault 3, s)
    if !r.write then return (.fault 1, s)
    return (.stored, { s with
      overrun := s.overrun && data / 4 % 2 == 0
      framing := s.framing && data / 8 % 2 == 0 })

def refEdge (i : Input) (s : RefState) : Option RefResponse × RefState × List RefEvent := Id.run do
  if i.reset then return (none, refInitial, [.reset])
  let mut current := s
  let mut result := none
  let mut log := []
  if let some r := i.operation then
    let (value, next) := refAccess i.gpioInput.toNat r s
    current := next
    result := some value
    log := [.cpu r i.gpioInput.toNat value]
  current := { current with timer := (s.timer + 1) % 4294967296 }
  log := log ++ [.tick]
  if i.txComplete then
    if let some byte := s.tx then
      current := { current with tx := none }
      log := log ++ [.complete byte]
  if let some byte := i.rxArrival then
    if current.rx == none then
      current := { current with rx := some byte.toNat }
      log := log ++ [.receive byte.toNat true]
    else
      current := { current with overrun := true }
      log := log ++ [.receive byte.toNat false]
  if i.framingError then
    current := { current with framing := true }
    log := log ++ [.framing]
  return (result, current, log)

/-- A second interpretation of the actual event stream checks values and
admission, allowing history reconstruction independently of the edge oracle. -/
def refReplay (s : RefState) (events : List RefEvent) : Option RefState := do
  let mut state := s
  for event in events do
    match event with
    | .cpu r gpio result =>
      let (expected, next) := refAccess gpio r state
      if expected != result then return ← none
      state := next
    | .tick => state := { state with timer := (state.timer + 1) % 4294967296 }
    | .complete byte =>
      if state.tx != some byte then return ← none
      state := { state with tx := none }
    | .receive byte accepted =>
      if accepted then
        if state.rx != none then return ← none
        state := { state with rx := some byte }
      else
        if state.rx == none then return ← none
        state := { state with overrun := true }
    | .framing => state := { state with framing := true }
    | .reset => state := refInitial
  return state

def state (mask : Nat) : State :=
  ⟨BitVec.ofNat 32 (0x91827364+mask), BitVec.ofNat 32 (0xffffffff-mask),
    if mask % 2 == 0 then none else some (BitVec.ofNat 8 (0x80+mask)),
    if mask / 2 % 2 == 0 then none else some (BitVec.ofNat 8 (0xf0+mask)),
    mask / 4 % 2 == 1, mask / 8 % 2 == 1⟩

def request (device : Device) (word : Nat) (write : Bool) (data : Nat) : Request :=
  ⟨device, BitVec.ofNat 6 word, write, BitVec.ofNat 32 data⟩

def accessCases : IO Nat := do
  let mut count := 0
  for mask in [0:16] do
    let s := state mask
    for device in #[Device.gpio, .timer, .uart] do
      for word in [0:64] do
        for write in #[false, true] do
          for data in #[0, 1, 4, 8, 12, 255, 0x80000000, 0xffffffff] do
            let r := request device word write data
            let (expected, next) := refAccess 0xabcd1234 r (snapshot s)
            let actual := access 0xabcd1234 r s
            unless response actual.1 == expected && snapshot actual.2 == next do
              throw (IO.userError s!"Access mismatch {repr r} state{mask}")
            count := count + 1
  return count

def checkEdge (i : Input) (s : State) : IO State := do
  let (value, next, expectedEvents) := refEdge i (snapshot s)
  let actual := step i s
  let actualEvents := events i s
  unless (observe i s).map response == value && snapshot actual == next &&
      actualEvents.map captureEvent == expectedEvents do
    throw (IO.userError s!"Edge mismatch input {repr i}, before {repr s}, expected {repr next}, actual {repr actual}")
  unless replay s actualEvents == some actual && refReplay (snapshot s) (actualEvents.map captureEvent) == some next do
    throw (IO.userError "Actual events failed independent reconstruction")
  let requestCount := if i.reset then 0 else i.operation.toList.length
  unless (actualEvents.filterMap Event.request).length == requestCount &&
      (actualEvents.filterMap Event.response).length == requestCount do
    throw (IO.userError "Response accounting omitted or duplicated a request")
  return actual

def edgeCases : IO Nat := do
  let mut count := 0
  for mask in [0:16] do
    let s := state mask
    let mut operations : Array (Option Request) := #[none]
    for device in #[Device.gpio, .timer, .uart] do
      for word in [0:5] do
        for write in #[false, true] do
          for data in #[0, 12, 0xffffffff] do
            operations := operations.push (some (request device word write data))
    for operation in operations do
      for reset in #[false, true] do
        for txComplete in #[false, true] do
          for arrival in #[none, some (0 : Byte), some (255 : Byte)] do
            for framingError in #[false, true] do
              let i : Input := ⟨reset, operation, 0x01234567, txComplete, arrival, framingError⟩
              let _ ← checkEdge i s
              count := count + 1
  return count

def histories : IO Nat := do
  let mut edges := 0
  for mask in [0:16] do
    let start := state mask
    let mut s := start
    let mut log := []
    let mut seed := 17+mask
    let mut requests := 0
    for cycle in [0:512] do
      seed := (1664525*seed+1013904223)%4294967296
      let device := if seed % 3 == 0 then Device.gpio else if seed % 3 == 1 then .timer else .uart
      let operation := if cycle % 11 == 0 then none else
        some (request device (seed / 7 % 6) (seed / 43 % 2 == 1) seed)
      let i : Input := ⟨cycle % 67 == 0, operation, BitVec.ofNat 32 (seed+cycle),
        seed / 17 % 2 == 1, if cycle % 5 == 0 then some (BitVec.ofNat 8 seed) else none,
        cycle % 13 == 0⟩
      log := log ++ events i s
      requests := requests + (if i.reset then 0 else i.operation.toList.length)
      s ← checkEdge i s
      edges := edges + 1
    unless replay start log == some s && refReplay (snapshot start) (log.map captureEvent) == some (snapshot s) &&
        (log.filterMap Event.request).length == requests && (log.filterMap Event.response).length == requests do
      throw (IO.userError "Cross-reset history lost state or completion occurrences")
  return edges

/-- Corruptions are validly typed alternate semantic results or events. Parser
failures and thrown simulation errors do not qualify as negative controls. -/
def negativeControls : IO Nat := do
  let dirty : State := ⟨0x12345678, 0xffffffff, some 0x42, some 0xa5, true, true⟩
  let input (operation : Option Request) : Input := ⟨false, operation, 0x87654321, false, none, false⟩
  let sample := input (some (request .timer 0 false 0))
  let started := { input (some (request .uart 1 true 0x123456a5)) with txComplete := true }
  let busy := { started with rxArrival := some 0x99 }
  let consume := { input (some (request .uart 2 false 0)) with rxArrival := some 0x11 }
  let clear := { input (some (request .uart 3 true 12)) with rxArrival := some 0x22, framingError := true }
  let reset := { clear with reset := true, txComplete := true }
  let mut rejected := 0
  let resultMutation (i : Input) (s badState : State) (badResponse : Option Response) : IO Unit := do
    let (expected, next, _) := refEdge i (snapshot s)
    unless snapshot badState != next || badResponse.map response != expected do
      throw (IO.userError "Inactive or undetected state/response corruption")
  resultMutation sample dirty (step sample dirty) (some (.read 0))
  rejected := rejected + 1
  let idle := { dirty with tx := none }
  resultMutation started idle { step started idle with tx := none } (observe started idle)
  rejected := rejected + 1
  resultMutation busy dirty { step busy dirty with tx := some 0xa5 } (some .stored)
  rejected := rejected + 1
  resultMutation consume dirty { step consume dirty with rx := none } (observe consume dirty)
  rejected := rejected + 1
  resultMutation clear dirty { step clear dirty with overrun := false, framing := false } (observe clear dirty)
  rejected := rejected + 1
  resultMutation reset dirty (step clear dirty) (observe clear dirty)
  rejected := rejected + 1
  let empty := { dirty with rx := none }
  resultMutation consume empty (step consume empty) (some (.read 0x11))
  rejected := rejected + 1
  let gpioRead := input (some (request .gpio 0 false 0))
  resultMutation gpioRead dirty (step gpioRead dirty) (some (.read dirty.gpioOut))
  rejected := rejected + 1
  let faulty := input (some (request .gpio 0 true 0xabcdef))
  resultMutation faulty dirty { step faulty dirty with gpioOut := 0xabcdef } (observe faulty dirty)
  rejected := rejected + 1
  let invalidEvents : Array (State × List Event) := #[
    (dirty, [.cpu (request .timer 0 false 0) 0 (.read 0)]),
    (dirty, [.txComplete 0xff]),
    (dirty, [.receive 0x11 true]),
    (empty, [.receive 0x11 false]),
    (dirty, [.cpu (request .uart 2 false 0) 0 (.read 0xa5),
      .cpu (request .uart 2 false 0) 0 (.read 0xa5)])]
  for (s, es) in invalidEvents do
    unless (replay s es).isNone && (refReplay (snapshot s) (es.map captureEvent)).isNone do
      throw (IO.userError "Corrupted event accepted by checked replay")
    rejected := rejected + 1
  return rejected

example (i : Input) (s : State) (traffic : List Input) :
    replay s (component.eventTrace events s (i :: traffic)) = some (component.run s (i :: traffic)) :=
  replay_history s _

end ProcessorMmioModelTests

open Lean.Elab.Command

elab "#audit_mmio_model" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.MmioModel." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.MmioModel." then
      count := count + 1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved axioms in {name}: {bad}"
  if count == 0 then throwError "Empty MMIO audit"
  logInfo m!"MMIO model audit: {count} declarations, standard axioms only."

#audit_mmio_model

def main : IO Unit := do
  let accesses ← ProcessorMmioModelTests.accessCases
  let edges ← ProcessorMmioModelTests.edgeCases
  let histories ← ProcessorMmioModelTests.histories
  let negatives ← ProcessorMmioModelTests.negativeControls
  IO.println s!"MMIO: {accesses} independent register accesses, {edges} simultaneous/reset edges, {histories} cross-reset history edges, {negatives} concrete semantic corruptions rejected."
