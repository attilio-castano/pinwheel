import Lean
import Pinwheel.Hardware.Processor.SerialModelProofs

open Lean Elab Pinwheel.Hardware Pinwheel.Hardware.Processor

/-! The two independent component oracles are reused from the established
MMIO/UART test methodology: integer register dispatch, a queue of wire periods,
and RX phase-local countdowns. Composition below uses neither production
cpuState/mmioInput/uartInput nor either production step/observe for expectations.
-/
namespace ProcessorSerialModelTests
namespace RefMmio
open MmioModel

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

end RefMmio
namespace RefUart
open Uart

/-- Independent TX representation: a queue containing every untransmitted
period. RX uses phase-local countdowns, not the model's absolute sample times. -/
structure Reference where
  txBits : List Bool := []
  txByte : Nat := 0
  rxPhase : Nat := 0
  rxRemaining : Nat := 0
  rxBit : Nat := 0
  rxByte : Nat := 0
  deriving Repr

def numericBit (byte index : Nat) : Bool := byte / 2^index % 2 == 1

def bitstream (divisor byte : Nat) : List Bool :=
  List.replicate divisor false ++ (List.range 8).flatMap (fun k => List.replicate divisor (numericBit byte k)) ++
  List.replicate divisor true

def referenceOutput (i : Input) (r : Reference) : Output :=
  if i.reset then ⟨true, false, false, none, false⟩ else
    let boundary := r.rxPhase == 3 && r.rxRemaining == 0
    ⟨r.txBits.headD true, r.txBits.isEmpty, r.txBits.length == 1,
      if boundary && i.rx then some (BitVec.ofNat 8 r.rxByte) else none, boundary && !i.rx⟩

def referenceStep (d : Nat) (i : Input) (r : Reference) : Reference := Id.run do
  if i.reset then return {}
  let mut next := r
  if !r.txBits.isEmpty then next := { next with txBits := r.txBits.tail }
  else if let some byte := i.offer then next := { next with txBits := bitstream d byte.toNat, txByte := byte.toNat }
  if r.rxPhase == 0 then
    if !i.rx then next := { next with rxPhase := 1, rxRemaining := d/2-1, rxBit := 0, rxByte := 0 }
  else if r.rxPhase == 4 then
    if i.rx then next := { next with rxPhase := 0 }
  else if r.rxRemaining != 0 then next := { next with rxRemaining := r.rxRemaining-1 }
  else if r.rxPhase == 1 then
    next := if i.rx then { next with rxPhase := 0 }
      else { next with rxPhase := 2, rxRemaining := d-1 }
  else if r.rxPhase == 2 then
    let value := r.rxByte + if i.rx then 2^r.rxBit else 0
    next := { next with
      rxPhase := (if r.rxBit == 7 then 3 else 2)
      rxRemaining := d-1
      rxBit := r.rxBit+1
      rxByte := value }
  else next := { next with rxPhase := if i.rx then 0 else 4 }
  return next

def referenceState (d : Nat) (r : Reference) : State :=
  let tx := if r.txBits.isEmpty then TxState.idle else .active (BitVec.ofNat 8 r.txByte) (10*d-r.txBits.length)
  let rx := if r.rxPhase == 0 then RxState.idle else if r.rxPhase == 4 then .waitHigh else
    let elapsed := if r.rxPhase == 1 then d/2-1-r.rxRemaining
      else if r.rxPhase == 2 then d/2+r.rxBit*d+(d-1-r.rxRemaining)
      else d/2+8*d+(d-1-r.rxRemaining)
    .receiving elapsed (BitVec.ofNat 8 r.rxByte)
  ⟨tx, rx⟩

end RefUart

open SerialModel

structure Reference where
  mmio : RefMmio.RefState := RefMmio.refInitial
  uart : RefUart.Reference := {}
  deriving Repr

def restore (d : Nat) (r : Reference) : State :=
  ⟨⟨BitVec.ofNat 32 r.mmio.gpio, BitVec.ofNat 32 r.mmio.timer,
    r.mmio.tx.map (BitVec.ofNat 8), r.mmio.rx.map (BitVec.ofNat 8), r.mmio.overrun, r.mmio.framing⟩,
    RefUart.referenceState d r.uart⟩

def referenceCPU (i : Input) (r : Reference) : RefMmio.RefState :=
  match i.operation with
  | none => r.mmio
  | some request => (RefMmio.refAccess i.gpioInput.toNat request r.mmio).2

def frontendInput (i : Input) (r : Reference) : Uart.Input :=
  ⟨i.reset, (referenceCPU i r).tx.map (BitVec.ofNat 8), i.rx⟩

def referenceInput (i : Input) (r : Reference) : MmioModel.Input :=
  let wire := RefUart.referenceOutput (frontendInput i r) r.uart
  ⟨i.reset, i.operation, i.gpioInput, wire.complete, wire.arrival, wire.framingError⟩

def referenceStep (d : Nat) (i : Input) (r : Reference) : Reference :=
  ⟨(RefMmio.refEdge (referenceInput i r) r.mmio).2.1,
    RefUart.referenceStep d (frontendInput i r) r.uart⟩

def responseCapture (o : Output) := o.response.map RefMmio.response
def referenceResponse (i : Input) (r : Reference) := (RefMmio.refEdge (referenceInput i r) r.mmio).1

structure Machine where
  next : Uart.Timing → Input → State → State := step
  output : Uart.Timing → Input → State → Output := observe

def observationsMatch (machine : Machine) (d : Uart.Timing) (i : Input) (s : State) (r : Reference) : Bool :=
  let o := machine.output d i s
  responseCapture o == referenceResponse i r &&
    o.frontend == RefUart.referenceOutput (frontendInput i r) r.uart &&
    o.gpioOutput.toNat == (if i.reset then 0 else r.mmio.gpio)

structure Ledger where
  nextId : Nat := 0
  accepted : List (Nat × Nat) := []
  retired : List (Nat × Nat) := []
  pending : Option (Nat × Nat) := none
  rxAccepted : List Nat := []
  rxRetired : List Nat := []
  rxPending : Option Nat := none
  deriving Repr

/-- Ordered occurrence identities are allocated on actual admissions, never
matched by byte value. Repeated equal payloads therefore remain separate. -/
def account (d : Uart.Timing) (i : Input) (s next : State) (ledger : Ledger) : IO Ledger := do
  let mut result := ledger
  for value in (txRetired d i s) do
    let some token := result.pending | throw (IO.userError "Unowned TX retirement")
    unless token.2 == value.toNat do throw (IO.userError "TX retirement byte mismatch")
    result := { result with pending := none, retired := result.retired ++ [token] }
  if let some byte := Uart.accepted (uartInput i s) s.uart.tx then
    unless result.pending.isNone do throw (IO.userError "Duplicate in-flight TX acceptance")
    let token := (result.nextId, byte.toNat)
    result := { result with nextId := result.nextId+1, accepted := result.accepted ++ [token], pending := some token }
  result := { result with
    rxAccepted := result.rxAccepted ++ (rxAccepted d i s).toList.map BitVec.toNat,
    rxRetired := result.rxRetired ++ (rxRetired i s).map BitVec.toNat,
    rxPending := next.mmio.rx.map BitVec.toNat }
  unless result.accepted == result.retired ++ result.pending.toList &&
      result.pending.map Prod.snd == next.mmio.tx.map BitVec.toNat &&
      result.rxAccepted == result.rxRetired ++ result.rxPending.toList do
    throw (IO.userError "Occurrence/pending conservation failed")
  return result

def edgeMatches (machine : Machine) (d : Uart.Timing) (i : Input) (s : State) (r : Reference) : Bool :=
  let next := machine.next d i s
  let expected := referenceStep d.divisor i r
  s == restore d.divisor r && next == restore d.divisor expected &&
    observationsMatch machine d i s r && observationsMatch machine d i next expected

def replay (d : Uart.Timing) (traffic : List Input) (start : Reference := {}) : IO Nat := do
  let mut s := restore d.divisor start
  let mut r := start
  let mut ledger : Ledger := {
    pending := start.mmio.tx.map (fun b => (0,b)),
    accepted := start.mmio.tx.toList.map (fun b => (0,b)), nextId := start.mmio.tx.isSome.toNat,
    rxAccepted := start.mmio.rx.toList, rxPending := start.mmio.rx }
  let mut cycles := 0
  for i in traffic do
    unless edgeMatches {} d i s r do
      throw (IO.userError s!"Serial mismatch D={d.divisor}, edge={cycles}, input={repr i}, state={repr s}, reference={repr r}")
    let expected := RefMmio.refEdge (referenceInput i r) r.mmio
    let log := (deviceEvents d i s).map RefMmio.captureEvent
    unless log == expected.2.2 && RefMmio.refReplay r.mmio log == some expected.2.1 do
      throw (IO.userError "Actual device event ordering/replay mismatch")
    let cpu := referenceCPU i r
    let wire := RefUart.referenceOutput (frontendInput i r) r.uart
    let expectedAccept := if !i.reset && r.uart.txBits.isEmpty then cpu.tx else none
    let expectedConsume := if !i.reset && i.operation.any (fun op =>
      op.device == .uart && op.word.toNat == 2 && !op.write) then r.mmio.rx else none
    unless (txWrite i s).map BitVec.toNat == expectedAccept &&
        (Uart.accepted (uartInput i s) s.uart.tx).map BitVec.toNat == expectedAccept &&
        (rxConsumed i s).map BitVec.toNat == expectedConsume &&
        (rxAccepted d i s).map BitVec.toNat == (if cpu.rx.isNone then wire.arrival.map BitVec.toNat else none) &&
        (rxDropped d i s).map BitVec.toNat == (if cpu.rx.isSome then wire.arrival.map BitVec.toNat else none) do
      throw (IO.userError "CPU/wire acceptance or RX disposition mismatch")
    let next := step d i s
    ledger ← account d i s next ledger
    s := next
    r := referenceStep d.divisor i r
    cycles := cycles+1
  return cycles

def request (device : MmioModel.Device) (word : Nat) (write : Bool) (data : Nat := 0) : Option MmioModel.Request :=
  some ⟨device, BitVec.ofNat 6 word, write, BitVec.ofNat 32 data⟩

def writeTX (byte : Nat) : Input := { operation := request .uart 1 true (0x91820000+byte) }
def readRX : Input := { operation := request .uart 2 false }
def clearErrors : Input := { operation := request .uart 3 true 12 }

def line (d byte time : Nat) : Bool :=
  if time < d then false else if time < 9*d then RefUart.numericBit byte (time/d-1) else true

def frame (d byte : Nat) (readAtStop : Bool := false) (badStop : Bool := false) : List Input :=
  (List.range (d/2+9*d+1)).map fun time =>
    { rx := if time == d/2+9*d && badStop then false else line d byte time
      operation := if time == d/2+9*d && readAtStop then readRX.operation else none }

def quiet : Input := {}

def transmit (d byte : Nat) : List Input :=
  [writeTX byte] ++ List.replicate (10*d) (writeTX byte) ++ List.replicate 3 quiet ++
    [writeTX byte] ++ List.replicate (10*d+3) quiet

def timing (n : Nat) : IO Uart.Timing :=
  match Uart.Timing.check n with | some d => pure d | none => throw (IO.userError "Bad test divisor")

def matrix : IO Nat := do
  let mut edges := 0
  for divisor in [4,6,10,32] do
    let d ← timing divisor
    let bytes := if divisor == 4 then List.range 256 else [0,1,2,3,0x55,0x7f,0x80,0x81,0xa5,0xfe,0xff]
    for byte in bytes do
      edges := edges + (← replay d (transmit divisor byte))
      for full in [false,true] do
        for consume in [false,true] do
          let start : Reference := { mmio := { RefMmio.refInitial with
            rx := if full then some (255-byte) else none, timer := 0xfffffff0,
            gpio := 0x91827364, overrun := false, framing := true } }
          edges := edges + (← replay d (frame divisor byte consume ++ [readRX, readRX, {}]) start)
    -- Every frame phase can be aborted, including the would-be closing edge.
    for cut in [0:10*divisor+1] do
      let before := [writeTX 0x96] ++ (List.range cut).map (fun k => ({ rx := line divisor 0x69 k } : Input))
      edges := edges + (← replay d (before ++ [{ reset := true, operation := (writeTX 0x96).operation, rx := false },
        {}, writeTX 0x96] ++ List.replicate (10*divisor+2) quiet))
    let malformed := (frame divisor 0xa5 false true).dropLast ++
      [{ clearErrors with rx := false }] ++ List.replicate (3*divisor) ({ rx := false } : Input) ++ [quiet]
    edges := edges + (← replay d malformed)
    -- New overrun wins software clearing on a valid stop sample.
    let full : Reference := { mmio := { RefMmio.refInitial with rx := some 0x55 } }
    edges := edges + (← replay d ((frame divisor 0xa5).dropLast ++ [clearErrors, readRX]) full)
    -- RX detection delayed D/2 aligns its stop with the TX completion edge.
    -- The simultaneous busy TX write faults while the independent RX overflows.
    let duplex := (List.range (10*divisor+1)).map fun time =>
      { operation := if time == 0 || time == 10*divisor then (writeTX 0x55).operation else none
        rx := if time < divisor/2 then true else line divisor 0xa5 (time-divisor/2) : Input }
    edges := edges + (← replay d (duplex ++ [readRX, writeTX 0x55] ++ List.replicate (10*divisor+2) quiet) full)
    -- Empty reads, register holes, direction faults, GPIO and timer accesses
    -- continue while TX/RX run, with wrapping timer and periodic reset.
    let mut traffic : List Input := []
    let mut seed := 31337+divisor
    for cycle in [0:2048] do
      seed := (1664525*seed+1013904223)%4294967296
      let device := if cycle%7 == 0 then MmioModel.Device.gpio else if cycle%11 == 0 then .timer else .uart
      traffic := {
        reset := cycle%173 == 0,
        operation := if seed%5 == 0 then none else request device (seed/5%8) (seed/7%2 == 0) seed,
        gpioInput := BitVec.ofNat 32 (seed/3), rx := line divisor (cycle/(10*divisor)%256) (cycle%(10*divisor)) } :: traffic
    edges := edges + (← replay d traffic.reverse)
  return edges

def changed (mutant : Nat) : Machine where
  next d i s :=
    let next := step d i s
    match mutant with
    | 0 => { next with uart := Uart.step d ⟨i.reset, s.mmio.tx, i.rx⟩ s.uart }
    | 1 => if (txComplete d i s).isSome then { next with mmio := { next.mmio with tx := s.mmio.tx } } else next
    | 2 => if (txComplete d i s).isSome then { next with uart := { next.uart with
        tx := s.mmio.tx.elim .idle (fun byte => .active byte 0) } } else next
    | 3 => if (txComplete d i s).isSome then { next with mmio := { next.mmio with
        tx := (cpuState i { s with mmio := { s.mmio with tx := none } }).tx } } else next
    | 4 => if i.operation.isNone then { next with mmio := MmioModel.step { (mmioInput d i s) with rxArrival := none } s.mmio } else next
    | 5 => if let some byte := (mmioInput d i s).rxArrival then
        { next with mmio := { next.mmio with rx := some byte } } else next
    | 6 => if i.operation == clearErrors.operation then { next with mmio := { next.mmio with framing := false } } else next
    | 7 => if i.reset then { next with uart := s.uart } else next
    | 8 => if i.reset then { next with mmio := { next.mmio with rx := s.mmio.rx } } else next
    | _ => if i.operation.isSome && !i.reset then { next with mmio := { next.mmio with timer := next.mmio.timer+1 } } else next

def mutations : IO (Nat × Nat) := do
  let d ← timing 4
  let mut controls := 0
  let mut baselineEdges := 0
  for mutant in [0:10] do
    let (traffic, start) : List Input × Reference :=
      if mutant < 4 then (transmit 4 0x55, {})
      else if mutant == 4 then (frame 4 0x96, {})
      else if mutant == 5 then (frame 4 0x96, { mmio := { RefMmio.refInitial with rx := some 0x55 } })
      else if mutant == 6 then ((frame 4 0xa5 false true).dropLast ++ [{ clearErrors with rx := false }], {})
      else if mutant == 7 then ([writeTX 0x96, {}, { reset := true }], {})
      else if mutant == 8 then ([{ reset := true }], { mmio := { RefMmio.refInitial with rx := some 0x55 } })
      else ([writeTX 0], {})
    baselineEdges := baselineEdges + (← replay d traffic start)
    let machine := changed mutant
    let mut s := restore 4 start
    let mut r := start
    let mut found := false
    for i in traffic do
      if !edgeMatches machine d i s r then found := true; break
      s := machine.next d i s
      r := referenceStep 4 i r
    unless found do throw (IO.userError s!"Undetected actual serial composition mutant {mutant}")
    controls := controls+1
  return (controls, baselineEdges)

elab "#audit_serial_model" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.SerialModel." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.SerialModel" then
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved serial model axioms in {name}: {bad}"
      count := count+1
  if count < 50 then throwError "Incomplete serial model audit"
  logInfo m!"Serial model audit: {count} declarations, standard axioms only."

#audit_serial_model

def main : IO Unit := do
  let edges ← matrix
  let (controls, positiveEdges) ← mutations
  IO.println s!"Serial MMIO/UART: {edges} independent full-state/pre/post/event edges; {controls} actual composition mutants with {positiveEdges} passing baseline edges."

end ProcessorSerialModelTests

def main := ProcessorSerialModelTests.main
