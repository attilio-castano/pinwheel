import Lean
import Pinwheel.Hardware.Uart.Model

open Lean Elab Pinwheel.Hardware
open Uart

namespace HardwareUartModelTests

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

def checkEdge (d : Timing) (i : Input) (s : State) (r : Reference) : IO (State × Reference) := do
  let next := step d i s
  let rr := referenceStep d.divisor i r
  unless s == referenceState d.divisor r && observe d i s == referenceOutput i r &&
      next == referenceState d.divisor rr && observe d i next == referenceOutput i rr do
    throw (IO.userError s!"UART mismatch D={d.divisor}, input={repr i}, state={repr s}, reference={repr r}, next={repr next}, expected={repr (referenceState d.divisor rr)}")
  return (next, rr)

def transmit (d : Timing) (byte : Nat) : IO Nat := do
  let start : Input := ⟨false, some (BitVec.ofNat 8 byte), true⟩
  let (s0, r0) ← checkEdge d start initial {}
  unless (observe d start s0).line == false do throw (IO.userError "TX start was delayed")
  let mut s := s0
  let mut r := r0
  let mut completedCount := 0
  let mut acceptedCount := 1
  for period in [0:10*d.divisor] do
    let i : Input := ⟨false, if period%3 == 0 then some (BitVec.ofNat 8 (255-byte)) else none, true⟩
    let o := observe d i s
    let symbol := period/d.divisor
    let expectedBit := if symbol == 0 then false else if symbol == 9 then true else numericBit byte (symbol-1)
    unless o.line == expectedBit && o.complete == (period+1 == 10*d.divisor) && !o.ready do
      throw (IO.userError "TX symbol duration/order/completion mismatch")
    completedCount := completedCount + o.complete.toNat
    acceptedCount := acceptedCount + (accepted i s.tx).isSome.toNat
    (s, r) ← checkEdge d i s r
  for _ in [0:3] do (s, r) ← checkEdge d {} s r
  unless completedCount == 1 && acceptedCount == 1 && s.tx == .idle do
    throw (IO.userError "TX duplicated an owned transaction")
  return 10*d.divisor+4

/-- Numeric waveform construction does not call frameBit/periodicLine. Noise
may affect any nonsampling point without changing the expected byte. -/
def receiveLine (d byte time : Nat) (noise : Bool) : Bool :=
  if !noise then
    if time < d then false else if time < 9*d then numericBit byte (time/d-1) else true
  else if time == 0 || time == d/2 then false
  else if time == d/2+9*d then true
  else match (List.range 8).find? (fun k => time == d/2+(k+1)*d) with
    | some k => numericBit byte k
    | none => (time+byte)%2 == 0

def receive (d : Timing) (byte : Nat) (noise : Bool) : IO Nat := do
  let stop := d.divisor/2+9*d.divisor
  let mut s := initial
  let mut r : Reference := {}
  let mut arrivals : List Nat := []
  for time in [0:stop+1] do
    let i : Input := ⟨false, none, receiveLine d.divisor byte time noise⟩
    let o := observe d i s
    if let some value := o.arrival then arrivals := arrivals ++ [value.toNat]
    unless o.arrival.isSome == (time == stop) && !o.framingError do
      throw (IO.userError "RX sampled too early/late or framed a valid schedule as faulty")
    (s, r) ← checkEdge d i s r
  unless arrivals == [byte] && s.rx == .idle do throw (IO.userError "RX byte assembly mismatch")
  return stop+1

def malformedAndReset (d : Timing) : IO Nat := do
  let mut edges := 0
  -- A start glitch is ignored even when a TX frame is active.
  let mut s := initial
  let mut r : Reference := {}
  for time in [0:d.divisor/2+2] do
    let i : Input := ⟨false, if time == 0 then some 0xa5 else none, time != 0⟩
    unless (observe d i s).arrival.isNone && !(observe d i s).framingError do
      throw (IO.userError "False start produced a receive/error event")
    (s, r) ← checkEdge d i s r
    edges := edges+1
  unless s.rx == .idle do throw (IO.userError "False start did not rearm")
  -- A continuous break produces exactly one framing error, then waits high.
  s := initial
  r := {}
  let mut errors := 0
  for _ in [0:21*d.divisor] do
    let i : Input := ⟨false, none, false⟩
    let o := observe d i s
    errors := errors+o.framingError.toNat
    unless o.arrival.isNone do throw (IO.userError "Bad stop emitted a byte")
    (s, r) ← checkEdge d i s r
    edges := edges+1
  unless errors == 1 && s.rx == .waitHigh do throw (IO.userError "Break produced repeated errors or rearmed early")
  (s, r) ← checkEdge d {} s r
  edges := edges+1
  unless s.rx == .idle do throw (IO.userError "High sample did not release break recovery")
  -- Abort at every possible TX-frame position, including its completion edge.
  for cut in [0:10*d.divisor+1] do
    (s, r) ← checkEdge d ⟨false, some 0x96, false⟩ initial {}
    edges := edges+1
    for time in [0:cut] do
      (s, r) ← checkEdge d ⟨false, none, receiveLine d.divisor 0x69 time false⟩ s r
      edges := edges+1
    let reset : Input := ⟨true, some 0xff, false⟩
    unless observe d reset s == ⟨true, false, false, none, false⟩ do
      throw (IO.userError "Reset leaked an acceptance/completion/arrival")
    (s, r) ← checkEdge d reset s r
    edges := edges+1
    unless s == initial do throw (IO.userError "Reset retained UART control")
    (s, r) ← checkEdge d {} s r
    edges := edges+1
  return edges

def backToBack (d : Timing) : IO Nat := do
  let bytes := #[0, 255, 0xa5, 0x81]
  let mut s := initial
  let mut r : Reference := {}
  let mut arrivals : List Nat := []
  for time in [0:bytes.size*10*d.divisor] do
    let frame := time/(10*d.divisor)
    let i : Input := ⟨false, none, receiveLine d.divisor bytes[frame]! (time%(10*d.divisor)) false⟩
    if let some byte := (observe d i s).arrival then arrivals := arrivals ++ [byte.toNat]
    (s, r) ← checkEdge d i s r
  unless arrivals == bytes.toList do throw (IO.userError "Back-to-back frames lost/duplicated a byte")
  return bytes.size*10*d.divisor

def randomHistory (d : Timing) : IO Nat := do
  let mut s := initial
  let mut r : Reference := {}
  let mut seed := 31337+d.divisor
  let mut traffic : List Input := []
  let mut acceptedBytes : List Byte := []
  let mut retiredBytes : List Byte := []
  for cycle in [0:2048] do
    seed := (1664525*seed+1013904223)%4294967296
    let i : Input := ⟨cycle%131 == 0, if seed%5 == 0 then some (BitVec.ofNat 8 (seed/7)) else none, seed/17%2 == 1⟩
    acceptedBytes := acceptedBytes ++ (accepted i s.tx).toList
    retiredBytes := retiredBytes ++ (completed d i s.tx).toList ++ (canceled i s.tx).toList
    traffic := i :: traffic
    (s, r) ← checkEdge d i s r
    unless acceptedBytes == retiredBytes ++ (txPending s.tx).toList do
      throw (IO.userError "Ordered TX completion/cancellation ledger failed")
  unless acceptedHistory d .idle traffic.reverse == acceptedBytes &&
      retiredHistory d .idle traffic.reverse == retiredBytes do
    throw (IO.userError "History extraction differs from per-edge ledger")
  return 2048

/-- Actual executable model modifications, not alterations of oracle answers. -/
def mutant (mode : Nat) (d : Timing) : Timed.Component Input State Output where
  step i s :=
    let good := step d i s
    if mode == 0 then
      match s.tx with
      | .active _ time => if !i.reset && time+2 ≥ d.frame then { good with tx := .idle } else good
      | _ => good
    else if mode == 1 then
      if !i.reset then match i.offer with | some byte => { good with tx := .active byte 0 } | none => good else good
    else if mode == 2 && i.reset then s
    else if mode == 3 then
      match s.rx with
      | .receiving time byte => if !i.reset && time+1 == d.half && i.rx then
          { good with rx := .receiving (time+1) byte } else good
      | _ => good
    else if mode == 4 then
      match good.rx with
      | .receiving time byte => if time == d.dataSample 0 then { good with rx := .receiving time (byte ^^^ 1) } else good
      | _ => good
    else good
  observe i s :=
    let good := observe d i s
    if mode == 5 then
      match s.tx with
      | .active byte time => if !i.reset && time/d.divisor > 0 && time/d.divisor < 9 then
          { good with line := byte.getLsbD (8-time/d.divisor) } else good
      | _ => good
    else if mode == 6 then { good with complete := (completed d { i with reset := false } s.tx).isSome }
    else if mode == 7 then
      match s.rx with
      | .receiving time byte => if !i.reset && time+1 ≥ d.stopSample then { good with arrival := some byte } else good
      | _ => good
    else if mode == 8 then { good with framingError := good.framingError || (s.rx == .waitHigh && !i.reset) }
    else if mode == 9 then { good with line := if i.reset then false else good.line }
    else good

def corruptionControls (d : Timing) : IO Nat := do
  for mode in [0:10] do
    let bad := mutant mode d
    let mut s := initial
    let mut r : Reference := {}
    let mut rejected := false
    let mut rows : List Input := [⟨false, some 0x96, true⟩]
    rows := rows ++ (List.range (10*d.divisor)).map (fun k =>
      ⟨k+1 == 10*d.divisor, if k == 2 then some 0x55 else none, true⟩)
    rows := rows ++ [⟨true, none, true⟩]
    rows := rows ++ (List.range (d.divisor/2+2)).map (fun k => ⟨false, none, k != 0⟩)
    rows := rows ++ [⟨true, none, true⟩]
    rows := rows ++ (List.range (21*d.divisor)).map (fun _ => ⟨false, none, false⟩)
    -- Each exact composed fixture must pass before it can reject a mutant.
    let mut baseline := initial
    let mut baselineReference : Reference := {}
    for i in rows do
      (baseline, baselineReference) ← checkEdge d i baseline baselineReference
    for i in rows do
      let next := bad.step i s
      let rr := referenceStep d.divisor i r
      if bad.observe i s != referenceOutput i r || next != referenceState d.divisor rr then rejected := true
      s := next
      r := rr
    unless rejected do throw (IO.userError s!"Undetected UART executable mutation {mode}")
  return 10

end HardwareUartModelTests

open Lean.Elab.Command

elab "#audit_uart_model" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Uart." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Uart." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved UART axioms in {name}: {bad}"
  if count < 100 then throwError "Incomplete UART model audit"
  logInfo m!"UART model audit: {count} declarations, standard axioms only."

#audit_uart_model

def main : IO Unit := do
  let mut frameEdges := 0
  let mut raceEdges := 0
  for raw in [0:65] do
    unless (Timing.check raw).isSome == (raw ≥ 4 && raw%2 == 0) do throw (IO.userError "Timing admission mismatch")
  for divisor in [4, 6, 10, 32] do
    let some d := Timing.check divisor | throw (IO.userError "Valid timing rejected")
    for byte in [0:256] do
      frameEdges := frameEdges + (← HardwareUartModelTests.transmit d byte)
      frameEdges := frameEdges + (← HardwareUartModelTests.receive d byte false)
      frameEdges := frameEdges + (← HardwareUartModelTests.receive d byte true)
    raceEdges := raceEdges + (← HardwareUartModelTests.malformedAndReset d)
    raceEdges := raceEdges + (← HardwareUartModelTests.backToBack d)
    raceEdges := raceEdges + (← HardwareUartModelTests.randomHistory d)
  let d : Timing := ⟨4, by decide, by decide⟩
  let controls ← HardwareUartModelTests.corruptionControls d
  IO.println s!"UART: {frameEdges} bitstream/countdown edges across all 256 bytes and D=4/6/10/32; {raceEdges} malformed/reset/back-to-back/random edges; 65 parameter checks; {controls} executable mutations rejected."
