import Lean
import Pinwheel.Hardware.Processor.SerialCircuitProofs

open Lean Elab Pinwheel.Hardware Pinwheel.Hardware.Processor

/-! Independent numeric raw-state oracle. The expected CPU dispatch, TX bit
periods, RX sample positions, retained inactive fields, and simultaneous device
updates are computed without any production model/circuit evaluator. -/
namespace ProcessorSerialCircuitTests

abbrev Row := Array Nat
def wordMask : Nat := 4294967296
def bit (n k : Nat) : Nat := n / 2^k % 2
def flag (p : Bool) : Nat := if p then 1 else 0

def frontend (divisor : Nat) (i s : Row) : Row := Id.run do
  if i[0]! == 1 then return #[1,0,0,0,0,0]
  let txActive := s[8]! == 1
  let txGood := s[9]! < 10*divisor
  let closeTx := txActive && txGood && s[9]!+1 == 10*divisor
  let closeRx := s[11]! == 1 && s[12]!+1 == divisor/2+9*divisor
  let tx := if !txActive || !txGood || 9*divisor ≤ s[9]! then 1 else
    if s[9]! < divisor then 0 else bit s[10]! (s[9]!/divisor-1)
  return #[tx,flag (!txActive),flag closeTx,flag (closeRx && i[7]! == 1),
    if closeRx && i[7]! == 1 then s[13]! else 0,flag (closeRx && i[7]! == 0)]

def response (i s : Row) : Nat × Nat := Id.run do
  let device := i[2]!
  let write := i[3]! == 1
  let reg := i[4]!
  if device == 0 then
    if reg == 0 then return (if write then 3 else 0,if write then 0 else i[6]!)
    if reg == 1 then return (if write then 1 else 0,if write then 0 else s[0]!)
    return (2,0)
  if device == 1 then
    if reg != 0 then return (2,0)
    return (if write then 3 else 0,if write then 0 else s[1]!)
  if device == 3 || reg > 3 then return (2,0)
  if reg == 0 then
    return (if write then 3 else 0,if write then 0 else
      (1-s[2]!)+2*s[4]!+4*s[6]!+8*s[7]!)
  if reg == 1 then return (if !write then 3 else if s[2]! == 1 then 4 else 1,0)
  if reg == 2 then return (if write then 3 else if s[4]! == 0 then 5 else 0,
    if !write && s[4]! == 1 then s[5]! else 0)
  return (if write then 1 else 3,0)

def output (divisor : Nat) (i s : Row) : Row :=
  let front := frontend divisor i s
  if i[0]! == 1 then #[0,0,0,0,0,0,0] ++ front else
    let (code,data) := response i s
    #[1,i[1]!,if i[1]! == 1 then code else 0,if i[1]! == 1 then data else 0,
      s[0]!,s[2]!,if s[2]! == 1 then s[3]! else 0] ++ front

def next (divisor : Nat) (i s : Row) : Row := Id.run do
  if i[0]! == 1 then return Array.replicate 14 0
  let front := frontend divisor i s
  let offered := i[1]! == 1
  let writing := i[3]! == 1
  let uart := i[2]! == 2
  let start := offered && uart && i[4]! == 1 && writing && s[2]! == 0
  let consume := offered && uart && i[4]! == 2 && !writing && s[4]! == 1
  let clear := offered && uart && i[4]! == 3 && writing
  let room := s[4]! == 0 || consume
  let receive := front[3]! == 1
  let capture := receive && room
  let overflow := receive && !room
  let offer := start || s[2]! == 1
  let byte := if start then i[5]! % 256 else s[3]!
  let txGood := s[9]! < 10*divisor
  let txAdvance := s[8]! == 1 && txGood && s[9]!+1 < 10*divisor
  let txAccept := s[8]! == 0 && offer
  let rxDetect := s[11]! == 0 && i[7]! == 0
  let stop := divisor/2+9*divisor
  let badStart := s[12]!+1 == divisor/2 && i[7]! == 1
  let rxAdvance := s[11]! == 1 && s[12]! < stop && !badStart && s[12]!+1 < stop
  let rxPhase := if s[11]! == 0 then flag (i[7]! == 0) else
    if s[11]! == 1 then
      if stop ≤ s[12]! || badStart then 0 else if s[12]!+1 == stop then
        (if i[7]! == 1 then 0 else 2) else 1
    else if s[11]! == 2 && i[7]! == 0 then 2 else 0
  let mut rxByte := s[13]!
  if rxDetect then rxByte := 0
  else if rxAdvance then
    for k in [0:8] do
      if s[12]!+1 == divisor/2+(k+1)*divisor then
        rxByte := rxByte - bit rxByte k * 2^k + i[7]!*2^k
  return #[
    if offered && i[2]! == 0 && i[4]! == 1 && writing then i[5]! else s[0]!,
    (s[1]!+1)%wordMask,
    flag (start || (s[2]! == 1 && front[2]! == 0)),if start then byte else s[3]!,
    flag (capture || (s[4]! == 1 && !consume)),if capture then front[4]! else s[5]!,
    flag ((s[6]! == 1 && !(clear && bit i[5]! 2 == 1)) || overflow),
    flag ((s[7]! == 1 && !(clear && bit i[5]! 3 == 1)) || front[5]! == 1),
    flag (if s[8]! == 1 then txAdvance else offer),
    if txAccept then 0 else if txAdvance then s[9]!+1 else s[9]!,
    if txAccept then byte else s[10]!,rxPhase,
    if rxDetect then 0 else if rxAdvance then s[12]!+1 else s[12]!,rxByte]

def pins (i : Row) : Values SerialInterface.Input := fun p =>
  BitVec.ofNat _ i[(SerialInterface.inputs.position p).val]!
def state (d : Uart.Timing) (s : Row) : Values (SerialCircuit.Register d) := fun p =>
  BitVec.ofNat _ s[((SerialCircuit.registers d).position p).val]!
def capture (desc : Interface P) (v : Values P) : Row := desc.ports.map fun ⟨_,p⟩ => (v p).toNat

def edgeMatches (c : Circuit SerialInterface.Input (SerialCircuit.Register d) SerialInterface.Output)
    (i s : Row) : Bool :=
  let raw : Values (SerialCircuit.Register d) := state d s
  let ip : Values SerialInterface.Input := pins i
  let after := next d.divisor i s
  let actualNext := capture (SerialCircuit.registers d) (c.step ip raw)
  capture SerialInterface.outputs (c.observe ip raw) == output d.divisor i s &&
    actualNext == after &&
    capture SerialInterface.outputs (c.observe ip (state d actualNext)) == output d.divisor i after

def requireEdge (d : Uart.Timing) (i s : Row) : IO Unit :=
  unless edgeMatches (SerialCircuit.circuit d) i s do
    throw (IO.userError s!"Serial hardware differs: D={d.divisor}, input={i}, state={s}")

def idle : Row := #[0,0,0,0,0,0,0,1]
def writeTX (byte : Nat) : Row := #[0,1,2,1,1,0x87650000+byte,0xdecafbad,1]
def readRX : Row := #[0,1,2,0,2,0,0,1]
def clearErrors : Row := #[0,1,2,1,3,12,0,1]
def zero : Row := Array.replicate 14 0

def replay (d : Uart.Timing) (traffic : List Row) (initial : Row := zero) : IO Nat := do
  let mut s := initial
  for i in traffic do
    requireEdge d i s
    s := next d.divisor i s
  return traffic.length

def rawStates (d : Uart.Timing) : List Row :=
  (List.range 32).map fun k =>
    let counts := #[0,d.divisor/2-1,d.divisor/2+d.divisor-1,d.stopSample-1,d.frame-1,d.frame,2^(Uart.Structural.width d)-1,7]
    #[0x91abcdef,0xfffffffe,k%2,0xa5,k/2%2,0x69,k/4%2,k/8%2,k/16%2,counts[k%8]!,
      0x55,k%4,counts[(k/4)%8]!,0x96]

def timing (n : Nat) : IO Uart.Timing :=
  match Uart.Timing.check n with | some d => pure d | none => throw (IO.userError "Bad test divisor")

def numericLine (divisor byte time : Nat) : Nat :=
  if time < divisor then 0 else if time < 9*divisor then bit byte (time/divisor-1) else 1
def rxFrame (divisor byte : Nat) : List Row :=
  (List.range (divisor/2+9*divisor+1)).map fun t => idle.set! 7 (numericLine divisor byte t)

def matrix : IO Nat := do
  let mut edges := 0
  for divisor in [4,6,10,32] do
    let d ← timing divisor
    for s in rawStates d do
      for device in [0:4] do
        for reg in (if divisor == 4 then List.range 64 else [0,1,2,3,4,63]) do
          for wr in [0:2] do
            for flags in [0:8] do
              let i := #[flags%2,flags/2%2,device,wr,reg,0x8765a50c,0xdecafbad,flags/4%2]
              requireEdge d i s
              edges := edges+1
    for byte in (if divisor == 4 then List.range 256 else [0,1,0x55,0x7f,0x80,0xa5,0xff]) do
      let traffic := [writeTX byte] ++ List.replicate d.frame (writeTX byte) ++ List.replicate 3 idle ++
        [writeTX byte] ++ List.replicate (d.frame+2) idle
      edges := edges + (← replay d traffic)
      -- Independently expanded period list checks duration and LSB-first wire order.
      let periods := List.replicate divisor 0 ++ (List.range 8).flatMap
        (fun k => List.replicate divisor (bit byte k)) ++ List.replicate divisor 1
      let mut s := next divisor (writeTX byte) zero
      for level in periods do
        let actual := (SerialCircuit.circuit d).observe (pins idle) (state d s) (.right Uart.Physical.tx)
        unless actual.toNat == level do throw (IO.userError "Wrong TX frame period")
        s := next divisor idle s
      unless s[2]! == 0 && s[8]! == 0 do throw (IO.userError "TX owner did not complete exactly once")
      for full in [false,true] do
        for consume in [false,true] do
          let start := ((zero.set! 4 full.toNat).set! 5 (255-byte)).set! 1 0xfffffff0
          let frame := rxFrame divisor byte
          let frame := if consume then frame.dropLast ++ [readRX] else frame
          edges := edges + (← replay d (frame ++ [readRX,readRX,idle]) start)
    for cut in [0:d.frame+1] do
      let traffic := [writeTX 0x96] ++ (rxFrame divisor 0x69).take cut ++
        [(writeTX 0xa5).set! 0 1,idle,writeTX 0x55] ++ List.replicate (d.frame+2) idle
      edges := edges + (← replay d traffic)
    let badFrame := (rxFrame divisor 0xa5).dropLast ++ [(clearErrors.set! 7 0)] ++ List.replicate divisor (idle.set! 7 0) ++ [idle]
    edges := edges + (← replay d badFrame)
    edges := edges + (← replay d ((rxFrame divisor 0xa5).dropLast ++ [clearErrors,readRX])
      ((zero.set! 4 1).set! 5 0x55))
  return edges

open SerialCircuit SerialInterface

def delayedInput : {b : Nat} → Uart.Physical.Input b → SerialCircuit.E d b
  | _, .at ⟨1,_⟩ => .reg (mmio MmioCircuit.txActiveReg)
  | _, .at ⟨2,_⟩ => .reg (mmio MmioCircuit.txDataReg)
  | _, p => uartInput p

def changed (which : Nat) (d : Uart.Timing) : Circuit Input (SerialCircuit.Register d) Output where
  next := fun {b} r =>
    if which == 0 then match r with
      | .left _ => (circuit d).next r
      | .right r => ((Uart.Structural.circuit d).next r).bind delayedInput (fun p => .reg (uart p))
    else match b,r with
    | _, .left (.at ⟨2,h⟩) => if which == 1 then
        .mux (uartOutput d Uart.Physical.txComplete) (.reg (mmio MmioCircuit.txActiveReg))
          ((circuit d).next (.left (.at ⟨2,h⟩)))
      else (circuit d).next (.left (.at ⟨2,h⟩))
    | _, .left (.at ⟨5,h⟩) => if which == 2 then
        .mux (uartOutput d Uart.Physical.rxValid) (uartOutput d Uart.Physical.rxData)
          ((circuit d).next (.left (.at ⟨5,h⟩)))
      else (circuit d).next (.left (.at ⟨5,h⟩))
    | _, .left (.at ⟨7,h⟩) => if which == 3 then
        .mux (MmioCircuit.clearErrors.bind cpuInput (fun p => .reg (mmio p))) (.lit 0)
          ((circuit d).next (.left (.at ⟨7,h⟩)))
      else (circuit d).next (.left (.at ⟨7,h⟩))
    | _, .right .txByte => if which == 4 then .mux (.input reset) (.reg (uart .txByte))
        ((circuit d).next (uart .txByte)) else (circuit d).next (uart .txByte)
    | _, .right .txActive => if which == 6 then .mux (uartOutput d Uart.Physical.txComplete) (.lit 1)
        ((circuit d).next (uart .txActive)) else (circuit d).next (uart .txActive)
    | _, .right .rxByte => if which == 8 then
        .mux (.equal (.reg (uart .rxCount)) (.lit (BitVec.ofNat _ (d.half+d.divisor-1))))
          (.reg (uart .rxByte)) ((circuit d).next (uart .rxByte)) else (circuit d).next (uart .rxByte)
    | _, r => (circuit d).next r
  output := fun {b} o => match b,o with
    | _, .left (.at ⟨2,h⟩) => if which == 5 then
        .mux (.band (.inv (.input reset)) (.band (.input requestValid) (.equal (.input device) (.lit 3))))
          (.lit 0) ((circuit d).output (.left (.at ⟨2,h⟩))) else (circuit d).output (.left (.at ⟨2,h⟩))
    | _, .right (.at ⟨0,h⟩) => if which == 7 then
        .mux (.band (.inv (.input reset)) (.band (.reg (uart .txActive))
          (.band (.inv (.ult (.reg (uart .txCount)) (.lit (BitVec.ofNat _ d.divisor))))
            (.ult (.reg (uart .txCount)) (.lit (BitVec.ofNat _ (2*d.divisor)))))))
          (.slice 7 1 (by decide) (.reg (uart .txByte))) ((circuit d).output (.right (.at ⟨0,h⟩)))
      else (circuit d).output (.right (.at ⟨0,h⟩))
    | _, o => (circuit d).output o

def mutations : IO (Nat × Nat) := do
  let d ← timing 4
  let mut checked := 0
  let mut baselineEdges := 0
  for which in [0:9] do
    let (traffic,start) : List Row × Row :=
      if which == 2 then (rxFrame 4 0xa5,(zero.set! 4 1).set! 5 0x55)
      else if which == 3 then ((rxFrame 4 0xa5).dropLast ++ [clearErrors.set! 7 0],zero)
      else if which == 4 then ([writeTX 0x96,idle,idle.set! 0 1],zero)
      else if which == 5 then ([#[0,1,3,0,0,0,0,1]],zero)
      else if which == 8 then (rxFrame 4 0xa5,zero)
      else ([writeTX 0x55] ++ List.replicate (d.frame+2) idle,zero)
    baselineEdges := baselineEdges + (← replay d traffic start)
    let mutant := changed which d
    let mut raw : Values (SerialCircuit.Register d) := state d start
    let mut expected := start
    let mut rejected := false
    for i in traffic do
      let ip : Values Input := pins i
      let actualNext := capture (SerialCircuit.registers d) (mutant.step ip raw)
      let wantedNext := next d.divisor i expected
      if capture outputs (mutant.observe ip raw) != output d.divisor i expected || actualNext != wantedNext ||
          capture outputs (mutant.observe ip (state d actualNext)) != output d.divisor i wantedNext then
        rejected := true
        break
      raw := state d actualNext
      expected := wantedNext
    unless rejected do throw (IO.userError s!"Actual Serial Expr mutant {which} survived")
    checked := checked+1
  return (checked,baselineEdges)

elab "#audit_serial_circuit" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.SerialCircuit." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.SerialCircuit" ||
        name.toString.startsWith "Pinwheel.Hardware.Processor.SerialInterface." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.SerialInterface" then
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved physical serial axioms in {name}: {bad}"
      count := count+1
  if count < 80 then throwError "Incomplete physical serial audit"
  logInfo m!"Physical serial audit: {count} declarations, standard axioms only."

#audit_serial_circuit

def main : IO Unit := do
  let edges ← matrix
  let (controls,baselineEdges) ← mutations
  IO.println s!"Serial hardware: {edges} independent raw-state/full-edge cases; {controls} actual Expr mutants with {baselineEdges} passing baseline edges."

end ProcessorSerialCircuitTests

def main := ProcessorSerialCircuitTests.main
