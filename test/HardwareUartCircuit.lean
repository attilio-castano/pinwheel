import Lean
import Pinwheel.Hardware.Uart.CircuitProofs

open Lean Elab Pinwheel.Hardware
open Uart Uart.Physical Uart.Structural

namespace HardwareUartCircuitTests

def pins (xs : Array Nat) : Values Physical.Input := fun p => match p with
  | .at k => BitVec.ofNat _ (xs[k.val]?.getD 0)

def raw (d : Timing) (xs : Array Nat) : Values (Register d)
  | _, .txActive => BitVec.ofNat _ xs[0]!
  | _, .txCount => BitVec.ofNat _ xs[1]!
  | _, .txByte => BitVec.ofNat _ xs[2]!
  | _, .rxPhase => BitVec.ofNat _ xs[3]!
  | _, .rxCount => BitVec.ofNat _ xs[4]!
  | _, .rxByte => BitVec.ofNat _ xs[5]!

def capture (descriptor : Interface P) (v : Values P) : Array Nat :=
  Array.ofFn fun k : Fin descriptor.size => (v (descriptor.signal k).2).toNat

def numericBit (byte k : Nat) : Nat := byte / 2^k % 2

/-- Independent numeric serialization, also used as an explicit queue of
periods in the frame campaign. No reference calls the UART model or Expr. -/
def symbols (byte : Nat) : Array Nat :=
  #[0] ++ (Array.range 8).map (numericBit byte) ++ #[1]

def bitstream (d byte : Nat) : List Nat :=
  (symbols byte).toList.flatMap (List.replicate d)

def referenceOutput (d : Nat) (i s : Array Nat) : Array Nat :=
  if i[0]! == 1 then #[1, 0, 0, 0, 0, 0] else
    let txLegal := s[0]! == 1 && s[1]! < 10*d
    let closing := s[3]! == 1 && s[4]!+1 == d/2+9*d
    #[if txLegal then (symbols s[2]!)[s[1]!/d]?.getD 1 else 1,
      1-s[0]!, (txLegal && s[1]!+1 == 10*d).toNat,
      (closing && i[3]! == 1).toNat, if closing && i[3]! == 1 then s[5]! else 0,
      (closing && i[3]! == 0).toNat]

def referenceStep (d : Nat) (i s : Array Nat) : Array Nat := Id.run do
  if i[0]! == 1 then return #[0, 0, 0, 0, 0, 0]
  let mut n := s
  if s[0]! == 1 then
    if s[1]!+1 >= 10*d then n := n.set! 0 0
    else n := n.set! 1 (s[1]!+1)
  else if i[1]! == 1 then n := ((n.set! 0 1).set! 1 0).set! 2 i[2]!
  if s[3]! == 0 then
    if i[3]! == 0 then n := ((n.set! 3 1).set! 4 0).set! 5 0
  else if s[3]! == 1 then
    if s[4]! >= d/2+9*d then n := n.set! 3 0
    else if s[4]!+1 == d/2 && i[3]! == 1 then n := n.set! 3 0
    else if s[4]!+1 == d/2+9*d then n := n.set! 3 (if i[3]! == 1 then 0 else 2)
    else
      n := n.set! 4 (s[4]!+1)
      for k in [0:8] do
        if s[4]!+1 == d/2+(k+1)*d then
          n := n.set! 5 (s[5]! - numericBit s[5]! k * 2^k + i[3]! * 2^k)
  else if s[3]! == 2 then
    if i[3]! == 1 then n := n.set! 3 0
  else n := n.set! 3 0
  return n

def validRaw (d : Nat) (s : Array Nat) : Bool :=
  (s[0]! != 1 || s[1]! < 10*d) && (s[3]! != 1 || s[4]! < d/2+9*d) && s[3]! != 3

def checkEdge (d : Timing) (i s : Array Nat) : IO (Array Nat) := do
  let input : Values Physical.Input := pins i
  let state : Values (Register d) := raw d s
  let next : Values (Register d) := (circuit d).step input state
  let expected := referenceStep d.divisor i s
  let actual := capture (registers d) next
  unless actual == expected &&
      capture outputs ((circuit d).observe input state) == referenceOutput d.divisor i s &&
      capture outputs ((circuit d).observe input next) == referenceOutput d.divisor i expected do
    throw (IO.userError s!"UART physical mismatch D={d.divisor}, input{i}, state{s}, actual{actual}, expected{expected}")
  unless validRaw d.divisor actual do throw (IO.userError "Raw state did not recover into invariant")
  if validRaw d.divisor s then
    unless view next == (spec d).step input (view state) do
      throw (IO.userError "UART model projection mismatch")
  return actual

def rawMatrix (d : Timing) : IO Nat := do
  let capacity := 2 ^ width d
  let mut edges := 0
  for count in [0:capacity] do
    for flags in [0:8] do
      for controls in [0:8] do
        let s := #[flags%2, count, (count*17+flags*23)%256, flags/2,
          (count*13+flags*7)%capacity, (count*31+flags*19)%256]
        let i := #[controls%2, controls/2%2, (count+flags*53)%256, controls/4%2]
        let _ ← checkEdge d i s
        edges := edges+1
  return edges

def sampledLine (d byte time : Nat) (noise : Bool) : Nat :=
  if !noise then (bitstream d byte)[time]?.getD 1
  else if time == 0 || time == d/2 then 0
  else if time == d/2+9*d then 1
  else match (List.range 8).find? (fun k => time == d/2+(k+1)*d) with
    | some k => numericBit byte k
    | none => (time+byte)%2

def frameCampaign (d : Timing) (byte : Nat) : IO Nat := do
  let mut s ← checkEdge d #[0, 1, byte, 1] #[0, 7, 0x81, 0, 13, 0x5a]
  let mut completions := 0
  let bits := bitstream d.divisor byte
  let mut edges := 1
  for time in [0:bits.length] do
    let i := #[0, time%2, 255-byte, 1]
    let o := capture outputs ((circuit d).observe (pins i) (raw d s))
    unless o[0]! == bits[time]! && o[1]! == 0 && o[2]! == (time+1 == bits.length).toNat do
      throw (IO.userError "TX bit order/duration/completion violation")
    completions := completions+o[2]!
    s ← checkEdge d i s
    edges := edges+1
  for _ in [0:3] do
    s ← checkEdge d #[0, 0, 0, 1] s
    edges := edges+1
  unless completions == 1 && s[0]! == 0 && s[2]! == byte do
    throw (IO.userError "Owned TX frame repeated or busy offer overwrote its byte")
  for noise in [false, true] do
    s := #[0, 0, 0, 0, 0, 0]
    let mut arrived : Array Nat := #[]
    for time in [0:d.divisor/2+9*d.divisor+1] do
      let i := #[0, 0, 0, sampledLine d.divisor byte time noise]
      let o := capture outputs ((circuit d).observe (pins i) (raw d s))
      unless o[3]! == (time == d.divisor/2+9*d.divisor).toNat && o[5]! == 0 do
        throw (IO.userError "RX event violated the explicit sample schedule")
      if o[3]! == 1 then arrived := arrived.push o[4]!
      s ← checkEdge d i s
      edges := edges+1
    unless arrived == #[byte] && s[3]! == 0 do throw (IO.userError "RX byte reconstruction mismatch")
  return edges

def races (d : Timing) : IO Nat := do
  let mut edges := 0
  -- A break reports exactly once and must observe high before rearming.
  let mut s := #[0, 0, 0, 0, 0, 0]
  let mut errors := 0
  for _ in [0:22*d.divisor] do
    let i := #[0, 0, 0, 0]
    errors := errors+(referenceOutput d.divisor i s)[5]!
    s ← checkEdge d i s
    edges := edges+1
  unless errors == 1 && s[3]! == 2 do throw (IO.userError "Break repeated its framing event")
  s ← checkEdge d #[0, 0, 0, 1] s
  edges := edges+1
  unless s[3]! == 0 do throw (IO.userError "RX did not rearm on high")
  -- Midpoint-high false start is an ignored glitch, with no data/error pulse.
  for time in [0:d.divisor/2+2] do
    let i := #[0, 0, 0, if time == 0 then 0 else 1]
    let o := referenceOutput d.divisor i s
    unless o[3]! == 0 && o[5]! == 0 do throw (IO.userError "False start produced an event")
    s ← checkEdge d i s
    edges := edges+1
  -- Reset on every active TX/RX position, including their closing edges.
  for time in [0:10*d.divisor] do
    let dirty := #[1, time, 0x96, 1, time, 0xa5]
    let clean ← checkEdge d #[1, 1, 0x42, 0] dirty
    unless clean == #[0,0,0,0,0,0] do throw (IO.userError "Reset retained a UART register")
    edges := edges+1
  -- Long arbitrary histories include resets, held offers, noise and malformed startup.
  for seed0 in [0:4] do
    s := #[1, 2^width d-1, 0x81, 3, 2^width d-1, 0x5a]
    let mut seed := seed0+17
    for cycle in [0:2048] do
      seed := (1664525*seed+1013904223)%4294967296
      let i := #[if cycle%173 == 0 then 1 else 0, if cycle%97 < 48 then 1 else 0,
        seed%256, seed/256%2]
      s ← checkEdge d i s
      edges := edges+1
  return edges

/-- Concrete Expr mutations exercise data, timing, reset and raw recovery. -/
def mutated (d : Timing) (mode : Nat) : Circuit Physical.Input (Register d) Physical.Output where
  next r := match r with
    | .txActive => if mode == 0 then .mux (.input reset) (.lit 0)
        (.mux (.reg .txActive) (.inv (.equal (.reg .txCount) (count d (d.frame-2)))) (.input txValid))
      else (circuit d).next .txActive
    | .txByte => if mode == 1 then .mux (.input txValid) (.input txData) ((circuit d).next .txByte)
      else (circuit d).next .txByte
    | .rxPhase => if mode == 2 then .mux (.input reset) (.reg .rxPhase) ((circuit d).next .rxPhase)
      else if mode == 3 then .mux (badStart d) (.reg .rxPhase) ((circuit d).next .rxPhase)
      else (circuit d).next .rxPhase
    | .rxByte => if mode == 4 then WordOps.wordXor ((circuit d).next .rxByte) (.lit 1) else (circuit d).next .rxByte
    | .txCount => (circuit d).next .txCount
    | .rxCount => (circuit d).next .rxCount
  output o := match o with
    | .at ⟨0, _⟩ => if mode == 5 then .mux (.reg .txActive) (.slice 7 1 (by decide) (.reg .txByte)) (.lit 1)
      else (circuit d).output tx
    | .at ⟨2, _⟩ => if mode == 6 then .band (.reg .txActive) (txClosing d)
      else if mode == 7 then .reg .txActive else (circuit d).output txComplete
    | .at ⟨3, _⟩ => if mode == 8 then .band (phase 1) (rxClosing d) else (circuit d).output rxValid
    | .at ⟨5, _⟩ => if mode == 9 then .band (phase 2) (.inv (.input rx)) else (circuit d).output Physical.framingError
    | .at k => (circuit d).output (.at k)

def corruptionControls (d : Timing) : IO Nat := do
  let mut fixtures : Array (Array Nat × Array Nat) := #[]
  for count in [0:2^width d] do
    fixtures := fixtures.push (#[0, 1, 0x69, 0], #[1, count, 0x96, 1, count, 0xa5])
    fixtures := fixtures.push (#[1, 1, 0x42, 0], #[1, count, 0x96, 3, count, 0xa5])
  fixtures := fixtures.push (#[0,0,0,1], #[0,0,0,1,d.divisor/2-1,0])
  fixtures := fixtures.push (#[0,0,0,0], #[0,0,0,2,0,0])
  -- Establish the unchanged circuit on these exact images before any rejection.
  for (i,s) in fixtures do let _ ← checkEdge d i s
  for mode in [0:10] do
    let mut rejected := false
    for (i,s) in fixtures do
      let c := mutated d mode
      let actual := capture (registers d) (c.step (pins i) (raw d s))
      let output := capture outputs (c.observe (pins i) (raw d s))
      if actual != referenceStep d.divisor i s || output != referenceOutput d.divisor i s then
        rejected := true
    unless rejected do throw (IO.userError s!"UART physical fault {mode} was not detected")
  return fixtures.size

elab "#audit_uart_circuit" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Uart." ||
        (name.toString.startsWith "_private.Pinwheel.Hardware.Uart." ) then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Nonstandard axiom {ax} in {name}"
      count := count+1
  if count < 450 then throwError "Incomplete UART circuit audit"
  logInfo m!"UART circuit audit: {count} declarations, standard axioms only."

#audit_uart_circuit

def main : IO Unit := do
  let mut rawEdges := 0
  let mut frameEdges := 0
  let mut raceEdges := 0
  let mut faultFixtures := 0
  for divisor in [4,6,10,32] do
    let some d := Timing.check divisor | throw (IO.userError "Rejected test timing")
    rawEdges := rawEdges + (← rawMatrix d)
    let bytes := if divisor ≤ 6 then List.range 256 else [0,1,0x55,0x80,0x81,0x96,0xa5,0xff]
    for byte in bytes do frameEdges := frameEdges + (← frameCampaign d byte)
    raceEdges := raceEdges + (← races d)
    faultFixtures := faultFixtures + (← corruptionControls d)
  IO.println s!"UART circuit: {rawEdges} raw edges, {frameEdges} frame edges, {raceEdges} race/history edges, {faultFixtures} positive fault fixtures; all 10 Expr mutants rejected at each divisor."

end HardwareUartCircuitTests

def main := HardwareUartCircuitTests.main
