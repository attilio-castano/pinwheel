import Lean
import Pinwheel.Hardware.Processor.MmioCircuitProofs

open Lean Elab
open Pinwheel.Hardware
open Pinwheel.Hardware.Processor
open MmioInterface MmioCircuit

namespace ProcessorMmioCircuitTests

def pins (xs : Array Nat) : Values Input := fun p => match p with
  | .at k => BitVec.ofNat _ (xs[k.val]?.getD 0)

def registersFrom (xs : Array Nat) : Values Register := fun r => match r with
  | .at k => BitVec.ofNat _ (xs[k.val]?.getD 0)

def capture (descriptor : Interface P) (v : Values P) : Array Nat :=
  Array.ofFn fun k : Fin descriptor.size => (v (descriptor.signal k).2).toNat

/-- Independent natural-number physical oracle. State order is GPIO,timer,
TX active/data,RX valid/data,overrun,framing. Inactive metadata is retained. -/
def cpuReference (i s : Array Nat) : Nat × Nat × Array Nat := Id.run do
  let mut next := s
  let device := i[2]!
  let write := i[3]! == 1
  let word := i[4]!
  let data := i[5]!
  if i[1]! == 0 then return (0, 0, next)
  if device == 0 then
    if word == 0 then return (if write then 3 else 0, if write then 0 else i[6]!, next)
    if word == 1 then
      if write then return (1, 0, next.set! 0 data)
      return (0, s[0]!, next)
    return (2, 0, next)
  if device == 1 then
    if word == 0 then return (if write then 3 else 0, if write then 0 else s[1]!, next)
    return (2, 0, next)
  if device == 2 then
    if word == 0 then
      if write then return (3, 0, next)
      return (0, (1-s[2]!)+2*s[4]!+4*s[6]!+8*s[7]!, next)
    if word == 1 then
      if !write then return (3, 0, next)
      if s[2]! == 1 then return (4, 0, next)
      next := (next.set! 2 1).set! 3 (data%256)
      return (1, 0, next)
    if word == 2 then
      if write then return (3, 0, next)
      if s[4]! == 0 then return (5, 0, next)
      return (0, s[5]!, next.set! 4 0)
    if word == 3 then
      if !write then return (3, 0, next)
      if data / 4 % 2 == 1 then next := next.set! 6 0
      if data / 8 % 2 == 1 then next := next.set! 7 0
      return (1, 0, next)
  return (2, 0, next)

def referenceOutput (i s : Array Nat) : Array Nat :=
  if i[0]! == 1 then #[0, 0, 0, 0, 0, 0, 0] else
    let (code, value, _) := cpuReference i s
    #[1, i[1]!, code, value, s[0]!, s[2]!, if s[2]! == 1 then s[3]! else 0]

def referenceStep (i s : Array Nat) : Array Nat := Id.run do
  if i[0]! == 1 then return #[0, 0, 0, 0, 0, 0, 0, 0]
  let (_, _, current) := cpuReference i s
  let mut next := current.set! 1 ((s[1]!+1)%4294967296)
  if s[2]! == 1 && i[7]! == 1 then next := next.set! 2 0
  if i[8]! == 1 then
    if next[4]! == 0 then next := (next.set! 4 1).set! 5 i[9]!
    else next := next.set! 6 1
  if i[10]! == 1 then next := next.set! 7 1
  return next

def startup (flags seed : Nat) : Array Nat :=
  #[(0x91827364+seed)%4294967296, (0xffffffff-seed)%4294967296,
    flags%2, (0xa5+seed)%256, flags/2%2, (0x80+seed)%256, flags/4%2, flags/8%2]

def checkEdge (i s : Array Nat) : IO (Array Nat) := do
  let raw : Values Register := registersFrom s
  let input : Values Input := pins i
  let next : Values Register := circuit.step input raw
  let actual := capture registers next
  let expected := referenceStep i s
  unless actual == expected && capture outputs (circuit.observe input raw) == referenceOutput i s &&
      capture outputs (circuit.observe input next) == referenceOutput i expected do
    throw (IO.userError s!"Raw MMIO mismatch input{i}, state{s}, expected{expected}, actual{actual}")
  unless view next == MmioInterface.spec.step input (view raw) do
    throw (IO.userError "State projection mismatch")
  unless observedResponse input raw == MmioInterface.response input (view raw) do
    throw (IO.userError "Actual response-pin decoding mismatch")
  if i[0]! == 1 || i[1]! == 0 || i[2]! != 3 then
    unless MmioModel.replay (view raw) (physicalEvents input raw) == some (view next) do
      throw (IO.userError "Admitted actual-response event replay mismatch")
  else
    unless observedResponse input raw == some (.fault .registerHole) do
      throw (IO.userError "Malformed selector did not emit its explicit fault")
  return actual

/-- The projection intentionally forgets inactive TX/RX bytes, while the
physical circuit retains both until capture or reset. -/
def retainedMetadata : IO Unit := do
  let first := #[0x12345678, 42, 0, 0xa5, 0, 0x81, 0, 0]
  let second := (first.set! 3 0x5a).set! 5 0x18
  let a : Values Register := registersFrom first
  let b : Values Register := registersFrom second
  unless view a == view b && capture registers a != capture registers b do
    throw (IO.userError "Inactive metadata example is not a noninjective projection")
  let idle := #[0, 0, 3, 1, 63, 0xffffffff, 0, 0, 0, 0, 0]
  let a' ← checkEdge idle first
  let b' ← checkEdge idle second
  unless a'[3]! == 0xa5 && a'[5]! == 0x81 && b'[3]! == 0x5a && b'[5]! == 0x18 do
    throw (IO.userError "Inactive physical bytes were not retained")
  let reset := idle.set! 0 1
  let a'' ← checkEdge reset a'
  let b'' ← checkEdge reset b'
  unless a'' == #[0,0,0,0,0,0,0,0] && b'' == a'' do
    throw (IO.userError "Reset did not clear every physical register")

def matrix : IO Nat := do
  let mut count := 0
  -- All register-address codes and malformed device3, both directions.
  for flags in [0:16] do
    let s := startup flags flags
    for device in [0:4] do
      for word in [0:64] do
        for write in [0:2] do
          let i := #[0, 1, device, write, word, 0xfedcba98+word, 0x12345678,
            word%2, word/2%2, (0xf0+word)%256, word/4%2]
          let _ ← checkEdge i s
          count := count+1
  -- Complete one-bit-control matrix for the implemented registers and a hole.
  for flags in [0:16] do
    let s := startup flags (flags*7)
    for device in [0:4] do
      for word in [0:5] do
        for write in [0:2] do
          for controls in [0:32] do
            let i := #[controls%2, controls/2%2, device, write, word,
              if flags%2 == 0 then 12 else 0xffffffff, 0x87654321,
              controls/4%2, controls/8%2, 0x5a, controls/16%2]
            let _ ← checkEdge i s
            count := count+1
  return count

def histories : IO Nat := do
  let mut count := 0
  for flags in [0:16] do
    let mut s := startup flags (flags*13)
    let mut seed := 17+flags
    for cycle in [0:512] do
      seed := (1664525*seed+1013904223)%4294967296
      let i := #[if cycle%61 == 0 then 1 else 0, if cycle%7 == 0 then 0 else 1,
        seed%4, seed/4%2, seed/8%6, seed, (seed+29)%4294967296,
        seed/48%2, seed/96%2, seed%256, seed/192%2]
      s ← checkEdge i s
      count := count+1
  return count

/-- These alter actual Expr endpoints, rather than changing an expected value. -/
def mutated (mode : Nat) : Circuit Input Register Output where
  next r := match r with
    | .at ⟨0, _⟩ => if mode == 0 then
        .mux (.input reset) (.lit 0) (.mux (.input write) (.input data) (.reg gpio))
      else if mode == 5 then .reg gpio else circuit.next gpio
    | .at ⟨1, _⟩ => if mode == 1 then .reg timer else circuit.next timer
    | .at ⟨2, _⟩ => if mode == 2 then
        .mux (.input txComplete) (.lit 0) (circuit.next txActiveReg) else circuit.next txActiveReg
    | .at ⟨5, _⟩ => if mode == 3 then
        .mux (.input reset) (.lit 0)
          (.mux (.band (.input rxValid) (.inv (.reg rxValidReg))) (.input rxData) (.reg rxDataReg))
      else circuit.next rxDataReg
    | .at ⟨6, _⟩ => if mode == 4 then
        .mux clearErrors (.lit 0) (circuit.next overrun) else circuit.next overrun
    | .at k => circuit.next (.at k)
  output o := match o with
    | .at ⟨1, _⟩ => if mode == 8 then .input requestValid else circuit.output responseValid
    | .at ⟨2, _⟩ => if mode == 6 then .lit 0 else circuit.output responseCode
    | .at ⟨6, _⟩ => if mode == 7 then .reg txDataReg else circuit.output txData
    | .at k => circuit.output (.at k)

def controls : IO Nat := do
  let dirty := #[0x12345678, 0xffffffff, 1, 0xa5, 1, 0x80, 1, 1]
  let idle := (dirty.set! 2 0).set! 4 0
  let fixtures : Array (Nat × Array Nat × Array Nat) := #[
    (0, #[0,1,0,1,0,0xabcdef,0,0,0,0,0], dirty),
    (1, #[0,0,0,0,0,0,0,0,0,0,0], dirty),
    (2, #[0,1,2,1,1,0x12345642,0,1,0,0,0], idle),
    (3, #[0,1,2,0,2,0,0,0,1,0x11,0], dirty),
    (4, #[0,1,2,1,3,12,0,0,1,0x22,1], dirty),
    (5, #[1,1,2,1,3,12,0,1,1,0x33,1], dirty),
    (6, #[0,1,3,0,0,0,0xabcdef,0,0,0,0], dirty),
    (7, #[0,0,0,0,0,0,0,0,0,0,0], idle),
    (8, #[1,1,0,0,0,0,0xabcdef,0,0,0,0], dirty)]
  for (mode, i, s) in fixtures do
    let _ ← checkEdge i s
    let bad := mutated mode
    let registers := capture MmioCircuit.registers (bad.step (pins i) (registersFrom s))
    let outputs := capture MmioInterface.outputs (bad.observe (pins i) (registersFrom s))
    unless registers != referenceStep i s || outputs != referenceOutput i s do
      throw (IO.userError s!"Inactive or undetected structural mutation{mode}")
  return fixtures.size

end ProcessorMmioCircuitTests

open Lean.Elab.Command
elab "#audit_mmio_circuit" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.Mmio" ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.Mmio" then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved MMIO axioms in {name}: {bad}"
  if count < 400 then throwError "Incomplete MMIO circuit audit"
  logInfo m!"MMIO circuit audit: {count} declarations, standard axioms only."

#audit_mmio_circuit

def main : IO Unit := do
  ProcessorMmioCircuitTests.retainedMetadata
  let matrix ← ProcessorMmioCircuitTests.matrix
  let histories ← ProcessorMmioCircuitTests.histories
  let controls ← ProcessorMmioCircuitTests.controls
  IO.println s!"MMIO circuit: {matrix} raw-state/control edges, {histories} history edges, all 8 registers and pre/post 7 outputs, actual response/event checks, inactive-byte retention/reset, {controls} actual Expr corruptions rejected."
