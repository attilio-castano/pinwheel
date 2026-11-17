import Pinwheel.Hardware.Memory.TransferCircuitProofs

open Pinwheel.Hardware
open Pinwheel.Hardware.Memory
open Pinwheel.Hardware.Memory.TransferInterface

namespace MemoryTransferCircuitTests

def transform (wi wo : Nat) : Stream.Map wi wo :=
  ⟨.slice 0 wo (by omega) (.concat (.lit (0 : BitVec wo)) (.inv (.input .data))),
    fun value => ((0 : BitVec wo) ++ ~~~value).extractLsb' 0 wo, fun _ => rfl⟩

structure Oracle where
  phase : Nat
  sourceBase : Nat
  destinationBase : Nat
  length : Nat
  index : Nat
  done : Bool
  error : Bool
  deriving BEq, Repr

def registers (a : Nat) (s : Oracle) : Values (TransferCircuit.Register a)
  | _, .phase => BitVec.ofNat 2 s.phase
  | _, .sourceBase => BitVec.ofNat a s.sourceBase
  | _, .destinationBase => BitVec.ofNat a s.destinationBase
  | _, .length => BitVec.ofNat (a+1) s.length
  | _, .index => BitVec.ofNat (a+1) s.index
  | _, .done => BitVec.ofBool s.done
  | _, .error => BitVec.ofBool s.error

def capture (s : Values (TransferCircuit.Register a)) : Oracle :=
  ⟨(s .phase).toNat, (s .sourceBase).toNat, (s .destinationBase).toNat,
    (s .length).toNat, (s .index).toNat, s .done == 1, s .error == 1⟩

/-- This integer oracle includes malformed raw states, outside the logical
refinement invariant. It does not use the model decoder or transition. -/
def advance (a : Nat) (p : Pins a wi) (s : Oracle) : Oracle := Id.run do
  if p.reset == 1 then return ⟨0, 0, 0, 0, 0, false, false⟩
  if s.phase == 3 then return ⟨0, 0, 0, 0, 0, false, true⟩
  let clear := { s with done := false, error := false }
  if s.phase == 0 then
    if p.startValid == 0 then return clear
    if p.length.toNat > 2^a-p.sourceBase.toNat ||
        p.length.toNat > 2^a-p.destinationBase.toNat then
      return ⟨0, 0, 0, 0, 0, false, true⟩
    return ⟨if p.length.toNat == 0 then 0 else 1, p.sourceBase.toNat,
      p.destinationBase.toNat, p.length.toNat, 0, p.length.toNat == 0, false⟩
  if s.phase == 1 then
    return { clear with phase := if p.sourceRequestReady == 1 then 2 else 1 }
  if p.sourceResponseValid == 1 && p.destinationRequestReady == 1 then
    let next := (s.index+1) % 2^(a+1)
    return { clear with
      phase := if next < s.length then 1 else 0
      index := next
      done := !(next < s.length) }
  return clear

def expectedOutput (a wi wo : Nat) (p : Pins a wi) (s : Oracle) : Array Nat :=
  if p.reset == 1 || s.phase == 3 then #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  else
    let src := s.phase == 1
    let dst := s.phase == 2 && p.sourceResponseValid == 1
    #[if s.phase == 0 then 1 else 0, if s.phase != 0 then 1 else 0,
      if s.done then 1 else 0, if s.error then 1 else 0, if src then 1 else 0,
      if src then (s.sourceBase+s.index) % 2^a else 0,
      if s.phase == 2 && p.destinationRequestReady == 1 then 1 else 0,
      if dst then 1 else 0, if dst then (s.destinationBase+s.index) % 2^a else 0,
      if dst then (2^wi-1-p.sourceResponseData.toNat) % 2^wo else 0, 0]

def captureOutput (a wo : Nat) (o : Values (Output a wo)) : Array Nat :=
  (outputs a wo).ports.map fun p => (o p.2).toNat

def checkEdge (a wi wo : Nat) (label : String) (p : Pins a wi) (s : Oracle) : IO Oracle := do
  let c := TransferCircuit.circuit (a := a) (transform wi wo)
  let actualBefore := captureOutput a wo (c.observe p.values (registers a s))
  unless actualBefore == expectedOutput a wi wo p s do
    throw (IO.userError s!"{label}: pre-edge outputs differ: {actualBefore}")
  let expected := advance a p s
  let actual := capture (c.step p.values (registers a s))
  unless actual == expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  let actualAfter := captureOutput a wo (c.observe p.values (registers a actual))
  unless actualAfter == expectedOutput a wi wo p expected do
    throw (IO.userError s!"{label}: post-edge outputs differ: {actualAfter}")
  return actual

def checkDescriptors (a wi wo : Nat) : IO Unit := do
  unless (inputs a wi).ports.map (fun p => p.1) == #[1, 1, a, a, a+1, 1, 1, wi, 1] &&
      (outputs a wo).ports.map (fun p => p.1) == #[1, 1, 1, 1, 1, a, 1, 1, a, wo, 1] &&
      (TransferCircuit.registers a).ports.map (fun p => p.1) == #[2, a, a, a+1, a+1, 1, 1] do
    throw (IO.userError "wrong complete descriptor width/order")

def seeded (a seed : Nat) : Oracle :=
  ⟨seed % 4, (seed / 4) % 2^a, (seed / (4*2^a)) % 2^a,
    (seed / (4*2^(2*a))) % 2^(a+1), (seed / (8*2^(3*a))) % 2^(a+1),
    seed / (16*2^(4*a)) % 2 == 1, seed / (32*2^(4*a)) % 2 == 1⟩

/-- Address/data width zero is a meaningful Lean semantics boundary even
though the separately tested HDL profile requires positive physical widths. -/
def zeroWidth : IO Nat := do
  checkDescriptors 0 0 0
  let mut count := 0
  for state in [0:64] do
    for bits in [0:64] do
      let p : Pins 0 0 := ⟨BitVec.ofNat 1 bits, BitVec.ofNat 1 (bits/2), 0, 0,
        BitVec.ofNat 1 (bits/4), BitVec.ofNat 1 (bits/8), BitVec.ofNat 1 (bits/16), 0,
        BitVec.ofNat 1 (bits/32)⟩
      let _ ← checkEdge 0 0 0 s!"zero width state{state}/input{bits}" p (seeded 0 state)
      count := count+1
  return count

/-- Exhaustive command range/admission and handshake pins across each raw
phase, with arbitrary stored fields and sticky status inputs. -/
def small : IO Nat := do
  checkDescriptors 1 1 1
  let mut count := 0
  for state in [0:16] do
    let s := seeded 1 ((state*67) % 1024)
    for control in [0:32] do
      for source in [0:2] do
        for destination in [0:2] do
          for length in [0:4] do
            for data in [0:2] do
              let p : Pins 1 1 := ⟨BitVec.ofNat 1 control, BitVec.ofNat 1 (control/2),
                BitVec.ofNat 1 source, BitVec.ofNat 1 destination, BitVec.ofNat 2 length,
                BitVec.ofNat 1 (control/4), BitVec.ofNat 1 (control/8), BitVec.ofNat 1 data,
                BitVec.ofNat 1 (control/16)⟩
              let _ ← checkEdge 1 1 1 s!"small state{state}/input{count}" p s
              count := count+1
  return count

def mixed (a wi wo : Nat) : IO Nat := do
  checkDescriptors a wi wo
  let mut s : Oracle := ⟨3, 2^a-1, 2^a-1, 2^(a+1)-1, 2^(a+1)-1, true, true⟩
  for cycle in [0:280] do
    let p : Pins a wi := ⟨BitVec.ofBool (cycle % 71 == 17), BitVec.ofBool (cycle % 4 != 3),
      BitVec.ofNat a (cycle / 13), BitVec.ofNat a (cycle / 19),
      BitVec.ofNat (a+1) (cycle / 7), BitVec.ofBool (cycle % 5 > 1),
      BitVec.ofBool (cycle % 7 != 0), BitVec.ofNat wi (cycle*43+13),
      BitVec.ofBool (cycle % 13 > 5)⟩
    s ← checkEdge a wi wo s!"mixed a{a}/{wi}/{wo} cycle{cycle}" p s
  return 280

end MemoryTransferCircuitTests

def main : IO Unit := do
  let boundary ← MemoryTransferCircuitTests.zeroWidth
  let small ← MemoryTransferCircuitTests.small
  let mut mixed := 0
  for (a, wi, wo) in [(2, 8, 8), (3, 8, 4), (2, 4, 17)] do
    mixed := mixed + (← MemoryTransferCircuitTests.mixed a wi wo)
  IO.println s!"Memory transfer circuit: {boundary} exhaustive zero-width raw edges, {small} small range/handshake edges, {mixed} mixed-width trace edges; every register and pre/post output agree."
