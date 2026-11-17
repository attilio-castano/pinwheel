import Lean
import Pinwheel.Hardware.Memory.ByteAdapterLoader

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Memory
open ByteAdapterLoader

namespace MemoryByteAdapterLoaderTests

def input (a : Nat) (values : Array Nat) : Values (Input a) := fun {b} p =>
  BitVec.ofNat b values[((inputs a).position p).val]!
def bank (a : Nat) (values : Array Nat) : Values (Register a) := fun {b} p =>
  BitVec.ofNat b values[((registers a).position p).val]!
def capture (d : Interface P) (v : Values P) : Array Nat := d.ports.map fun ⟨_,p⟩ => (v p).toNat

/-- Integer-array reference for word-sized CPU traffic and the loader override.
The CPU metadata and Q are tracked independently of the production step. -/
def reference (a : Nat) (i s : Array Nat) : Array Nat := Id.run do
  let depth := 2^a
  let mut next := s
  if i[0]! == 1 || i[9]! == 1 then next := next.set! (depth+7) 0
  else if s[depth+7]! == 0 then
    if i[1]! == 1 then
      next := next.set! depth s[i[5]!]!
      for (index,value) in [(1,i[2]!), (2,i[3]!), (3,i[4]!), (4,i[5]!), (5,i[6]!), (6,i[7]!), (7,1)] do
        next := next.set! (depth+index) value
  else if i[8]! == 1 then
    next := next.set! (depth+7) 0
    if s[depth+1]! == 1 then next := next.set! s[depth+4]! s[depth+6]!
  if i[0]! == 0 && i[9]! == 1 && i[10]! == 1 then next := next.set! i[11]! i[12]!
  return next

def outputReference (a : Nat) (i s : Array Nat) : Array Nat :=
  let blocked := i[0]! == 1 || i[9]! == 1
  let pending := s[2^a+7]! == 1
  let write := s[2^a+1]! == 1
  #[(!blocked && !pending).toNat,(!blocked && pending).toNat,
    if !blocked && pending && write then 1 else 0,
    if !blocked && pending && !write then s[2^a]! else 0,
    (i[0]! == 0 && i[9]! == 1).toNat]

def initial (a pending write target : Nat) : Array Nat :=
  (Array.range (2^a) |>.map fun k => (0x12345678+65793*k)%2^32) ++
    #[0x87654321,write,1,2,target,0,0xfeedface,pending]

def check (a : Nat) (i s : Array Nat) : IO Unit := do
  let pins : Values (Input a) := input a i
  let raw : Values (Register a) := bank a s
  let next := reference a i s
  unless capture (registers a) ((circuit a).step pins raw) == next &&
      capture outputs ((circuit a).observe pins raw) == outputReference a i s &&
      capture outputs ((circuit a).observe pins (bank a next)) == outputReference a i next do
    throw (IO.userError s!"Loader mismatch a{a} input{i} raw{s}")

def campaign : IO Nat := do
  let mut checks := 0
  for a in [:4] do
    for reset in [:2] do
      for mode in [:2] do
        for valid in [:2] do
          for cpuValid in [:2] do
            for cpuWrite in [:2] do
              for pending in [:2] do
                for oldWrite in [:2] do
                  for ready in [:2] do
                    for loadAddress in [:2^a] do
                      for oldAddress in [0,2^a-1] do
                        let pins := #[reset,cpuValid,cpuWrite,0,2,(loadAddress+1)%2^a,0,0xa5a5ff80,ready,
                          mode,valid,loadAddress,0x80ff7f01]
                        check a pins (initial a pending oldWrite oldAddress)
                        checks := checks+1
  return checks

def mutantNext (mode : Nat) : {b : Nat} → Register 1 b → Expr (Input 1) (Register 1) b
  | _, .left (.left (.word k)) =>
      if mode == 0 then .mux (.input valid) (.input data) ((circuit 1).next (.left (CommandFlops.word k)))
      else if mode == 1 then .mux accepted (.input data) ((circuit 1).next (.left (CommandFlops.word k)))
      else (circuit 1).next (.left (CommandFlops.word k))
  | _, .left (.right .q) => if mode == 2 then .mux accepted (.input data) (.reg (.left CommandFlops.q))
      else (circuit 1).next (.left CommandFlops.q)
  | _, .right (.at ⟨6,h⟩) => if mode == 3 then .reg (.right (.at ⟨6,h⟩))
      else (circuit 1).next (.right (.at ⟨6,h⟩))
  | _, .right (.at k) => (circuit 1).next (.right (.at k))

def mutants (mode : Nat) : Circuit (Input 1) (Register 1) Output where
  next := mutantNext mode
  output := fun {b} o => match b,o with
    | _, .left (.at ⟨1,h⟩) => if mode == 4 then .reg ByteAdapterCircuit.pending
        else (circuit 1).output (.left (.at ⟨1,h⟩))
    | _, .left o => (circuit 1).output (.left o)
    | _, .right o => (circuit 1).output (.right o)

def controls : IO Nat := do
  for (mode,pins) in [(0,#[1,1,1,0,2,0,0,0x33,1,1,1,0,0xa5]),
      (1,#[0,1,1,0,2,0,0,0x33,1,1,1,0,0xa5]),
      (2,#[0,1,1,0,2,0,0,0x33,1,1,1,0,0xa5]),
      (3,#[0,1,1,0,2,0,0,0x33,1,1,1,0,0xa5]),
      (4,#[0,1,1,0,2,0,0,0x33,1,1,1,0,0xa5])] do
    let raw := initial 1 1 1 0
    check 1 pins raw
    let i : Values (Input 1) := input 1 pins
    let s : Values (Register 1) := bank 1 raw
    unless capture (registers 1) ((mutants mode).step i s) != reference 1 pins raw ||
        capture outputs ((mutants mode).observe i s) != outputReference 1 pins raw do
      throw (IO.userError s!"Loader Expr mutant escaped {mode}")
  return 5

end MemoryByteAdapterLoaderTests

elab "#audit_byte_loader" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name,_) in env.constants.toList do
    if ["Pinwheel.Hardware.Memory.ByteAdapterLoader.","_private.Pinwheel.Hardware.Memory.ByteAdapterLoader.",
        "MemoryByteAdapterLoaderTests."].any (fun pfx => name.toString.startsWith pfx) then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved loader axiom {name}: {bad}"
  if count < 40 then throwError "Incomplete loader audit"
  logInfo m!"Byte loader audit: {count} declarations, standard axioms only."

#audit_byte_loader

def main : IO Unit := do
  let cases ← MemoryByteAdapterLoaderTests.campaign
  let mutants ← MemoryByteAdapterLoaderTests.controls
  IO.println s!"Byte loader: {cases} integer-array raw edges, all registers and pre/post outputs; {mutants} actual Expr faults rejected."
