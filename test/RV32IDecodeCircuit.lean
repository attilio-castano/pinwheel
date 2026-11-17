import Lean
import Pinwheel.Hardware.Processor.RV32I.DecodeCircuit

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Processor.RV32I
open DecodeCircuit
namespace RV32IDecodeCircuitTests

/-- Retained independent integer oracle from RV32IDecode.lean. Its arithmetic
field extraction/encoding table does not call the production decoder, Kind map,
format predicates, immediate helpers, or expression constructors. -/
def field (word start width : Nat) : Nat := word / 2^start % 2^width
def sext (raw width : Nat) : Nat := if raw < 2^(width-1) then raw else raw + 2^32 - 2^width

/-- Independent Nat division/remainder decoder from the pinned chapter 36
encoding table. No production decoder, field helper, opcode map, immediate
getter, instruction encoder, or format predicate is used to compute expectations. -/
def reference (word : Nat) : Option (Array Nat) := Id.run do
  let op := word%128
  let d := field word 7 5
  let a := field word 15 5
  let b := field word 20 5
  let f := field word 12 3
  let h := field word 25 7
  let i := sext (field word 20 12) 12
  match op with
  | 55 => return some #[0, d, 0, 0, word/4096*4096, 0, 0, 0]
  | 23 => return some #[1, d, 0, 0, word/4096*4096, 0, 0, 0]
  | 111 =>
    let j := field word 31 1 * 2^20 + field word 12 8 * 2^12 + field word 20 1 * 2^11 + field word 21 10 * 2
    return some #[2, d, 0, 0, sext j 21, 0, 0, 0]
  | 103 => return if f = 0 then some #[3, d, a, 0, i, 0, 0, 0] else none
  | 99 =>
    let some id := (match f with | 0 => some 4 | 1 => some 5 | 4 => some 6 | 5 => some 7 | 6 => some 8 | 7 => some 9 | _ => none) | return none
    let branch := field word 31 1 * 4096 + field word 7 1 * 2048 + field word 25 6 * 32 + field word 8 4 * 2
    return some #[id, 0, a, b, sext branch 13, 0, 0, 0]
  | 3 =>
    let some id := (match f with | 0 => some 10 | 1 => some 11 | 2 => some 12 | 4 => some 13 | 5 => some 14 | _ => none) | return none
    return some #[id, d, a, 0, i, 0, 0, 0]
  | 35 =>
    let some id := (match f with | 0 => some 15 | 1 => some 16 | 2 => some 17 | _ => none) | return none
    return some #[id, 0, a, b, sext (h*32+d) 12, 0, 0, 0]
  | 19 =>
    match f with
    | 0 => return some #[18, d, a, 0, i, 0, 0, 0]
    | 2 => return some #[19, d, a, 0, i, 0, 0, 0]
    | 3 => return some #[20, d, a, 0, i, 0, 0, 0]
    | 4 => return some #[21, d, a, 0, i, 0, 0, 0]
    | 6 => return some #[22, d, a, 0, i, 0, 0, 0]
    | 7 => return some #[23, d, a, 0, i, 0, 0, 0]
    | 1 => return if h = 0 then some #[24, d, a, 0, b, 0, 0, 0] else none
    | 5 => return if h = 0 then some #[25, d, a, 0, b, 0, 0, 0]
      else if h = 32 then some #[26, d, a, 0, b, 0, 0, 0] else none
    | _ => return none
  | 51 =>
    let some id := (match h, f with
      | 0, 0 => some 27 | 32, 0 => some 28 | 0, 1 => some 29 | 0, 2 => some 30
      | 0, 3 => some 31 | 0, 4 => some 32 | 0, 5 => some 33 | 32, 5 => some 34
      | 0, 6 => some 35 | 0, 7 => some 36 | _, _ => none)
      | return none
    return some #[id, d, a, b, 0, 0, 0, 0]
  | 15 => return if f = 0 then some #[37, d, a, 0, 0, field word 28 4, field word 24 4, field word 20 4] else none
  | 115 => return if word = 115 then some #[38, 0, 0, 0, 0, 0, 0, 0]
    else if word = 1048691 then some #[39, 0, 0, 0, 0, 0, 0, 0] else none
  | _ => return none

/-- Independently assembled arithmetic instruction formats. -/
def rWord (op f high d a b : Nat) : Nat := high*2^25+b*2^20+a*2^15+f*2^12+d*2^7+op
def iWord (op f d a imm : Nat) : Nat := imm*2^20+a*2^15+f*2^12+d*2^7+op
def sWord (f a b imm : Nat) : Nat := (imm/32)*2^25+b*2^20+a*2^15+f*2^12+(imm%32)*2^7+35
def bWord (f a b offset : Nat) : Nat :=
  (offset/2048)*2^31 + (offset/16%64)*2^25 + b*2^20+a*2^15+f*2^12+(offset%16)*2^8+(offset/1024%2)*2^7+99
def jWord (d offset : Nat) : Nat :=
  (offset/2^19)*2^31+(offset%1024)*2^21+(offset/1024%2)*2^20+(offset/2048%256)*2^12+d*128+111


def expectedPins (word : Nat) : Array Nat :=
  match reference word with
  | none => Array.replicate 9 0
  | some fields => #[1] ++ fields.set! 0 (fields[0]!+1)

def inputValues (word : Word) : Values Input := fun p => match p with | .instruction => word
def noRegisters : Values NoRegisters := fun p => nomatch p

def expressions : Array (Sigma fun b => Expr Input NoRegisters b) :=
  outputs.ports.map fun ⟨b, field⟩ => ⟨b, circuit.output field⟩

def actual (word : Word) : Array Nat :=
  expressions.map fun ⟨_, expr⟩ => (expr.eval (inputValues word) noRegisters).toNat

structure Coverage where
  checked : Nat := 0
  illegal : Nat := 0
  mnemonics : Array Bool := Array.replicate 40 false

def check (word : Nat) (coverage : Coverage) : IO Coverage := do
  unless word < 2^32 do throw (IO.userError "Oracle word overflow")
  let expected := expectedPins word
  let observed := actual (BitVec.ofNat 32 word)
  unless observed = expected do throw (IO.userError s!"Structural decoder mismatch {word}: {observed} != {expected}")
  if expected[0]! = 0 then
    return {coverage with checked := coverage.checked+1, illegal := coverage.illegal+1}
  else return {coverage with checked := coverage.checked+1, mnemonics := coverage.mnemonics.set! (expected[1]!-1) true}

def campaign : IO Coverage := do
  let mut c : Coverage := {}
  -- Exhaust every opcode/funct3/funct7 combination, with independently varying operands.
  for op in [:128] do
    for f in [:8] do
      for high in [:128] do
        c ← check (rWord op f high ((op+high)%32) ((high*7+f)%32) ((op*3+f*5)%32)) c
  -- Every I/S/B immediate bit pattern, all respective operation kinds.
  for imm in [:4096] do
    let d := imm%32
    let a := imm/32%32
    let b := (imm*13+17)%32
    for f in [0, 2, 3, 4, 6, 7] do c ← check (iWord 19 f d a imm) c
    for f in [0, 1, 2, 4, 5] do c ← check (iWord 3 f d a imm) c
    c ← check (iWord 103 0 d a imm) c
    for f in [0, 1, 2] do c ← check (sWord f a b imm) c
    for f in [0, 1, 4, 5, 6, 7] do c ← check (bWord f a b imm) c
  -- All fence mode/pred/succ settings, including reserved settings and nonzero unused registers.
  for fields in [:4096] do
    for d in [0, 1, 17, 31] do c ← check (iWord 15 0 d ((fields+d)%32) fields) c
  -- Signed boundaries, each scattered J bit, and modular U values.
  for bits in [0, 1, 1023, 1024, 2047, 2048, 2^19-1, 2^19, 2^20-1] do
    for d in [0, 1, 31] do
      c ← check (jWord d bits) c
      c ← check (bits*4096+d*128+55) c
      c ← check (bits*4096+d*128+23) c
  for k in [:20] do c ← check (jWord (k%32) (2^k)) c
  let mut seed : Nat := 0x72763332
  for _ in [:65536] do
    seed := (1664525*seed+1013904223)%2^32
    c ← check seed c
    c ← check (jWord (seed%32) (seed/32%2^20)) c
  -- ECALL/EBREAK require all other fields zero; neighboring SYSTEM encodings must not be assumed legal.
  for system in [115, 1048691] do
    c ← check system c
    for bit in [:32] do c ← check (Nat.xor system (2^bit)) c
  -- Every one-bit neighbor of independent legal-format fixtures, including legal neighbors.
  for fixture in [:512] do
    let base := if fixture%2 = 0 then bWord #[0, 1, 4, 5, 6, 7][fixture%6]! (fixture%32) (fixture/32%32) (fixture*7%4096)
      else rWord 51 (fixture%8) 0 (fixture%32) (fixture/16%32) (fixture/32%32)
    for bit in [:32] do c ← check (Nat.xor base (2^bit)) c
  unless c.mnemonics.all id do throw (IO.userError "Not all forty base instructions were exercised")
  unless c.illegal > 100000 do throw (IO.userError "Insufficient illegal/extension encoding coverage")
  return c


/-- Every mutation replaces an actual expression endpoint. Expectations stay
fixed and the unchanged expression bundle must pass each same witness first. -/
def mutant (mode : Nat) : Bundle Input NoRegisters := fun field =>
  let word : Expr Input NoRegisters 32 := .input .instruction
  match field with
  | .valid =>
      if mode = 0 then .lit 1
      else if mode = 5 then .band (bundle word .valid) (.inv (.zero (.slice 7 5 (by decide) word)))
      else if mode = 6 then .band (bundle word .valid) (.zero (.slice 28 4 (by decide) word))
      else if mode = 7 then .mux (.equal (.slice 0 7 (by decide) word) (.lit 115)) (.lit 1) (bundle word .valid)
      else if mode = 8 then .mux (.band (.equal (.slice 0 7 (by decide) word) (.lit 19))
        (.equal (.slice 12 3 (by decide) word) (.lit 1))) (.lit 1) (bundle word .valid)
      else (bundle word .valid)
  | .tag => if mode = 9 then .mux (recognize word .sub) (.lit Kind.add.tag) (bundle word .tag) else (bundle word .tag)
  | .rd => if mode = 4 then .slice 7 5 (by decide) word else (bundle word .rd)
  | .rs1 => if mode = 10 then .slice 20 5 (by decide) word
      else if mode = 11 then .mux (recognize word .fence) (.lit 0) (bundle word .rs1) else (bundle word .rs1)
  | .rs2 => (bundle word .rs2)
  | .immediate =>
      if mode = 1 then .concat (.lit (0#20)) (.slice 20 12 (by decide) word)
      else if mode = 2 then WordOps.wordXor (bundle word .immediate) (.lit 2048)
      else if mode = 3 then WordOps.shiftRight 1 (bundle word .immediate)
      else if mode = 12 then WordOps.shiftRight 12 (bundle word .immediate) else (bundle word .immediate)
  | .fenceMode => if mode = 13 then .lit 0 else (bundle word .fenceMode)
  | .fencePredecessor => (bundle word .fencePredecessor)
  | .fenceSuccessor => (bundle word .fenceSuccessor)

def mutationControls : IO Nat := do
  let fence := iWord 15 0 31 17 0xf33
  let probes := #[(0, 0x02000033), (1, iWord 19 3 7 9 4095), (2, jWord 7 0x80001),
    (3, bWord 0 1 2 2048), (4, 0x020000b3), (5, 0x13), (6, fence),
    (7, 0x000080f3), (8, rWord 19 1 1 1 2 3), (9, rWord 51 0 32 1 2 3),
    (10, iWord 19 0 7 9 3), (11, fence), (12, 0x800000b7), (13, fence)]
  for (mode, word) in probes do
    let _ ← check word {}
    let values := outputs.ports.map fun ⟨_, field⟩ =>
      ((mutant mode field).eval (inputValues (BitVec.ofNat 32 word)) noRegisters).toNat
    unless values ≠ expectedPins word do throw (IO.userError s!"Inactive/undetected expression corruption {mode}")
  return probes.size

inductive HalfInput : Nat → Type where | low : HalfInput 16
inductive HalfRegister : Nat → Type where | high : HalfRegister 16

def replacement : {b : Nat} → Input b → Expr HalfInput HalfRegister b
  | _, .instruction => .concat (.reg HalfRegister.high) (.input HalfInput.low)

def replaceRegister : {b : Nat} → NoRegisters b → Expr HalfInput HalfRegister b := fun r => nomatch r

def boundBundle : Bundle HalfInput HalfRegister := DecodeCircuit.bind (bundle (R := NoRegisters) (.input Input.instruction)) replacement replaceRegister

def bindChecks : IO Nat := do
  for k in [:512] do
    let high : Nat := (k*1337+0x8000)%65536
    let low : Nat := (k*17+0x13)%65536
    let iv : Values HalfInput := fun p => match p with | .low => BitVec.ofNat 16 low
    let rv : Values HalfRegister := fun p => match p with | .high => BitVec.ofNat 16 high
    let values := outputs.ports.map fun ⟨_, field⟩ => ((boundBundle field).eval iv rv).toNat
    unless values = expectedPins (high*65536+low) do throw (IO.userError "Bound expression bundle mismatch")
  return 512

end RV32IDecodeCircuitTests

elab "#audit_rv32i_decode_circuit" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.RV32I.DecodeCircuit." ||
        name.toString.startsWith "RV32IDecodeCircuitTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved structural decoder axioms in {name}: {bad}"
  if count < 100 then throwError "Incomplete structural decoder audit"
  logInfo m!"RV32I structural decoder audit: {count} declarations, standard axioms only."

#audit_rv32i_decode_circuit

def main : IO Unit := do
  let c ← RV32IDecodeCircuitTests.campaign
  let bound ← RV32IDecodeCircuitTests.bindChecks
  let mutations ← RV32IDecodeCircuitTests.mutationControls
  IO.println s!"RV32I structural decoder: {c.checked} independent word checks, {c.illegal} illegal/unsupported, all 40 tags and all 9 fields; {bound} bound-input/register checks; {mutations} actual Expr corruption controls rejected."
