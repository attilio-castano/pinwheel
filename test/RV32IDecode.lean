import Lean
import Pinwheel.Hardware.Processor.RV32I.Decode

open Lean Elab Command Pinwheel.Hardware.Processor.RV32I
namespace RV32IDecodeTests

/-- Stable test-only mnemonic IDs, enumerating all forty base instructions. -/
def branchId : BranchOp → Nat
  | .eq => 4 | .ne => 5 | .lt => 6 | .ge => 7 | .ltu => 8 | .geu => 9
def loadId : LoadOp → Nat
  | .byte => 10 | .half => 11 | .word => 12 | .byteUnsigned => 13 | .halfUnsigned => 14
def storeId : StoreOp → Nat
  | .byte => 15 | .half => 16 | .word => 17
def immediateId : ImmediateOp → Nat
  | .add => 18 | .slt => 19 | .sltu => 20 | .bitXor => 21 | .bitOr => 22 | .bitAnd => 23
def shiftId : ShiftOp → Nat
  | .left => 24 | .rightLogical => 25 | .rightArithmetic => 26
def registerId : RegisterOp → Nat
  | .add => 27 | .sub => 28 | .sll => 29 | .slt => 30 | .sltu => 31
  | .bitXor => 32 | .srl => 33 | .sra => 34 | .bitOr => 35 | .bitAnd => 36

/-- Observations retain every meaningful decoded field; unused fields are zero. -/
def observation (i : Instruction) : Array Nat :=
  let imm := (i.immediate.map BitVec.toNat).getD 0
  match i with
  | .lui rd _ => #[0, rd.toNat, 0, 0, imm, 0, 0, 0]
  | .auipc rd _ => #[1, rd.toNat, 0, 0, imm, 0, 0, 0]
  | .jal rd _ => #[2, rd.toNat, 0, 0, imm, 0, 0, 0]
  | .jalr rd rs1 _ => #[3, rd.toNat, rs1.toNat, 0, imm, 0, 0, 0]
  | .branch op rs1 rs2 _ => #[branchId op, 0, rs1.toNat, rs2.toNat, imm, 0, 0, 0]
  | .load op rd rs1 _ => #[loadId op, rd.toNat, rs1.toNat, 0, imm, 0, 0, 0]
  | .store op rs1 rs2 _ => #[storeId op, 0, rs1.toNat, rs2.toNat, imm, 0, 0, 0]
  | .aluImm op rd rs1 _ => #[immediateId op, rd.toNat, rs1.toNat, 0, imm, 0, 0, 0]
  | .shiftImm op rd rs1 _ => #[shiftId op, rd.toNat, rs1.toNat, 0, imm, 0, 0, 0]
  | .aluReg op rd rs1 rs2 => #[registerId op, rd.toNat, rs1.toNat, rs2.toNat, 0, 0, 0, 0]
  | .fence rd rs1 mode pred succ => #[37, rd.toNat, rs1.toNat, 0, 0, mode.toNat, pred.toNat, succ.toNat]
  | .ecall => #[38, 0, 0, 0, 0, 0, 0, 0]
  | .ebreak => #[39, 0, 0, 0, 0, 0, 0, 0]

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

structure Coverage where
  checked : Nat := 0
  illegal : Nat := 0
  mnemonics : Array Bool := Array.replicate 40 false

def check (word : Nat) (coverage : Coverage) : IO Coverage := do
  unless word < 2^32 do throw (IO.userError "Reference constructor overflowed the instruction word")
  let decoded := decode (BitVec.ofNat 32 word)
  let expected := reference word
  unless decoded.map observation = expected do
    throw (IO.userError s!"Decode mismatch for {word}: actual {decoded.map observation}, reference {expected}")
  match decoded with
  | none => return {coverage with checked := coverage.checked+1, illegal := coverage.illegal+1}
  | some instruction =>
    unless (encode instruction).toNat = word do throw (IO.userError "Decoding discarded significant raw fields")
    return {coverage with
      checked := coverage.checked+1, mnemonics := coverage.mnemonics.set! (observation instruction)[0]! true}

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

def permissiveShift (word : Word) : Option Instruction :=
  if opcode word = 19 ∧ funct3 word = 1 then some (.shiftImm .left (rd word) (rs1 word) (rs2 word))
  else decode word

def permissiveSystem (word : Word) : Option Instruction :=
  if opcode word = 115 then decode (word &&& 0xfff0707f) else decode word

def rejectFenceFields (word : Word) : Option Instruction :=
  if opcode word = 15 ∧ (rd word ≠ 0 ∨ rs1 word ≠ 0 ∨ fenceMode word ≠ 0) then none else decode word

def eraseFenceFields (word : Word) : Option Instruction :=
  (decode word).map fun instruction => match instruction with
    | .fence _ _ _ pred succ => .fence 0 0 0 pred succ
    | other => other

def wrongJump (word : Word) : Option Instruction :=
  (decode word).map fun instruction => match instruction with
    | .jal dest bits => .jal dest (bits ^^^ 1024)
    | other => other

def rejectHint (word : Word) : Option Instruction :=
  if opcode word = 19 ∧ rd word = 0 then none else decode word

def rejectMutation (label : String) (word : Nat) (actual : Option (Array Nat)) : IO Unit := do
  unless actual ≠ reference word do throw (IO.userError s!"Semantic decoder mutation escaped: {label}")

def mutationControls : IO Nat := do
  let illegalShift := rWord 19 1 1 1 2 3
  rejectMutation "RV64/reserved shift upper bits ignored" illegalShift
    ((permissiveShift (BitVec.ofNat 32 illegalShift)).map observation)
  rejectMutation "ECALL nonzero rd/rs1 ignored" 0x000080f3 ((permissiveSystem 0x000080f3).map observation)
  let fence := iWord 15 0 31 17 0xf33
  rejectMutation "required conservative FENCE configurations rejected" fence
    ((rejectFenceFields (BitVec.ofNat 32 fence)).map observation)
  rejectMutation "raw FENCE fields discarded" fence ((eraseFenceFields (BitVec.ofNat 32 fence)).map observation)
  let jump := jWord 7 0x80001
  rejectMutation "J offset bit 11 scattered incorrectly" jump ((wrongJump (BitVec.ofNat 32 jump)).map observation)
  rejectMutation "legal rd=x0 HINT rejected" 0x00000013 ((rejectHint 0x00000013).map observation)
  let sltiu := iWord 19 3 7 9 4095
  rejectMutation "SLTIU immediate zero extended" sltiu
    ((decode (BitVec.ofNat 32 sltiu)).map fun instruction => (observation instruction).set! 4 4095)
  let branch := bWord 0 1 2 2048
  rejectMutation "B offset missing implicit low zero" branch
    ((decode (BitVec.ofNat 32 branch)).map fun instruction =>
      (observation instruction).set! 4 ((bBits (BitVec.ofNat 32 branch)).signExtend 32).toNat)
  let upper := 0x800000b7
  rejectMutation "LUI upper field not shifted" upper
    ((decode (BitVec.ofNat 32 upper)).map fun instruction => (observation instruction).set! 4 0x80000)
  -- Named extension/reserved probes supplement the exhaustive control matrix.
  for word in [0x02000033, 0x02001013, 0x0000001b, 0x00101073, 0x0000100f,
      0x0000002f, 0x00000053, 0x30200073, 0x00000001, 0x000080f3, 0x001000f3] do
    unless (decode (BitVec.ofNat 32 word)).isNone && (reference word).isNone do
      throw (IO.userError s!"Unsupported/strict-system probe incorrectly admitted: {word}")
  return 9

end RV32IDecodeTests

elab "#audit_rv32i_decode" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.RV32I." || name.toString.startsWith "RV32IDecodeTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved RV32I decoder axioms in {name}: {bad}"
  if count < 100 then throwError "Incomplete RV32I decoder audit"
  logInfo m!"RV32I decoder audit: {count} declarations, standard axioms only."

#audit_rv32i_decode

def main : IO Unit := do
  let c ← RV32IDecodeTests.campaign
  let mutations ← RV32IDecodeTests.mutationControls
  IO.println s!"RV32I decoder: {c.checked} independent word checks, {c.illegal} illegal/unsupported, all 40 base instructions; {mutations} semantic mutation controls rejected."
