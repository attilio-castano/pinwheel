import Pinwheel.Hardware.Processor.RV32I.Instruction

/-! RV32I 2.1 decoding against the official pinned release 20260120:
§§2.2–2.3 immediate formats, §2.4 shifts/computation, §§2.5–2.6 control/memory,
§2.7 FENCE (printed pp35–36), §2.8 strict ECALL/EBREAK, §2.9 HINTs, and
chapter 36 instruction listings (printed pp585–586).

`none` is this project's illegal-or-unsupported policy, not a claim that the
ISA mandates traps for every reserved encoding. Extensions (M/C/Zicsr/Zifencei,
etc.) are not decoded here. Legal computational rd=x0 HINT encodings remain
their base instructions; all FENCE fm/rd/rs1/pred/succ fields are admitted as
required by §2.7, without claiming that reserved configurations are standard
software encodings. FENCE.TSO/PAUSE retain their raw FENCE representation.
-/
namespace Pinwheel.Hardware.Processor.RV32I

def opcode (word : Word) : BitVec 7 := word.extractLsb' 0 7
def rd (word : Word) : Register := word.extractLsb' 7 5
def funct3 (word : Word) : BitVec 3 := word.extractLsb' 12 3
def rs1 (word : Word) : Register := word.extractLsb' 15 5
def rs2 (word : Word) : Register := word.extractLsb' 20 5
def funct7 (word : Word) : BitVec 7 := word.extractLsb' 25 7
def iBits (word : Word) : BitVec 12 := word.extractLsb' 20 12
def sBits (word : Word) : BitVec 12 := word.extractLsb' 25 7 ++ word.extractLsb' 7 5
def bBits (word : Word) : BitVec 12 :=
  word.extractLsb' 31 1 ++ word.extractLsb' 7 1 ++ word.extractLsb' 25 6 ++ word.extractLsb' 8 4
def jBits (word : Word) : BitVec 20 :=
  word.extractLsb' 31 1 ++ word.extractLsb' 12 8 ++ word.extractLsb' 20 1 ++ word.extractLsb' 21 10
def uBits (word : Word) : BitVec 20 := word.extractLsb' 12 20
def fenceMode (word : Word) : BitVec 4 := word.extractLsb' 28 4
def fencePredecessor (word : Word) : BitVec 4 := word.extractLsb' 24 4
def fenceSuccessor (word : Word) : BitVec 4 := word.extractLsb' 20 4

def BranchOp.code : BranchOp → BitVec 3
  | .eq => 0 | .ne => 1 | .lt => 4 | .ge => 5 | .ltu => 6 | .geu => 7
def LoadOp.code : LoadOp → BitVec 3
  | .byte => 0 | .half => 1 | .word => 2 | .byteUnsigned => 4 | .halfUnsigned => 5
def StoreOp.code : StoreOp → BitVec 3
  | .byte => 0 | .half => 1 | .word => 2
def ImmediateOp.code : ImmediateOp → BitVec 3
  | .add => 0 | .slt => 2 | .sltu => 3 | .bitXor => 4 | .bitOr => 6 | .bitAnd => 7
def ShiftOp.code : ShiftOp → BitVec 3
  | .left => 1 | .rightLogical | .rightArithmetic => 5
def ShiftOp.high : ShiftOp → BitVec 7
  | .rightArithmetic => 32 | _ => 0
def RegisterOp.code : RegisterOp → BitVec 3
  | .add | .sub => 0 | .sll => 1 | .slt => 2 | .sltu => 3 | .bitXor => 4
  | .srl | .sra => 5 | .bitOr => 6 | .bitAnd => 7
def RegisterOp.high : RegisterOp → BitVec 7
  | .sub | .sra => 32 | _ => 0

def branchKind (f : BitVec 3) : Option BranchOp :=
  if f = 0 then some .eq else if f = 1 then some .ne else if f = 4 then some .lt
  else if f = 5 then some .ge else if f = 6 then some .ltu else if f = 7 then some .geu else none
def loadKind (f : BitVec 3) : Option LoadOp :=
  if f = 0 then some .byte else if f = 1 then some .half else if f = 2 then some .word
  else if f = 4 then some .byteUnsigned else if f = 5 then some .halfUnsigned else none
def storeKind (f : BitVec 3) : Option StoreOp :=
  if f = 0 then some .byte else if f = 1 then some .half else if f = 2 then some .word else none
def immediateKind (f : BitVec 3) : Option ImmediateOp :=
  if f = 0 then some .add else if f = 2 then some .slt else if f = 3 then some .sltu
  else if f = 4 then some .bitXor else if f = 6 then some .bitOr else if f = 7 then some .bitAnd else none
def shiftKind (f : BitVec 3) (high : BitVec 7) : Option ShiftOp :=
  if f = 1 ∧ high = 0 then some .left else if f = 5 ∧ high = 0 then some .rightLogical
  else if f = 5 ∧ high = 32 then some .rightArithmetic else none
def registerKind (f : BitVec 3) (high : BitVec 7) : Option RegisterOp :=
  if high = 0 then
    if f = 0 then some .add else if f = 1 then some .sll else if f = 2 then some .slt
    else if f = 3 then some .sltu else if f = 4 then some .bitXor else if f = 5 then some .srl
    else if f = 6 then some .bitOr else some .bitAnd
  else if high = 32 ∧ f = 0 then some .sub else if high = 32 ∧ f = 5 then some .sra else none

def decode (word : Word) : Option Instruction :=
  if opcode word = 0x37 then some (.lui (rd word) (uBits word))
  else if opcode word = 0x17 then some (.auipc (rd word) (uBits word))
  else if opcode word = 0x6f then some (.jal (rd word) (jBits word))
  else if opcode word = 0x67 then
    if funct3 word = 0 then some (.jalr (rd word) (rs1 word) (iBits word)) else none
  else if opcode word = 0x63 then (branchKind (funct3 word)).map fun op => .branch op (rs1 word) (rs2 word) (bBits word)
  else if opcode word = 0x03 then (loadKind (funct3 word)).map fun op => .load op (rd word) (rs1 word) (iBits word)
  else if opcode word = 0x23 then (storeKind (funct3 word)).map fun op => .store op (rs1 word) (rs2 word) (sBits word)
  else if opcode word = 0x13 then
    match immediateKind (funct3 word) with
    | some op => some (.aluImm op (rd word) (rs1 word) (iBits word))
    | none => (shiftKind (funct3 word) (funct7 word)).map fun op => .shiftImm op (rd word) (rs1 word) (rs2 word)
  else if opcode word = 0x33 then (registerKind (funct3 word) (funct7 word)).map fun op => .aluReg op (rd word) (rs1 word) (rs2 word)
  else if opcode word = 0x0f then
    if funct3 word = 0 then some (.fence (rd word) (rs1 word) (fenceMode word) (fencePredecessor word) (fenceSuccessor word)) else none
  else if word = 0x00000073 then some .ecall
  else if word = 0x00100073 then some .ebreak else none

theorem branchKind_iff (f : BitVec 3) (op : BranchOp) : branchKind f = some op ↔ f = op.code := by
  cases op <;> simp [branchKind, BranchOp.code] <;> grind

theorem loadKind_iff (f : BitVec 3) (op : LoadOp) : loadKind f = some op ↔ f = op.code := by
  cases op <;> simp [loadKind, LoadOp.code] <;> grind

theorem storeKind_iff (f : BitVec 3) (op : StoreOp) : storeKind f = some op ↔ f = op.code := by
  cases op <;> simp [storeKind, StoreOp.code] <;> grind

theorem immediateKind_iff (f : BitVec 3) (op : ImmediateOp) : immediateKind f = some op ↔ f = op.code := by
  cases op <;> simp [immediateKind, ImmediateOp.code] <;> grind

theorem shiftKind_iff (f : BitVec 3) (h : BitVec 7) (op : ShiftOp) :
    shiftKind f h = some op ↔ f = op.code ∧ h = op.high := by
  cases op <;> simp [shiftKind, ShiftOp.code, ShiftOp.high] <;> grind

theorem registerKind_iff (f : BitVec 3) (h : BitVec 7) (op : RegisterOp) :
    registerKind f h = some op ↔ f = op.code ∧ h = op.high := by
  cases op <;> simp [registerKind, RegisterOp.code, RegisterOp.high] <;> grind

/-- Direct instruction-format relation, independent of `decode` and `encode`.
Every fixed opcode/funct field and every variable operand/immediate field is
specified. In particular ECALL/EBREAK have no ignored register fields. -/
def Matches (word : Word) : Instruction → Prop
  | .lui dest upper => opcode word = 0x37 ∧ rd word = dest ∧ uBits word = upper
  | .auipc dest upper => opcode word = 0x17 ∧ rd word = dest ∧ uBits word = upper
  | .jal dest off => opcode word = 0x6f ∧ rd word = dest ∧ jBits word = off
  | .jalr dest source imm => opcode word = 0x67 ∧ funct3 word = 0 ∧ rd word = dest ∧ rs1 word = source ∧ iBits word = imm
  | .branch op first second off => opcode word = 0x63 ∧ funct3 word = op.code ∧ rs1 word = first ∧ rs2 word = second ∧ bBits word = off
  | .load op dest source imm => opcode word = 3 ∧ funct3 word = op.code ∧ rd word = dest ∧ rs1 word = source ∧ iBits word = imm
  | .store op first second imm => opcode word = 0x23 ∧ funct3 word = op.code ∧ rs1 word = first ∧ rs2 word = second ∧ sBits word = imm
  | .aluImm op dest source imm => opcode word = 0x13 ∧ funct3 word = op.code ∧ rd word = dest ∧ rs1 word = source ∧ iBits word = imm
  | .shiftImm op dest source amount => opcode word = 0x13 ∧ funct3 word = op.code ∧ funct7 word = op.high ∧ rd word = dest ∧ rs1 word = source ∧ rs2 word = amount
  | .aluReg op dest first second => opcode word = 0x33 ∧ funct3 word = op.code ∧ funct7 word = op.high ∧ rd word = dest ∧ rs1 word = first ∧ rs2 word = second
  | .fence dest source mode pred succ => opcode word = 0x0f ∧ funct3 word = 0 ∧ rd word = dest ∧ rs1 word = source ∧ fenceMode word = mode ∧ fencePredecessor word = pred ∧ fenceSuccessor word = succ
  | .ecall => word = 0x00000073
  | .ebreak => word = 0x00100073

@[simp] theorem branchKind_code (op : BranchOp) : branchKind op.code = some op := (branchKind_iff _ _).mpr rfl
@[simp] theorem loadKind_code (op : LoadOp) : loadKind op.code = some op := (loadKind_iff _ _).mpr rfl
@[simp] theorem storeKind_code (op : StoreOp) : storeKind op.code = some op := (storeKind_iff _ _).mpr rfl
@[simp] theorem immediateKind_code (op : ImmediateOp) : immediateKind op.code = some op := (immediateKind_iff _ _).mpr rfl
@[simp] theorem shiftKind_code (op : ShiftOp) : shiftKind op.code op.high = some op := (shiftKind_iff _ _ _).mpr ⟨rfl, rfl⟩
@[simp] theorem registerKind_code (op : RegisterOp) : registerKind op.code op.high = some op := (registerKind_iff _ _ _).mpr ⟨rfl, rfl⟩
@[simp] theorem immediateKind_shift (op : ShiftOp) : immediateKind op.code = none := by cases op <;> rfl

theorem matches_decode (word : Word) (instruction : Instruction) (h : Matches word instruction) :
    decode word = some instruction := by
  cases instruction <;> simp_all [Matches, decode, opcode]

theorem decode_matches (word : Word) (instruction : Instruction) (h : decode word = some instruction) :
    Matches word instruction := by
  unfold decode at h
  by_cases hop0 : opcode word = 55
  · rw [if_pos hop0] at h
    cases Option.some.inj h
    simp_all [Matches]
  rw [if_neg hop0] at h
  by_cases hop1 : opcode word = 23
  · rw [if_pos hop1] at h
    cases Option.some.inj h
    simp_all [Matches]
  rw [if_neg hop1] at h
  by_cases hop2 : opcode word = 111
  · rw [if_pos hop2] at h
    cases Option.some.inj h
    simp_all [Matches]
  rw [if_neg hop2] at h
  by_cases hop3 : opcode word = 103
  · rw [if_pos hop3] at h
    by_cases hf : funct3 word = 0
    · rw [if_pos hf] at h
      cases Option.some.inj h
      simp_all [Matches]
    · simp only [if_neg hf] at h
      contradiction
  rw [if_neg hop3] at h
  by_cases hop4 : opcode word = 99
  · rw [if_pos hop4] at h
    obtain ⟨op, hk, rfl⟩ := Option.map_eq_some_iff.mp h
    simp_all [Matches, branchKind_iff]
  rw [if_neg hop4] at h
  by_cases hop5 : opcode word = 3
  · rw [if_pos hop5] at h
    obtain ⟨op, hk, rfl⟩ := Option.map_eq_some_iff.mp h
    simp_all [Matches, loadKind_iff]
  rw [if_neg hop5] at h
  by_cases hop6 : opcode word = 35
  · rw [if_pos hop6] at h
    obtain ⟨op, hk, rfl⟩ := Option.map_eq_some_iff.mp h
    simp_all [Matches, storeKind_iff]
  rw [if_neg hop6] at h
  by_cases hop7 : opcode word = 19
  · rw [if_pos hop7] at h
    cases hk : immediateKind (funct3 word) with
    | some op =>
      simp only [hk] at h
      cases Option.some.inj h
      simp_all [Matches, immediateKind_iff]
    | none =>
      simp only [hk] at h
      obtain ⟨op, hs, rfl⟩ := Option.map_eq_some_iff.mp h
      simp_all [Matches, shiftKind_iff]
  rw [if_neg hop7] at h
  by_cases hop8 : opcode word = 51
  · rw [if_pos hop8] at h
    obtain ⟨op, hk, rfl⟩ := Option.map_eq_some_iff.mp h
    simp_all [Matches, registerKind_iff]
  rw [if_neg hop8] at h
  by_cases hop9 : opcode word = 15
  · rw [if_pos hop9] at h
    by_cases hf : funct3 word = 0
    · rw [if_pos hf] at h
      cases Option.some.inj h
      simp_all [Matches]
    · simp only [if_neg hf] at h
      contradiction
  rw [if_neg hop9] at h
  by_cases hc : word = 0x00000073
  · rw [if_pos hc] at h
    cases Option.some.inj h
    exact hc
  rw [if_neg hc] at h
  by_cases hb : word = 0x00100073
  · rw [if_pos hb] at h
    cases Option.some.inj h
    exact hb
  simp only [if_neg hb] at h
  contradiction

theorem decode_iff_matches (word : Word) (instruction : Instruction) :
    decode word = some instruction ↔ Matches word instruction :=
  ⟨decode_matches word instruction, matches_decode word instruction⟩

theorem illegal_iff (word : Word) : decode word = none ↔ ∀ instruction, ¬ Matches word instruction := by
  constructor
  · intro h instruction hm
    rw [matches_decode word instruction hm] at h
    contradiction
  · intro h
    cases hd : decode word with
    | none => rfl
    | some instruction => exact False.elim (h instruction (decode_matches word instruction hd))

theorem classification (word : Word) :
    (decode word = none ∧ ∀ instruction, ¬ Matches word instruction) ∨
      ∃ instruction, decode word = some instruction ∧ Matches word instruction := by
  cases h : decode word with
  | none => exact .inl ⟨rfl, (illegal_iff word).mp h⟩
  | some instruction => exact .inr ⟨instruction, rfl, decode_matches word instruction h⟩

theorem matches_unique (word : Word) (first second : Instruction)
    (hf : Matches word first) (hs : Matches word second) : first = second :=
  Option.some.inj ((matches_decode word first hf).symm.trans (matches_decode word second hs))

def packI (operation : BitVec 7) (function : BitVec 3) (dest source : Register) (imm : BitVec 12) : Word :=
  imm ++ source ++ function ++ dest ++ operation
def packR (operation : BitVec 7) (function : BitVec 3) (high : BitVec 7)
    (dest first second : Register) : Word := high ++ second ++ first ++ function ++ dest ++ operation

/-- A lossless encoder of the intrinsically sized typed operands. -/
def encode : Instruction → Word
  | .lui dest upper => upper ++ dest ++ (0x37 : BitVec 7)
  | .auipc dest upper => upper ++ dest ++ (0x17 : BitVec 7)
  | .jal dest off => off.extractLsb' 19 1 ++ off.extractLsb' 0 10 ++ off.extractLsb' 10 1 ++
      off.extractLsb' 11 8 ++ dest ++ (0x6f : BitVec 7)
  | .jalr dest source imm => packI 0x67 0 dest source imm
  | .branch op first second off => off.extractLsb' 11 1 ++ off.extractLsb' 4 6 ++ second ++ first ++
      op.code ++ off.extractLsb' 0 4 ++ off.extractLsb' 10 1 ++ (0x63 : BitVec 7)
  | .load op dest source imm => packI 3 op.code dest source imm
  | .store op first second imm => imm.extractLsb' 5 7 ++ second ++ first ++ op.code ++
      imm.extractLsb' 0 5 ++ (0x23 : BitVec 7)
  | .aluImm op dest source imm => packI 0x13 op.code dest source imm
  | .shiftImm op dest source amount => packR 0x13 op.code op.high dest source amount
  | .aluReg op dest first second => packR 0x33 op.code op.high dest first second
  | .fence dest source mode pred succ => mode ++ pred ++ succ ++ source ++ (0 : BitVec 3) ++ dest ++ (0x0f : BitVec 7)
  | .ecall => 0x00000073
  | .ebreak => 0x00100073

theorem encode_matches (instruction : Instruction) : Matches (encode instruction) instruction := by
  cases instruction <;> simp [Matches, encode, packI, packR, opcode, rd, rs1, rs2, funct3,
    funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  all_goals repeat' apply And.intro
  all_goals apply BitVec.eq_of_getLsbD_eq
  all_goals intro k hk
  all_goals grind (gen := 20)

theorem decode_encode (instruction : Instruction) : decode (encode instruction) = some instruction :=
  matches_decode _ instruction (encode_matches instruction)

theorem matches_encode (word : Word) (instruction : Instruction) (h : Matches word instruction) :
    encode instruction = word := by
  cases instruction with
  | lui dest upper =>
    obtain ⟨hop, hd, hu⟩ := h
    simp only [encode]
    rw [← hd, ← hu, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | auipc dest upper =>
    obtain ⟨hop, hd, hu⟩ := h
    simp only [encode]
    rw [← hd, ← hu, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | jal dest off =>
    obtain ⟨hop, hd, hj⟩ := h
    simp only [encode]
    rw [← hd, ← hj, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | jalr dest source imm =>
    obtain ⟨hop, hf, hd, hs, hi⟩ := h
    simp only [encode, packI]
    rw [← hf, ← hd, ← hs, ← hi, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | branch op first second off =>
    obtain ⟨hop, hf, hs1, hs2, hb⟩ := h
    simp only [encode]
    rw [← hf, ← hs1, ← hs2, ← hb, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | load op dest source imm =>
    obtain ⟨hop, hf, hd, hs, hi⟩ := h
    simp only [encode, packI]
    rw [← hf, ← hd, ← hs, ← hi, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | store op first second imm =>
    obtain ⟨hop, hf, hs1, hs2, hi⟩ := h
    simp only [encode]
    rw [← hf, ← hs1, ← hs2, ← hi, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | aluImm op dest source imm =>
    obtain ⟨hop, hf, hd, hs, hi⟩ := h
    simp only [encode, packI]
    rw [← hf, ← hd, ← hs, ← hi, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | shiftImm op dest source amount =>
    obtain ⟨hop, hf, hh, hd, hs, ha⟩ := h
    simp only [encode, packR]
    rw [← hf, ← hh, ← hd, ← hs, ← ha, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | aluReg op dest first second =>
    obtain ⟨hop, hf, hh, hd, hs1, hs2⟩ := h
    simp only [encode, packR]
    rw [← hf, ← hh, ← hd, ← hs1, ← hs2, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | fence dest source mode pred succ =>
    obtain ⟨hop, hf, hd, hs, hm, hp, hu⟩ := h
    simp only [encode]
    rw [← hf, ← hd, ← hs, ← hm, ← hp, ← hu, ← hop]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    grind (gen := 20) [opcode, rd, rs1, rs2, funct3, funct7, iBits, sBits, bBits, jBits, uBits, fenceMode, fencePredecessor, fenceSuccessor]
  | ecall => exact h.symm
  | ebreak => exact h.symm

theorem encode_decoded (word : Word) (instruction : Instruction) (h : decode word = some instruction) :
    encode instruction = word := matches_encode word instruction (decode_matches word instruction h)

theorem matches_word_unique (first second : Word) (instruction : Instruction)
    (hf : Matches first instruction) (hs : Matches second instruction) : first = second :=
  (matches_encode first instruction hf).symm.trans (matches_encode second instruction hs)

theorem encode_injective : Function.Injective encode := by
  intro first second h
  have hd := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using hd

/-- Per-bit specifications state the signed scattering independently of the
decoder control flow. They cover every bit of the modular 32-bit result. -/
theorem i_immediate_bit (word : Word) (k : Nat) (hk : k < 32) :
    (signedImmediate (iBits word)).getLsbD k =
      if k < 12 then word.getLsbD (k+20) else word.getLsbD 31 := by
  grind (gen := 20) [signedImmediate, iBits, BitVec.msb_eq_getLsbD_last]

theorem s_immediate_bit (word : Word) (k : Nat) (hk : k < 32) :
    (signedImmediate (sBits word)).getLsbD k =
      if k < 5 then word.getLsbD (k+7) else if k < 12 then word.getLsbD (k+20) else word.getLsbD 31 := by
  grind (gen := 20) [signedImmediate, sBits, BitVec.msb_eq_getLsbD_last]

theorem b_immediate_bit (word : Word) (k : Nat) (hk : k < 32) :
    (branchOffset (bBits word)).getLsbD k =
      if k = 0 then false else if k < 5 then word.getLsbD (k+7)
      else if k < 11 then word.getLsbD (k+20) else if k = 11 then word.getLsbD 7 else word.getLsbD 31 := by
  grind (gen := 20) [branchOffset, bBits, BitVec.msb_eq_getLsbD_last]

theorem j_immediate_bit (word : Word) (k : Nat) (hk : k < 32) :
    (jumpOffset (jBits word)).getLsbD k =
      if k = 0 then false else if k < 11 then word.getLsbD (k+20)
      else if k = 11 then word.getLsbD 20 else if k < 20 then word.getLsbD k else word.getLsbD 31 := by
  grind (gen := 20) [jumpOffset, jBits, BitVec.msb_eq_getLsbD_last]

theorem u_immediate_bit (word : Word) (k : Nat) (hk : k < 32) :
    (upperImmediate (uBits word)).getLsbD k = if k < 12 then false else word.getLsbD k := by
  grind (gen := 20) [upperImmediate, uBits]

end Pinwheel.Hardware.Processor.RV32I
