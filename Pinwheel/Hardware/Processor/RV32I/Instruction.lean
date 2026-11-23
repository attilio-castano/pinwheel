import Std

/-! Pure RV32I 2.1 instruction vocabulary. Source: the pinned RISC-V
Unprivileged ISA release 20260120, chapter 2 §§2.2–2.9 and chapter 36 RV32I
encoding table (tools/riscv-isa.json). No execution, EEI, or hardware is defined.
-/
namespace Pinwheel.Hardware.Processor.RV32I

abbrev Word := BitVec 32
abbrev Register := BitVec 5

inductive BranchOp where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr

inductive LoadOp where
  | byte | half | word | byteUnsigned | halfUnsigned
  deriving DecidableEq, Repr

inductive StoreOp where
  | byte | half | word
  deriving DecidableEq, Repr

inductive ImmediateOp where
  | add | slt | sltu | bitXor | bitOr | bitAnd
  deriving DecidableEq, Repr

inductive ShiftOp where
  | left | rightLogical | rightArithmetic
  deriving DecidableEq, Repr

inductive RegisterOp where
  | add | sub | sll | slt | sltu | bitXor | srl | sra | bitOr | bitAnd
  deriving DecidableEq, Repr

/-- Immediate fields retain their exact instruction bits. I/S fields are signed
12-bit values; B fields are offset[12:1], J fields offset[20:1], and U fields
imm[31:12]. Use the getters below to obtain their 32-bit byte values. A shift
amount is exactly five bits, as required for RV32I (not RV64I).

FENCE keeps even unused/reserved fields for lossless decoding. Section 2.7
requires base implementations to ignore rd/rs1 and treat reserved fm/configurations
as ordinary FENCE; conservative execution may additionally order all operations.
This instruction datatype does not itself implement memory ordering.
-/
inductive Instruction where
  | lui (rd : Register) (upper : BitVec 20)
  | auipc (rd : Register) (upper : BitVec 20)
  | jal (rd : Register) (offset : BitVec 20)
  | jalr (rd rs1 : Register) (immediate : BitVec 12)
  | branch (op : BranchOp) (rs1 rs2 : Register) (offset : BitVec 12)
  | load (op : LoadOp) (rd rs1 : Register) (immediate : BitVec 12)
  | store (op : StoreOp) (rs1 rs2 : Register) (immediate : BitVec 12)
  | aluImm (op : ImmediateOp) (rd rs1 : Register) (immediate : BitVec 12)
  | shiftImm (op : ShiftOp) (rd rs1 : Register) (amount : BitVec 5)
  | aluReg (op : RegisterOp) (rd rs1 rs2 : Register)
  | fence (rd rs1 : Register) (mode predecessor successor : BitVec 4)
  | ecall
  | ebreak
  deriving DecidableEq, Repr

def signedImmediate (bits : BitVec 12) : Word := bits.signExtend 32
def branchOffset (bits : BitVec 12) : Word := (bits ++ (0 : BitVec 1)).signExtend 32
def jumpOffset (bits : BitVec 20) : Word := (bits ++ (0 : BitVec 1)).signExtend 32
def upperImmediate (bits : BitVec 20) : Word := bits ++ (0 : BitVec 12)

/-- The immediate as a modular 32-bit value, including low zero bits in U/B/J
formats. Arithmetic interpretation and PC addition belong to execution semantics. -/
def Instruction.immediate : Instruction → Option Word
  | .lui _ bits | .auipc _ bits => some (upperImmediate bits)
  | .jal _ bits => some (jumpOffset bits)
  | .jalr _ _ bits | .load _ _ _ bits | .store _ _ _ bits | .aluImm _ _ _ bits => some (signedImmediate bits)
  | .branch _ _ _ bits => some (branchOffset bits)
  | .shiftImm _ _ _ amount => some (amount.setWidth 32)
  | _ => none

theorem signedImmediate_toInt (bits : BitVec 12) : (signedImmediate bits).toInt = bits.toInt :=
  BitVec.toInt_signExtend_of_le (by decide)

theorem branchOffset_toInt (bits : BitVec 12) : (branchOffset bits).toInt = 2 * bits.toInt := by
  rw [branchOffset, BitVec.toInt_signExtend_of_le (by decide : 13 ≤ 32)]
  exact BitVec.toInt_append_zero

theorem jumpOffset_toInt (bits : BitVec 20) : (jumpOffset bits).toInt = 2 * bits.toInt := by
  rw [jumpOffset, BitVec.toInt_signExtend_of_le (by decide : 21 ≤ 32)]
  exact BitVec.toInt_append_zero

theorem upperImmediate_toNat (bits : BitVec 20) : (upperImmediate bits).toNat = bits.toNat * 4096 := by
  have h := BitVec.toNat_append (x := bits) (y := (0 : BitVec 12))
  simpa [upperImmediate, Nat.shiftLeft_eq] using h

end Pinwheel.Hardware.Processor.RV32I
