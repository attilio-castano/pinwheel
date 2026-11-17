import Pinwheel.Hardware.WordOps
import Pinwheel.Hardware.Interface
import Pinwheel.Hardware.Processor.RV32I.Decode

/-! Combinational RV32I decoding made entirely from existing expression trees.
The stable six-bit tag is the complete mnemonic/control classification. Zero is
illegal/unsupported; tags 1..40 are defined by `Kind.tag`. No execution, memory
operation, or CPU retirement is implied. All invalid and inapplicable fields are
zero. FENCE retains raw rd/rs1/mode/predecessor/successor as data, not register
write or memory-action enables; all reserved FENCE fields remain accepted.
-/
namespace Pinwheel.Hardware.Processor.RV32I.DecodeCircuit

inductive Kind where
  | lui
  | auipc
  | jal
  | jalr
  | beq
  | bne
  | blt
  | bge
  | bltu
  | bgeu
  | lb
  | lh
  | lw
  | lbu
  | lhu
  | sb
  | sh
  | sw
  | addi
  | slti
  | sltiu
  | xori
  | ori
  | andi
  | slli
  | srli
  | srai
  | add
  | sub
  | sll
  | slt
  | sltu
  | bitXor
  | srl
  | sra
  | bitOr
  | bitAnd
  | fence
  | ecall
  | ebreak
  deriving DecidableEq, Repr

def Kind.tag : Kind → BitVec 6
  | .lui => 1
  | .auipc => 2
  | .jal => 3
  | .jalr => 4
  | .beq => 5
  | .bne => 6
  | .blt => 7
  | .bge => 8
  | .bltu => 9
  | .bgeu => 10
  | .lb => 11
  | .lh => 12
  | .lw => 13
  | .lbu => 14
  | .lhu => 15
  | .sb => 16
  | .sh => 17
  | .sw => 18
  | .addi => 19
  | .slti => 20
  | .sltiu => 21
  | .xori => 22
  | .ori => 23
  | .andi => 24
  | .slli => 25
  | .srli => 26
  | .srai => 27
  | .add => 28
  | .sub => 29
  | .sll => 30
  | .slt => 31
  | .sltu => 32
  | .bitXor => 33
  | .srl => 34
  | .sra => 35
  | .bitOr => 36
  | .bitAnd => 37
  | .fence => 38
  | .ecall => 39
  | .ebreak => 40

def kinds : List Kind := [.lui, .auipc, .jal, .jalr, .beq, .bne, .blt, .bge, .bltu, .bgeu, .lb, .lh, .lw, .lbu, .lhu, .sb, .sh, .sw, .addi, .slti, .sltiu, .xori, .ori, .andi, .slli, .srli, .srai, .add, .sub, .sll, .slt, .sltu, .bitXor, .srl, .sra, .bitOr, .bitAnd, .fence, .ecall, .ebreak]

def decodeTag (tag : BitVec 6) : Option Kind := kinds.find? fun kind => kind.tag == tag

@[simp] theorem decodeTag_tag (kind : Kind) : decodeTag kind.tag = some kind := by cases kind <;> rfl

theorem tag_injective : Function.Injective Kind.tag := by
  intro a b h
  have he := congrArg decodeTag h
  simpa only [decodeTag_tag, Option.some.injEq] using he

@[simp] theorem tag_nonzero (kind : Kind) : kind.tag ≠ 0 := by cases kind <;> decide +kernel
@[simp] theorem kind_mem (kind : Kind) : kind ∈ kinds := by cases kind <;> decide +kernel

def construct (kind : Kind) (w : Word) : Instruction :=
  match kind with
  | .lui => .lui (rd w) (uBits w)
  | .auipc => .auipc (rd w) (uBits w)
  | .jal => .jal (rd w) (jBits w)
  | .jalr => .jalr (rd w) (rs1 w) (iBits w)
  | .beq => .branch .eq (rs1 w) (rs2 w) (bBits w)
  | .bne => .branch .ne (rs1 w) (rs2 w) (bBits w)
  | .blt => .branch .lt (rs1 w) (rs2 w) (bBits w)
  | .bge => .branch .ge (rs1 w) (rs2 w) (bBits w)
  | .bltu => .branch .ltu (rs1 w) (rs2 w) (bBits w)
  | .bgeu => .branch .geu (rs1 w) (rs2 w) (bBits w)
  | .lb => .load .byte (rd w) (rs1 w) (iBits w)
  | .lh => .load .half (rd w) (rs1 w) (iBits w)
  | .lw => .load .word (rd w) (rs1 w) (iBits w)
  | .lbu => .load .byteUnsigned (rd w) (rs1 w) (iBits w)
  | .lhu => .load .halfUnsigned (rd w) (rs1 w) (iBits w)
  | .sb => .store .byte (rs1 w) (rs2 w) (sBits w)
  | .sh => .store .half (rs1 w) (rs2 w) (sBits w)
  | .sw => .store .word (rs1 w) (rs2 w) (sBits w)
  | .addi => .aluImm .add (rd w) (rs1 w) (iBits w)
  | .slti => .aluImm .slt (rd w) (rs1 w) (iBits w)
  | .sltiu => .aluImm .sltu (rd w) (rs1 w) (iBits w)
  | .xori => .aluImm .bitXor (rd w) (rs1 w) (iBits w)
  | .ori => .aluImm .bitOr (rd w) (rs1 w) (iBits w)
  | .andi => .aluImm .bitAnd (rd w) (rs1 w) (iBits w)
  | .slli => .shiftImm .left (rd w) (rs1 w) (rs2 w)
  | .srli => .shiftImm .rightLogical (rd w) (rs1 w) (rs2 w)
  | .srai => .shiftImm .rightArithmetic (rd w) (rs1 w) (rs2 w)
  | .add => .aluReg .add (rd w) (rs1 w) (rs2 w)
  | .sub => .aluReg .sub (rd w) (rs1 w) (rs2 w)
  | .sll => .aluReg .sll (rd w) (rs1 w) (rs2 w)
  | .slt => .aluReg .slt (rd w) (rs1 w) (rs2 w)
  | .sltu => .aluReg .sltu (rd w) (rs1 w) (rs2 w)
  | .bitXor => .aluReg .bitXor (rd w) (rs1 w) (rs2 w)
  | .srl => .aluReg .srl (rd w) (rs1 w) (rs2 w)
  | .sra => .aluReg .sra (rd w) (rs1 w) (rs2 w)
  | .bitOr => .aluReg .bitOr (rd w) (rs1 w) (rs2 w)
  | .bitAnd => .aluReg .bitAnd (rd w) (rs1 w) (rs2 w)
  | .fence => .fence (rd w) (rs1 w) (fenceMode w) (fencePredecessor w) (fenceSuccessor w)
  | .ecall => .ecall
  | .ebreak => .ebreak

def kindOf : Instruction → Kind
  | .lui _ _ => .lui
  | .auipc _ _ => .auipc
  | .jal _ _ => .jal
  | .jalr _ _ _ => .jalr
  | .branch .eq _ _ _ => .beq
  | .branch .ne _ _ _ => .bne
  | .branch .lt _ _ _ => .blt
  | .branch .ge _ _ _ => .bge
  | .branch .ltu _ _ _ => .bltu
  | .branch .geu _ _ _ => .bgeu
  | .load .byte _ _ _ => .lb
  | .load .half _ _ _ => .lh
  | .load .word _ _ _ => .lw
  | .load .byteUnsigned _ _ _ => .lbu
  | .load .halfUnsigned _ _ _ => .lhu
  | .store .byte _ _ _ => .sb
  | .store .half _ _ _ => .sh
  | .store .word _ _ _ => .sw
  | .aluImm .add _ _ _ => .addi
  | .aluImm .slt _ _ _ => .slti
  | .aluImm .sltu _ _ _ => .sltiu
  | .aluImm .bitXor _ _ _ => .xori
  | .aluImm .bitOr _ _ _ => .ori
  | .aluImm .bitAnd _ _ _ => .andi
  | .shiftImm .left _ _ _ => .slli
  | .shiftImm .rightLogical _ _ _ => .srli
  | .shiftImm .rightArithmetic _ _ _ => .srai
  | .aluReg .add _ _ _ => .add
  | .aluReg .sub _ _ _ => .sub
  | .aluReg .sll _ _ _ => .sll
  | .aluReg .slt _ _ _ => .slt
  | .aluReg .sltu _ _ _ => .sltu
  | .aluReg .bitXor _ _ _ => .bitXor
  | .aluReg .srl _ _ _ => .srl
  | .aluReg .sra _ _ _ => .sra
  | .aluReg .bitOr _ _ _ => .bitOr
  | .aluReg .bitAnd _ _ _ => .bitAnd
  | .fence _ _ _ _ _ => .fence
  | .ecall => .ecall
  | .ebreak => .ebreak

@[simp] theorem kindOf_construct (kind : Kind) (w : Word) : kindOf (construct kind w) = kind := by cases kind <;> rfl

def MatchesKind (w : Word) : Kind → Prop
  | .lui => opcode w = 55
  | .auipc => opcode w = 23
  | .jal => opcode w = 111
  | .jalr => opcode w = 103 ∧ funct3 w = 0
  | .beq => opcode w = 99 ∧ funct3 w = 0
  | .bne => opcode w = 99 ∧ funct3 w = 1
  | .blt => opcode w = 99 ∧ funct3 w = 4
  | .bge => opcode w = 99 ∧ funct3 w = 5
  | .bltu => opcode w = 99 ∧ funct3 w = 6
  | .bgeu => opcode w = 99 ∧ funct3 w = 7
  | .lb => opcode w = 3 ∧ funct3 w = 0
  | .lh => opcode w = 3 ∧ funct3 w = 1
  | .lw => opcode w = 3 ∧ funct3 w = 2
  | .lbu => opcode w = 3 ∧ funct3 w = 4
  | .lhu => opcode w = 3 ∧ funct3 w = 5
  | .sb => opcode w = 35 ∧ funct3 w = 0
  | .sh => opcode w = 35 ∧ funct3 w = 1
  | .sw => opcode w = 35 ∧ funct3 w = 2
  | .addi => opcode w = 19 ∧ funct3 w = 0
  | .slti => opcode w = 19 ∧ funct3 w = 2
  | .sltiu => opcode w = 19 ∧ funct3 w = 3
  | .xori => opcode w = 19 ∧ funct3 w = 4
  | .ori => opcode w = 19 ∧ funct3 w = 6
  | .andi => opcode w = 19 ∧ funct3 w = 7
  | .slli => opcode w = 19 ∧ funct3 w = 1 ∧ funct7 w = 0
  | .srli => opcode w = 19 ∧ funct3 w = 5 ∧ funct7 w = 0
  | .srai => opcode w = 19 ∧ funct3 w = 5 ∧ funct7 w = 32
  | .add => opcode w = 51 ∧ funct3 w = 0 ∧ funct7 w = 0
  | .sub => opcode w = 51 ∧ funct3 w = 0 ∧ funct7 w = 32
  | .sll => opcode w = 51 ∧ funct3 w = 1 ∧ funct7 w = 0
  | .slt => opcode w = 51 ∧ funct3 w = 2 ∧ funct7 w = 0
  | .sltu => opcode w = 51 ∧ funct3 w = 3 ∧ funct7 w = 0
  | .bitXor => opcode w = 51 ∧ funct3 w = 4 ∧ funct7 w = 0
  | .srl => opcode w = 51 ∧ funct3 w = 5 ∧ funct7 w = 0
  | .sra => opcode w = 51 ∧ funct3 w = 5 ∧ funct7 w = 32
  | .bitOr => opcode w = 51 ∧ funct3 w = 6 ∧ funct7 w = 0
  | .bitAnd => opcode w = 51 ∧ funct3 w = 7 ∧ funct7 w = 0
  | .fence => opcode w = 15 ∧ funct3 w = 0
  | .ecall => w = 115
  | .ebreak => w = 1048691

instance (w : Word) (kind : Kind) : Decidable (MatchesKind w kind) := by
  cases kind <;> unfold MatchesKind <;> infer_instance

theorem matches_construct (w : Word) (kind : Kind) :
    Matches w (construct kind w) ↔ MatchesKind w kind := by
  cases kind <;> simp [construct, Matches, MatchesKind, BranchOp.code, LoadOp.code,
    StoreOp.code, ImmediateOp.code, ShiftOp.code, ShiftOp.high, RegisterOp.code, RegisterOp.high]

theorem construct_decoded (w : Word) (kind : Kind) (h : MatchesKind w kind) :
    decode w = some (construct kind w) := matches_decode w _ ((matches_construct w kind).mpr h)

theorem decoded_kind (w : Word) (instruction : Instruction) (h : decode w = some instruction) :
    MatchesKind w (kindOf instruction) ∧ construct (kindOf instruction) w = instruction := by
  have hm := decode_matches w instruction h
  cases instruction <;> simp only [Matches] at hm
  all_goals first
    | (rename_i op _ _ _; cases op <;> simp_all [kindOf, MatchesKind, construct, BranchOp.code,
        LoadOp.code, StoreOp.code, ImmediateOp.code, ShiftOp.code, ShiftOp.high, RegisterOp.code, RegisterOp.high])
    | simp_all [kindOf, MatchesKind, construct]

def recognize (word : Expr I R 32) : Kind → Expr I R 1
  | .lui => .equal (.slice 0 7 (by decide) word) (.lit 55)
  | .auipc => .equal (.slice 0 7 (by decide) word) (.lit 23)
  | .jal => .equal (.slice 0 7 (by decide) word) (.lit 111)
  | .jalr => .band (.equal (.slice 0 7 (by decide) word) (.lit 103)) (.equal (.slice 12 3 (by decide) word) (.lit 0))
  | .beq => .band (.equal (.slice 0 7 (by decide) word) (.lit 99)) (.equal (.slice 12 3 (by decide) word) (.lit 0))
  | .bne => .band (.equal (.slice 0 7 (by decide) word) (.lit 99)) (.equal (.slice 12 3 (by decide) word) (.lit 1))
  | .blt => .band (.equal (.slice 0 7 (by decide) word) (.lit 99)) (.equal (.slice 12 3 (by decide) word) (.lit 4))
  | .bge => .band (.equal (.slice 0 7 (by decide) word) (.lit 99)) (.equal (.slice 12 3 (by decide) word) (.lit 5))
  | .bltu => .band (.equal (.slice 0 7 (by decide) word) (.lit 99)) (.equal (.slice 12 3 (by decide) word) (.lit 6))
  | .bgeu => .band (.equal (.slice 0 7 (by decide) word) (.lit 99)) (.equal (.slice 12 3 (by decide) word) (.lit 7))
  | .lb => .band (.equal (.slice 0 7 (by decide) word) (.lit 3)) (.equal (.slice 12 3 (by decide) word) (.lit 0))
  | .lh => .band (.equal (.slice 0 7 (by decide) word) (.lit 3)) (.equal (.slice 12 3 (by decide) word) (.lit 1))
  | .lw => .band (.equal (.slice 0 7 (by decide) word) (.lit 3)) (.equal (.slice 12 3 (by decide) word) (.lit 2))
  | .lbu => .band (.equal (.slice 0 7 (by decide) word) (.lit 3)) (.equal (.slice 12 3 (by decide) word) (.lit 4))
  | .lhu => .band (.equal (.slice 0 7 (by decide) word) (.lit 3)) (.equal (.slice 12 3 (by decide) word) (.lit 5))
  | .sb => .band (.equal (.slice 0 7 (by decide) word) (.lit 35)) (.equal (.slice 12 3 (by decide) word) (.lit 0))
  | .sh => .band (.equal (.slice 0 7 (by decide) word) (.lit 35)) (.equal (.slice 12 3 (by decide) word) (.lit 1))
  | .sw => .band (.equal (.slice 0 7 (by decide) word) (.lit 35)) (.equal (.slice 12 3 (by decide) word) (.lit 2))
  | .addi => .band (.equal (.slice 0 7 (by decide) word) (.lit 19)) (.equal (.slice 12 3 (by decide) word) (.lit 0))
  | .slti => .band (.equal (.slice 0 7 (by decide) word) (.lit 19)) (.equal (.slice 12 3 (by decide) word) (.lit 2))
  | .sltiu => .band (.equal (.slice 0 7 (by decide) word) (.lit 19)) (.equal (.slice 12 3 (by decide) word) (.lit 3))
  | .xori => .band (.equal (.slice 0 7 (by decide) word) (.lit 19)) (.equal (.slice 12 3 (by decide) word) (.lit 4))
  | .ori => .band (.equal (.slice 0 7 (by decide) word) (.lit 19)) (.equal (.slice 12 3 (by decide) word) (.lit 6))
  | .andi => .band (.equal (.slice 0 7 (by decide) word) (.lit 19)) (.equal (.slice 12 3 (by decide) word) (.lit 7))
  | .slli => .band (.equal (.slice 0 7 (by decide) word) (.lit 19)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 1)) (.equal (.slice 25 7 (by decide) word) (.lit 0)))
  | .srli => .band (.equal (.slice 0 7 (by decide) word) (.lit 19)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 5)) (.equal (.slice 25 7 (by decide) word) (.lit 0)))
  | .srai => .band (.equal (.slice 0 7 (by decide) word) (.lit 19)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 5)) (.equal (.slice 25 7 (by decide) word) (.lit 32)))
  | .add => .band (.equal (.slice 0 7 (by decide) word) (.lit 51)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 0)) (.equal (.slice 25 7 (by decide) word) (.lit 0)))
  | .sub => .band (.equal (.slice 0 7 (by decide) word) (.lit 51)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 0)) (.equal (.slice 25 7 (by decide) word) (.lit 32)))
  | .sll => .band (.equal (.slice 0 7 (by decide) word) (.lit 51)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 1)) (.equal (.slice 25 7 (by decide) word) (.lit 0)))
  | .slt => .band (.equal (.slice 0 7 (by decide) word) (.lit 51)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 2)) (.equal (.slice 25 7 (by decide) word) (.lit 0)))
  | .sltu => .band (.equal (.slice 0 7 (by decide) word) (.lit 51)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 3)) (.equal (.slice 25 7 (by decide) word) (.lit 0)))
  | .bitXor => .band (.equal (.slice 0 7 (by decide) word) (.lit 51)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 4)) (.equal (.slice 25 7 (by decide) word) (.lit 0)))
  | .srl => .band (.equal (.slice 0 7 (by decide) word) (.lit 51)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 5)) (.equal (.slice 25 7 (by decide) word) (.lit 0)))
  | .sra => .band (.equal (.slice 0 7 (by decide) word) (.lit 51)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 5)) (.equal (.slice 25 7 (by decide) word) (.lit 32)))
  | .bitOr => .band (.equal (.slice 0 7 (by decide) word) (.lit 51)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 6)) (.equal (.slice 25 7 (by decide) word) (.lit 0)))
  | .bitAnd => .band (.equal (.slice 0 7 (by decide) word) (.lit 51)) (.band (.equal (.slice 12 3 (by decide) word) (.lit 7)) (.equal (.slice 25 7 (by decide) word) (.lit 0)))
  | .fence => .band (.equal (.slice 0 7 (by decide) word) (.lit 15)) (.equal (.slice 12 3 (by decide) word) (.lit 0))
  | .ecall => .equal word (.lit 115)
  | .ebreak => .equal word (.lit 1048691)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem recognize_eval (word : Expr I R 32) (kind : Kind) (i : Values I) (s : Values R) :
    (recognize word kind).eval i s = BitVec.ofBool (decide (MatchesKind (word.eval i s) kind)) := by
  cases kind <;> simp [recognize, Expr.eval, MatchesKind, opcode, funct3, funct7 ]

def select (word : Expr I R 32) (value : Kind → Expr I R b) : List Kind → Expr I R b
  | [] => .lit 0
  | kind :: rest => .mux (recognize word kind) (value kind) (select word value rest)

theorem select_none (word : Expr I R 32) (value : Kind → Expr I R b) (ks : List Kind)
    (i : Values I) (s : Values R) (h : decode (word.eval i s) = none) :
    (select word value ks).eval i s = 0 := by
  induction ks with
  | nil => rfl
  | cons kind rest ih =>
      have hn : ¬ MatchesKind (word.eval i s) kind := by
        intro hm
        have hd := construct_decoded _ _ hm
        rw [h] at hd
        cases hd
      simp [select, Expr.eval, recognize_eval, hn, ih]

theorem select_some (word : Expr I R 32) (value : Kind → Expr I R b) (ks : List Kind)
    (i : Values I) (s : Values R) (instruction : Instruction)
    (h : decode (word.eval i s) = some instruction) (member : kindOf instruction ∈ ks) :
    (select word value ks).eval i s = (value (kindOf instruction)).eval i s := by
  induction ks with
  | nil => cases member
  | cons kind rest ih =>
      by_cases hm : MatchesKind (word.eval i s) kind
      · have he : construct kind (word.eval i s) = instruction := Option.some.inj ((construct_decoded _ _ hm).symm.trans h)
        have hk : kind = kindOf instruction := by simpa using congrArg kindOf he
        simpa [select, Expr.eval, recognize_eval, hm] using congrArg (fun k => (value k).eval i s) hk
      · have hr : kindOf instruction ∈ rest := by
          rcases List.mem_cons.mp member with he | he
          · subst kind
            exact False.elim (hm (decoded_kind _ _ h).1)
          · exact he
        simp [select, Expr.eval, recognize_eval, hm, ih hr]

inductive Field : Nat → Type where
  | valid : Field 1
  | tag : Field 6
  | rd : Field 5
  | rs1 : Field 5
  | rs2 : Field 5
  | immediate : Field 32
  | fenceMode : Field 4
  | fencePredecessor : Field 4
  | fenceSuccessor : Field 4
  deriving DecidableEq

/-- A width-indexed expression bundle, usable directly or through `Expr.bind`. -/
abbrev Bundle (I R : Nat → Type) := {b : Nat} → Field b → Expr I R b

def instructionRd : Instruction → Register
  | .lui d _ | .auipc d _ | .jal d _ | .jalr d _ _ | .load _ d _ _
  | .aluImm _ d _ _ | .shiftImm _ d _ _ | .aluReg _ d _ _ | .fence d _ _ _ _ => d
  | _ => 0

def instructionRs1 : Instruction → Register
  | .jalr _ a _ | .branch _ a _ _ | .load _ _ a _ | .store _ a _ _
  | .aluImm _ _ a _ | .shiftImm _ _ a _ | .aluReg _ _ a _ | .fence _ a _ _ _ => a
  | _ => 0

def instructionRs2 : Instruction → Register
  | .branch _ _ b _ | .store _ _ b _ | .aluReg _ _ _ b => b
  | _ => 0

def fields (instruction : Instruction) : Values Field
  | _, .valid => 1
  | _, .tag => (kindOf instruction).tag
  | _, .rd => instructionRd instruction
  | _, .rs1 => instructionRs1 instruction
  | _, .rs2 => instructionRs2 instruction
  | _, .immediate => instruction.immediate.getD 0
  | _, .fenceMode => match instruction with | .fence _ _ m _ _ => m | _ => 0
  | _, .fencePredecessor => match instruction with | .fence _ _ _ p _ => p | _ => 0
  | _, .fenceSuccessor => match instruction with | .fence _ _ _ _ s => s | _ => 0

def expected (word : Word) : Values Field :=
  match decode word with | some instruction => fields instruction | none => fun _ => 0

def Kind.hasRD : Kind → Bool
  | .lui | .auipc | .jal | .jalr | .lb | .lh | .lw | .lbu | .lhu | .addi | .slti | .sltiu | .xori | .ori | .andi | .slli | .srli | .srai | .add | .sub | .sll | .slt | .sltu | .bitXor | .srl | .sra | .bitOr | .bitAnd | .fence => true
  | _ => false

def Kind.hasRS1 : Kind → Bool
  | .jalr | .beq | .bne | .blt | .bge | .bltu | .bgeu | .lb | .lh | .lw | .lbu | .lhu | .sb | .sh | .sw | .addi | .slti | .sltiu | .xori | .ori | .andi | .slli | .srli | .srai | .add | .sub | .sll | .slt | .sltu | .bitXor | .srl | .sra | .bitOr | .bitAnd | .fence => true
  | _ => false

def Kind.hasRS2 : Kind → Bool
  | .beq | .bne | .blt | .bge | .bltu | .bgeu | .sb | .sh | .sw | .add | .sub | .sll | .slt | .sltu | .bitXor | .srl | .sra | .bitOr | .bitAnd => true
  | _ => false

def extend (upper : Nat) (bits : Expr I R n) : Expr I R (upper+n) :=
  .concat (.mux (WordOps.signBit bits) (.lit (BitVec.allOnes upper)) (.lit 0)) bits

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem extend_eval (upper : Nat) (bits : Expr I R n) (i : Values I) (s : Values R) :
    (extend upper bits).eval i s = (bits.eval i s).signExtend (upper+n) := by
  rw [BitVec.signExtend_eq_append_of_le (by omega : n ≤ upper+n)]
  simp only [extend, Expr.eval, WordOps.signBit_eval]
  have hn : upper+n-n = upper := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  cases (bits.eval i s).msb <;> simp [BitVec.getLsbD_append, hn]

def immediateExpr (word : Expr I R 32) : Kind → Expr I R 32
  | .lui | .auipc => .concat (.slice 12 20 (by decide) word) (.lit (0#12))
  | .jal => extend 11 (.concat (.concat (.concat (.concat (.slice 31 1 (by decide) word) (.slice 12 8 (by decide) word)) (.slice 20 1 (by decide) word)) (.slice 21 10 (by decide) word)) (.lit (0#1)))
  | .jalr | .lb | .lh | .lw | .lbu | .lhu | .addi | .slti | .sltiu | .xori | .ori | .andi => extend 20 (.slice 20 12 (by decide) word)
  | .beq | .bne | .blt | .bge | .bltu | .bgeu => extend 19 (.concat (.concat (.concat (.concat (.slice 31 1 (by decide) word) (.slice 7 1 (by decide) word)) (.slice 25 6 (by decide) word)) (.slice 8 4 (by decide) word)) (.lit (0#1)))
  | .sb | .sh | .sw => extend 20 (.concat (.slice 25 7 (by decide) word) (.slice 7 5 (by decide) word))
  | .slli | .srli | .srai => .concat (.lit (0#27)) (.slice 20 5 (by decide) word)
  | _ => .lit 0

def fieldExpr (word : Expr I R 32) (kind : Kind) : {b : Nat} → Field b → Expr I R b
  | _, .valid => .lit 1
  | _, .tag => .lit kind.tag
  | _, .rd => if kind.hasRD then .slice 7 5 (by decide) word else .lit 0
  | _, .rs1 => if kind.hasRS1 then .slice 15 5 (by decide) word else .lit 0
  | _, .rs2 => if kind.hasRS2 then .slice 20 5 (by decide) word else .lit 0
  | _, .immediate => immediateExpr word kind
  | _, .fenceMode => if kind = .fence then .slice 28 4 (by decide) word else .lit 0
  | _, .fencePredecessor => if kind = .fence then .slice 24 4 (by decide) word else .lit 0
  | _, .fenceSuccessor => if kind = .fence then .slice 20 4 (by decide) word else .lit 0

theorem shift_zero_extension (bits : BitVec 5) : (0#27) ++ bits = bits.setWidth 32 := by
  revert bits
  decide +kernel

@[simp] theorem fieldExpr_eval (word : Expr I R 32) (kind : Kind) (field : Field b)
    (i : Values I) (s : Values R) :
    (fieldExpr word kind field).eval i s = fields (construct kind (word.eval i s)) field := by
  cases kind <;> cases field <;>
    simp [fieldExpr, fields, construct, kindOf, Kind.hasRD, Kind.hasRS1, Kind.hasRS2,
      instructionRd, instructionRs1, instructionRs2, immediateExpr, Instruction.immediate,
      Expr.eval, extend_eval, rd, rs1, rs2, uBits, iBits, sBits, bBits, jBits,
      fenceMode, fencePredecessor, fenceSuccessor, signedImmediate, upperImmediate,
      branchOffset, jumpOffset, shift_zero_extension]

def bundle (word : Expr I R 32) : Bundle I R := fun field =>
  select word (fun kind => fieldExpr word kind field) kinds

@[simp] theorem bundle_eval (word : Expr I R 32) (field : Field b) (i : Values I) (s : Values R) :
    (bundle word field).eval i s = expected (word.eval i s) field := by
  cases h : decode (word.eval i s) with
  | none => simpa [bundle, expected, h] using select_none word (fun k => fieldExpr word k field) kinds i s h
  | some instruction =>
      rw [bundle, select_some word _ kinds i s instruction h (kind_mem _), fieldExpr_eval,
        (decoded_kind _ _ h).2]
      simp [expected, h]

theorem decodeTag_some_iff (tag : BitVec 6) (kind : Kind) :
    decodeTag tag = some kind ↔ tag = kind.tag := by
  constructor
  · intro h
    have he := List.find?_some h
    exact (beq_iff_eq.mp he).symm
  · intro h
    subst tag
    exact decodeTag_tag kind

@[simp] theorem decodeTag_zero : decodeTag 0 = none := by decide +kernel

theorem invalid_zero (word : Expr I R 32) (i : Values I) (s : Values R)
    (h : decode (word.eval i s) = none) (field : Field b) :
    (bundle word field).eval i s = 0 := by simp [bundle_eval, expected, h]

theorem valid_iff (word : Expr I R 32) (i : Values I) (s : Values R) :
    (bundle word .valid).eval i s = 1 ↔ (decode (word.eval i s)).isSome = true := by
  cases h : decode (word.eval i s) <;> simp [bundle_eval, expected, fields, h]

/-- The emitted tag has an exact inverse. Invalid raw instructions do not
alias a legal mnemonic, and distinct legal mnemonics have distinct tags. -/
theorem tag_decode (word : Expr I R 32) (i : Values I) (s : Values R) :
    decodeTag ((bundle word .tag).eval i s) = (decode (word.eval i s)).map kindOf := by
  cases h : decode (word.eval i s) <;> simp [bundle_eval, expected, fields, h] <;> rfl

theorem tag_iff (word : Expr I R 32) (i : Values I) (s : Values R) (kind : Kind) :
    (bundle word .tag).eval i s = kind.tag ↔
      ∃ instruction, decode (word.eval i s) = some instruction ∧ kindOf instruction = kind := by
  rw [← decodeTag_some_iff, tag_decode, Option.map_eq_some_iff]

def bind (value : Bundle I R) (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) : Bundle J S :=
  fun field => (value field).bind input register

theorem bundle_bind_eval (word : Expr I R 32) (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (i : Values J) (s : Values S) (field : Field b) :
    (bind (bundle word) input register field).eval i s =
      (bundle (word.bind input register) field).eval i s := by
  simp only [bind, Expr.eval_bind, bundle_eval]

/-- Complete typed descriptors make the bundle directly exportable as a
stateless circuit. Descriptor order is valid, tag, rd, rs1, rs2, immediate,
fence_mode, fence_predecessor, fence_successor. -/
def outputs : Interface Field where
  size := 9
  signal k := match k with
    | ⟨0, _⟩ => ⟨1, .valid⟩ | ⟨1, _⟩ => ⟨6, .tag⟩
    | ⟨2, _⟩ => ⟨5, .rd⟩ | ⟨3, _⟩ => ⟨5, .rs1⟩ | ⟨4, _⟩ => ⟨5, .rs2⟩
    | ⟨5, _⟩ => ⟨32, .immediate⟩ | ⟨6, _⟩ => ⟨4, .fenceMode⟩
    | ⟨7, _⟩ => ⟨4, .fencePredecessor⟩ | ⟨8, _⟩ => ⟨4, .fenceSuccessor⟩
    | ⟨n+9, h⟩ => False.elim (by omega)
  position field := match field with
    | .valid => 0 | .tag => 1 | .rd => 2 | .rs1 => 3 | .rs2 => 4
    | .immediate => 5 | .fenceMode => 6 | .fencePredecessor => 7 | .fenceSuccessor => 8
  signal_position field := by cases field <;> rfl
  label field := match field with
    | .valid => "decode_valid" | .tag => "tag" | .rd => "rd" | .rs1 => "rs1" | .rs2 => "rs2"
    | .immediate => "immediate" | .fenceMode => "fence_mode"
    | .fencePredecessor => "fence_predecessor" | .fenceSuccessor => "fence_successor"
  unique := by decide +kernel

inductive Input : Nat → Type where
  | instruction : Input 32

abbrev NoRegisters (_ : Nat) := Empty

def inputs : Interface Input where
  size := 1
  signal _ := ⟨32, .instruction⟩
  position _ := 0
  signal_position p := by cases p; rfl
  label _ := "instruction"
  unique a b _ := Fin.ext (by omega)

def registers : Interface NoRegisters where
  size := 0
  signal k := Fin.elim0 k
  position r := nomatch r
  signal_position r := nomatch r
  label r := nomatch r
  unique a := Fin.elim0 a

def circuit : Circuit Input NoRegisters Field where
  next r := nomatch r
  output := bundle (.input .instruction)

theorem circuit_correct (i : Values Input) (s : Values NoRegisters) (field : Field b) :
    circuit.observe i s field = expected (i .instruction) field := bundle_eval _ _ _ _

end Pinwheel.Hardware.Processor.RV32I.DecodeCircuit
