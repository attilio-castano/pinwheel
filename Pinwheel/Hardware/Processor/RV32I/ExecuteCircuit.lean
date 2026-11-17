import Pinwheel.Hardware.Processor.RV32I.DecodeCircuit
import Pinwheel.Hardware.Processor.RV32I.ALU

/-! Combinational RV32I execution from a raw instruction, PC, and two pre-edge
register operands. This block produces a result; it does not produce a clocked
retirement pulse or perform memory/device effects. Fetch alignment/access, request
ownership, accepted replies, and FENCE service remain controller obligations.

Class codes: retire0/load1/store2/fence3/trap4. Codes5..7 are never produced.
Trap codes: illegal0/ECALL1/EBREAK2/taken-target-misalignment3. All inactive fields
are zero, including nextPC outside retirement and writeRd/writeData when the
write enable is zero. A load to x0 remains a full pending load.
-/
namespace Pinwheel.Hardware.Processor.RV32I.ExecuteCircuit

inductive Field : Nat → Type where
  | classification : Field 3
  | nextPC : Field 32
  | writeEnable : Field 1
  | writeRd : Field 5
  | writeData : Field 32
  | address : Field 32
  | size : Field 2
  | signedLoad : Field 1
  | storeData : Field 32
  | loadRd : Field 5
  | trapCause : Field 2
  | trapTarget : Field 32
  deriving DecidableEq

structure Result where
  classification : BitVec 3 := 0
  nextPC : Word := 0
  writeEnable : BitVec 1 := 0
  writeRd : Register := 0
  writeData : Word := 0
  address : Word := 0
  size : BitVec 2 := 0
  signedLoad : BitVec 1 := 0
  storeData : Word := 0
  loadRd : Register := 0
  trapCause : BitVec 2 := 0
  trapTarget : Word := 0
  deriving DecidableEq, Repr

def Result.values (r : Result) : Values Field
  | _, .classification => r.classification | _, .nextPC => r.nextPC
  | _, .writeEnable => r.writeEnable | _, .writeRd => r.writeRd | _, .writeData => r.writeData
  | _, .address => r.address | _, .size => r.size | _, .signedLoad => r.signedLoad
  | _, .storeData => r.storeData | _, .loadRd => r.loadRd
  | _, .trapCause => r.trapCause | _, .trapTarget => r.trapTarget

def Result.ofValues (v : Values Field) : Result :=
  ⟨v .classification, v .nextPC, v .writeEnable, v .writeRd, v .writeData,
    v .address, v .size, v .signedLoad, v .storeData, v .loadRd, v .trapCause, v .trapTarget⟩

def retired (pc : Word) (dest : Register) (data : Word) : Result :=
  {nextPC := pc, writeEnable := BitVec.ofBool (dest != 0),
    writeRd := if dest = 0 then 0 else dest, writeData := if dest = 0 then 0 else data}

def trapped (cause : BitVec 2) (target : Word := 0) : Result :=
  {classification := 4, trapCause := cause, trapTarget := target}

def sizeCode : Memory.ByteAccess.Size → BitVec 2
  | .byte => 0 | .half => 1 | .word => 2

def loading (op : LoadOp) (dest : Register) (address : Word) : Result :=
  {classification := 1, address := address, size := sizeCode (Semantics.loadSize op),
    signedLoad := BitVec.ofBool (Semantics.loadSigned op), loadRd := dest}

def storing (op : StoreOp) (address operand : Word) : Result :=
  {classification := 2, address := address, size := sizeCode (Semantics.storeSize op), storeData := operand}

def fencing : Result := {classification := 3}

/-- Projection of the actual instruction semantics. Delayed data faults are
outside combinational execution and use reserved class7 in this total helper;
`Semantics.step` never returns those outcomes, as the correspondence proves. -/
def project : Semantics.Outcome → Result
  | .retired context after =>
      let dest := DecodeCircuit.instructionRd context.instruction
      retired after.pc dest (Semantics.read after.registers dest)
  | .pending (.load _ op dest address) => loading op dest address
  | .pending (.store _ op address operand) => storing op address operand
  | .pending (.fence _) => fencing
  | .trapped _ _ .illegalInstruction => trapped 0
  | .trapped _ _ .environmentCall => trapped 1
  | .trapped _ _ .breakpoint => trapped 2
  | .trapped _ _ (.instructionAddressMisaligned target) => trapped 3 target
  | .trapped _ _ _ => {classification := 7}

abbrev Bundle (I R : Nat → Type) := {b : Nat} → Field b → Expr I R b

def constant (value : Result) : Bundle I R := fun field => .lit (value.values field)

def retireExpr (pc : Expr I R 32) (dest : Expr I R 5) (data : Expr I R 32) : Bundle I R
  | _, .nextPC => pc
  | _, .writeEnable => .inv (.zero dest)
  | _, .writeRd => .mux (.zero dest) (.lit 0) dest
  | _, .writeData => .mux (.zero dest) (.lit 0) data
  | _, _ => .lit 0

def trapExpr (cause : BitVec 2) (target : Expr I R 32) : Bundle I R
  | _, .classification => .lit 4
  | _, .trapCause => .lit cause
  | _, .trapTarget => target
  | _, _ => .lit 0

def loadExpr (op : LoadOp) (dest : Expr I R 5) (address : Expr I R 32) : Bundle I R
  | _, .classification => .lit 1
  | _, .address => address
  | _, .size => .lit (sizeCode (Semantics.loadSize op))
  | _, .signedLoad => .lit (BitVec.ofBool (Semantics.loadSigned op))
  | _, .loadRd => dest
  | _, _ => .lit 0

def storeExpr (op : StoreOp) (address data : Expr I R 32) : Bundle I R
  | _, .classification => .lit 2
  | _, .address => address
  | _, .size => .lit (sizeCode (Semantics.storeSize op))
  | _, .storeData => data
  | _, _ => .lit 0

def mux (condition : Expr I R 1) (yes no : Bundle I R) : Bundle I R :=
  fun field => .mux condition (yes field) (no field)

def jumpExpr (target link : Expr I R 32) (dest : Expr I R 5) : Bundle I R :=
  mux (.zero (.slice 0 2 (by decide) target)) (retireExpr target dest link) (trapExpr 3 target)

def branchExpr (op : BranchOp) (left right : Expr I R 32) : Expr I R 1 :=
  match op with
  | .eq => .equal left right
  | .ne => .inv (.equal left right)
  | .lt => WordOps.signedLess left right
  | .ge => .inv (WordOps.signedLess left right)
  | .ltu => .ult left right
  | .geu => .inv (.ult left right)

def row (word pc left right : Expr I R 32) (kind : DecodeCircuit.Kind) : Bundle I R :=
  let dest : Expr I R 5 := .slice 7 5 (by decide) word
  let immediate : Expr I R 12 := .slice 20 12 (by decide) word
  let amount : Expr I R 5 := .slice 20 5 (by decide) word
  let next := WordOps.add pc (.lit 4)
  let offset := DecodeCircuit.immediateExpr word kind
  match kind with
  | .lui => retireExpr next dest offset
  | .auipc => retireExpr next dest (WordOps.add pc offset)
  | .jal => jumpExpr (WordOps.add pc offset) next dest
  | .jalr => jumpExpr (.band (WordOps.add left offset) (.lit 0xfffffffe)) next dest
  | .beq => mux (branchExpr .eq left right) (jumpExpr (WordOps.add pc offset) (.lit 0) (.lit 0)) (retireExpr next (.lit 0) (.lit 0))
  | .bne => mux (branchExpr .ne left right) (jumpExpr (WordOps.add pc offset) (.lit 0) (.lit 0)) (retireExpr next (.lit 0) (.lit 0))
  | .blt => mux (branchExpr .lt left right) (jumpExpr (WordOps.add pc offset) (.lit 0) (.lit 0)) (retireExpr next (.lit 0) (.lit 0))
  | .bge => mux (branchExpr .ge left right) (jumpExpr (WordOps.add pc offset) (.lit 0) (.lit 0)) (retireExpr next (.lit 0) (.lit 0))
  | .bltu => mux (branchExpr .ltu left right) (jumpExpr (WordOps.add pc offset) (.lit 0) (.lit 0)) (retireExpr next (.lit 0) (.lit 0))
  | .bgeu => mux (branchExpr .geu left right) (jumpExpr (WordOps.add pc offset) (.lit 0) (.lit 0)) (retireExpr next (.lit 0) (.lit 0))
  | .lb => loadExpr .byte dest (WordOps.add left offset)
  | .lh => loadExpr .half dest (WordOps.add left offset)
  | .lw => loadExpr .word dest (WordOps.add left offset)
  | .lbu => loadExpr .byteUnsigned dest (WordOps.add left offset)
  | .lhu => loadExpr .halfUnsigned dest (WordOps.add left offset)
  | .sb => storeExpr .byte (WordOps.add left offset) right
  | .sh => storeExpr .half (WordOps.add left offset) right
  | .sw => storeExpr .word (WordOps.add left offset) right
  | .addi => retireExpr next dest (ALU.immediate .add left immediate)
  | .slti => retireExpr next dest (ALU.immediate .slt left immediate)
  | .sltiu => retireExpr next dest (ALU.immediate .sltu left immediate)
  | .xori => retireExpr next dest (ALU.immediate .bitXor left immediate)
  | .ori => retireExpr next dest (ALU.immediate .bitOr left immediate)
  | .andi => retireExpr next dest (ALU.immediate .bitAnd left immediate)
  | .slli => retireExpr next dest (ALU.shiftImmediate .left left amount)
  | .srli => retireExpr next dest (ALU.shiftImmediate .rightLogical left amount)
  | .srai => retireExpr next dest (ALU.shiftImmediate .rightArithmetic left amount)
  | .add => retireExpr next dest (ALU.register .add left right)
  | .sub => retireExpr next dest (ALU.register .sub left right)
  | .sll => retireExpr next dest (ALU.register .sll left right)
  | .slt => retireExpr next dest (ALU.register .slt left right)
  | .sltu => retireExpr next dest (ALU.register .sltu left right)
  | .bitXor => retireExpr next dest (ALU.register .bitXor left right)
  | .srl => retireExpr next dest (ALU.register .srl left right)
  | .sra => retireExpr next dest (ALU.register .sra left right)
  | .bitOr => retireExpr next dest (ALU.register .bitOr left right)
  | .bitAnd => retireExpr next dest (ALU.register .bitAnd left right)
  | .fence => constant fencing
  | .ecall => trapExpr 1 (.lit 0)
  | .ebreak => trapExpr 2 (.lit 0)

def bundle (word pc left right : Expr I R 32) : Bundle I R := fun field =>
  .mux (DecodeCircuit.bundle word .valid)
    (DecodeCircuit.select word (fun kind => row word pc left right kind field) DecodeCircuit.kinds)
    (constant (trapped 0) field)

inductive Input : Nat → Type where
  | instruction : Input 32
  | pc : Input 32
  | operand1 : Input 32
  | operand2 : Input 32

abbrev NoRegisters (_ : Nat) := Empty

def inputs : Interface Input where
  size := 4
  signal k := match k with
    | ⟨0, _⟩ => ⟨32, .instruction⟩ | ⟨1, _⟩ => ⟨32, .pc⟩
    | ⟨2, _⟩ => ⟨32, .operand1⟩ | ⟨3, _⟩ => ⟨32, .operand2⟩
    | ⟨n+4, h⟩ => False.elim (by omega)
  position p := match p with | .instruction => 0 | .pc => 1 | .operand1 => 2 | .operand2 => 3
  signal_position p := by cases p <;> rfl
  label p := match p with | .instruction => "instruction" | .pc => "pc" | .operand1 => "operand1" | .operand2 => "operand2"
  unique := by decide +kernel

def outputs : Interface Field where
  size := 12
  signal k := match k with
    | ⟨0, _⟩ => ⟨3, .classification⟩
    | ⟨1, _⟩ => ⟨32, .nextPC⟩
    | ⟨2, _⟩ => ⟨1, .writeEnable⟩
    | ⟨3, _⟩ => ⟨5, .writeRd⟩
    | ⟨4, _⟩ => ⟨32, .writeData⟩
    | ⟨5, _⟩ => ⟨32, .address⟩
    | ⟨6, _⟩ => ⟨2, .size⟩
    | ⟨7, _⟩ => ⟨1, .signedLoad⟩
    | ⟨8, _⟩ => ⟨32, .storeData⟩
    | ⟨9, _⟩ => ⟨5, .loadRd⟩
    | ⟨10, _⟩ => ⟨2, .trapCause⟩
    | ⟨11, _⟩ => ⟨32, .trapTarget⟩
    | ⟨n+12, h⟩ => False.elim (by omega)
  position p := match p with
    | .classification => 0
    | .nextPC => 1
    | .writeEnable => 2
    | .writeRd => 3
    | .writeData => 4
    | .address => 5
    | .size => 6
    | .signedLoad => 7
    | .storeData => 8
    | .loadRd => 9
    | .trapCause => 10
    | .trapTarget => 11
  signal_position p := by cases p <;> rfl
  label p := match p with
    | .classification => "classification"
    | .nextPC => "next_pc"
    | .writeEnable => "write_enable"
    | .writeRd => "write_rd"
    | .writeData => "write_data"
    | .address => "address"
    | .size => "size"
    | .signedLoad => "signed_load"
    | .storeData => "store_data"
    | .loadRd => "load_rd"
    | .trapCause => "trap_cause"
    | .trapTarget => "trap_target"
  unique := by decide +kernel

def registers : Interface NoRegisters where
  size := 0
  signal k := Fin.elim0 k
  position r := nomatch r
  signal_position r := nomatch r
  label r := nomatch r
  unique a := Fin.elim0 a

def circuit : Circuit Input NoRegisters Field where
  next r := nomatch r
  output := bundle (.input .instruction) (.input .pc) (.input .operand1) (.input .operand2)

end Pinwheel.Hardware.Processor.RV32I.ExecuteCircuit
