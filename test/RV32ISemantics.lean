import Lean
import Pinwheel.Hardware.Processor.RV32I.Semantics

open Lean Elab Command Pinwheel.Hardware.Processor.RV32I
open Pinwheel.Hardware.Processor.RV32I.Semantics
namespace RV32ISemanticsTests

def modulus : Nat := 2^32
def signed32 (n : Nat) : Int := if n < 2^31 then Int.ofNat n else Int.ofNat n - 2^32
def wrap (n : Int) : Nat := (n % (2^32 : Int)).toNat
def extend (n width : Nat) : Nat := if n < 2^(width-1) then n else n+modulus-2^width
def registerRead (bank : Array Nat) (index : Register) : Nat := if index.toNat = 0 then 0 else bank[index.toNat]!
def registerWrite (bank : Array Nat) (index value : Nat) : Array Nat := if index = 0 then bank else bank.set! index value

def physicalState (pc : Nat) (bank : Array Nat) : Semantics.State :=
  ⟨BitVec.ofNat 32 pc, fun k => BitVec.ofNat 32 bank[k.val+1]!⟩
def stateBank (state : Semantics.State) : Array Nat := Array.ofFn fun k : Fin 32 => (read state.registers (BitVec.ofFin k)).toNat

structure Expected where
  tag : Nat
  pc : Nat
  bank : Array Nat
  detail : Array Nat
  deriving DecidableEq, Repr

def pendingDetail (pending : Pending) : Array Nat :=
  let dest := match pending with | .load _ _ d _ => d.toNat | _ => 0
  match pending.intent with
  | .load address size signed => #[0, address.toNat, size.bytes, if signed then 1 else 0, dest, 0]
  | .store address size data => #[1, address.toNat, size.bytes, 0, 0, data.toNat]
  | .fenceAll => #[2, 0, 0, 0, 0, 0]

def trapDetail : Trap → Array Nat
  | .illegalInstruction => #[0, 0]
  | .environmentCall => #[1, 0]
  | .breakpoint => #[2, 0]
  | .instructionAddressMisaligned target => #[3, target.toNat]
  | .loadFault .misaligned address => #[4, address.toNat]
  | .loadFault .accessFault address => #[5, address.toNat]
  | .storeFault .misaligned address => #[6, address.toNat]
  | .storeFault .accessFault address => #[7, address.toNat]

def observe (outcome : Outcome) : Expected :=
  let state := outcome.state
  match outcome with
  | .retired _ _ => ⟨0, state.pc.toNat, stateBank state, #[]⟩
  | .pending pending => ⟨1, state.pc.toNat, stateBank state, pendingDetail pending⟩
  | .trapped _ _ reason => ⟨2, state.pc.toNat, stateBank state, trapDetail reason⟩

def immALU (op : ImmediateOp) (left raw : Nat) : Nat :=
  let right := extend raw 12
  match op with
  | .add => (left+right)%modulus
  | .slt => if signed32 left < signed32 right then 1 else 0
  | .sltu => if left < right then 1 else 0
  | .bitXor => Nat.xor left right
  | .bitOr => Nat.lor left right
  | .bitAnd => Nat.land left right

def shifted (op : ShiftOp) (value amount : Nat) : Nat :=
  match op with
  | .left => value * 2^amount % modulus
  | .rightLogical => value / 2^amount
  | .rightArithmetic => wrap (signed32 value / (2^amount : Int))

def regALU (op : RegisterOp) (left right : Nat) : Nat :=
  match op with
  | .add => (left+right)%modulus
  | .sub => (left+modulus-right)%modulus
  | .sll => shifted .left left (right%32)
  | .srl => shifted .rightLogical left (right%32)
  | .sra => shifted .rightArithmetic left (right%32)
  | .slt => if signed32 left < signed32 right then 1 else 0
  | .sltu => if left < right then 1 else 0
  | .bitXor => Nat.xor left right
  | .bitOr => Nat.lor left right
  | .bitAnd => Nat.land left right

def branch (op : BranchOp) (left right : Nat) : Bool :=
  match op with
  | .eq => left == right | .ne => left != right
  | .lt => signed32 left < signed32 right | .ge => signed32 left ≥ signed32 right
  | .ltu => left < right | .geu => left ≥ right

/-- Independent integer/array execution, without production ALU, target,
register, immediate-value, or completion helpers. It starts from the typed
instruction, whose separate decoder campaign checks the raw encoding layer. -/
def reference (pc : Nat) (rawBank : Array Nat) (instruction : Instruction) : Expected :=
  let bank := rawBank.set! 0 0
  let sequential := (pc+4)%modulus
  let retire := fun dest value => Expected.mk 0 sequential (registerWrite bank dest value) #[]
  let transfer := fun target link =>
    if target%4 ≠ 0 then Expected.mk 2 pc bank #[3, target]
    else Expected.mk 0 target (match link with | none => bank | some dest => registerWrite bank dest sequential) #[]
  match instruction with
  | .lui dest upper => retire dest.toNat (upper.toNat*4096)
  | .auipc dest upper => retire dest.toNat ((pc+upper.toNat*4096)%modulus)
  | .jal dest offset => transfer ((pc+extend (offset.toNat*2) 21)%modulus) (some dest.toNat)
  | .jalr dest source immediate =>
    let target := ((registerRead bank source+extend immediate.toNat 12)%modulus)/2*2
    transfer target (some dest.toNat)
  | .branch op first second offset =>
    if branch op (registerRead bank first) (registerRead bank second) then
      transfer ((pc+extend (offset.toNat*2) 13)%modulus) none else retire 0 0
  | .load op dest source immediate =>
    let size := match op with | .byte | .byteUnsigned => 1 | .half | .halfUnsigned => 2 | .word => 4
    let signed := match op with | .byte | .half => 1 | _ => 0
    ⟨1, pc, bank, #[0, (registerRead bank source+extend immediate.toNat 12)%modulus, size, signed, dest.toNat, 0]⟩
  | .store op source operand immediate =>
    let size := match op with | .byte => 1 | .half => 2 | .word => 4
    ⟨1, pc, bank, #[1, (registerRead bank source+extend immediate.toNat 12)%modulus, size, 0, 0, registerRead bank operand]⟩
  | .aluImm op dest source immediate => retire dest.toNat (immALU op (registerRead bank source) immediate.toNat)
  | .shiftImm op dest source amount => retire dest.toNat (shifted op (registerRead bank source) amount.toNat)
  | .aluReg op dest first second => retire dest.toNat (regALU op (registerRead bank first) (registerRead bank second))
  | .fence _ _ _ _ _ => ⟨1, pc, bank, #[2, 0, 0, 0, 0, 0]⟩
  | .ecall => ⟨2, pc, bank, #[1, 0]⟩
  | .ebreak => ⟨2, pc, bank, #[2, 0]⟩

def responseReference (before : Expected) (fault : Option Nat) (data : Nat) : Expected :=
  let kind := before.detail[0]!
  match fault with
  | some reason => ⟨2, before.pc, before.bank, #[4+kind*2+reason, before.detail[1]!]⟩
  | none =>
    let bank := if kind = 0 then
      let bits := before.detail[2]!*8
      let selected := data % 2^bits
      let value := if before.detail[3]! = 1 then extend selected bits else selected
      registerWrite before.bank before.detail[4]! value else before.bank
    ⟨0, (before.pc+4)%modulus, bank, #[]⟩

def reply (pending : Pending) (fault : Option Nat) (data : Nat) : Reply pending :=
  match pending, fault with
  | .load _ _ _ _, none => .loaded (BitVec.ofNat 32 data)
  | .load _ _ _ _, some reason => .loadFault (if reason = 0 then .misaligned else .accessFault)
  | .store _ _ _ _, none => .stored
  | .store _ _ _ _, some reason => .storeFault (if reason = 0 then .misaligned else .accessFault)
  | .fence _, _ => .fenced

def check (pc : Nat) (bank : Array Nat) (instruction : Instruction) (data : Nat) : IO Nat := do
  let state := physicalState pc bank
  let expected := reference pc bank instruction
  let actual := execute state instruction
  let raw := encode instruction
  unless observe actual = expected do throw (IO.userError s!"Execution mismatch: {repr instruction}; expected {repr expected}, got {repr (observe actual)}")
  unless observe (step state raw) = expected && actual.word = raw && stateBank actual.origin = bank.set! 0 0 &&
      actual.origin.pc.toNat = pc do throw (IO.userError "Raw instruction/origin identity changed")
  let mut checks := 1
  match actual with
  | .pending pending =>
    let faults := if expected.detail[0]! = 2 then [none] else [none, some 0, some 1]
    for fault in faults do
      let result := reply pending fault data
      for ready in [false, true] do
        for valid in [false, true] do
          let completed := respond pending ready (if valid then some result else none)
          let wanted := if ready && valid then responseReference expected fault data else expected
          unless observe completed = wanted && completed.word = raw && stateBank completed.origin = bank.set! 0 0 &&
              completed.origin.pc.toNat = pc do throw (IO.userError s!"Response commit/stall/fault mismatch for {repr instruction}")
          checks := checks+1
  | _ => pure ()
  return checks

def bank (left right seed : Nat) : Array Nat :=
  (Array.ofFn fun k : Fin 32 => (seed*1664525+k.val*0x10204081+0x80ff7f01)%modulus).set! 1 left |>.set! 2 right

def registerOps : List RegisterOp := [.add, .sub, .sll, .slt, .sltu, .bitXor, .srl, .sra, .bitOr, .bitAnd]
def immediateOps : List ImmediateOp := [.add, .slt, .sltu, .bitXor, .bitOr, .bitAnd]
def branchOps : List BranchOp := [.eq, .ne, .lt, .ge, .ltu, .geu]
def loadOps : List LoadOp := [.byte, .half, .word, .byteUnsigned, .halfUnsigned]
def storeOps : List StoreOp := [.byte, .half, .word]
def boundary : List Nat := [0, 1, 2, 3, 31, 32, 63, 127, 128, 32768, 0x7fffffff, 0x80000000, 0xffffffff]

def campaign : IO Nat := do
  let mut checks := 0
  for left in boundary do
    for right in boundary do
      for op in registerOps do
        for dest in [0, 5] do checks := checks+(← check 0xfffffffc (bank left right 7) (.aluReg op dest 1 2) 0)
      for op in branchOps do
        for offset in [0, 1, 2, 2047, 2048, 4095] do
          checks := checks+(← check 0x1000 (bank left right 11) (.branch op 1 2 (BitVec.ofNat 12 offset)) 0)
  for immediate in [:4096] do
    for op in immediateOps do
      checks := checks+(← check (if immediate%2 = 0 then 0xfffffffc else 0x1000)
        (bank (boundary[immediate%boundary.length]!) 0 immediate)
        (.aluImm op (BitVec.ofNat 5 (immediate%32)) 1 (BitVec.ofNat 12 immediate)) 0)
  for value in boundary do
    for amount in [:32] do
      for op in [ShiftOp.left, .rightLogical, .rightArithmetic] do
        for dest in [0, 5] do checks := checks+(← check 0 (bank value 0 amount) (.shiftImm op dest 1 (BitVec.ofNat 5 amount)) 0)
  for base in boundary ++ [0x1000, 0x1001, 0x1002, 0x1003, 0xfffffffc] do
    for imm in [0, 1, 2, 3, 2047, 2048, 4095] do
      for dest in [0, 5] do
        checks := checks+(← check 0xfffffffc (bank base 0 imm) (.jalr dest 1 (BitVec.ofNat 12 imm)) 0)
        for op in loadOps do
          for data in [0, 0x80, 0x8000, 0x80000000, 0xffffffff] do
            checks := checks+(← check 0xfffffffc (bank base 0 imm) (.load op dest 1 (BitVec.ofNat 12 imm)) data)
      for op in storeOps do checks := checks+(← check 0x1000 (bank base 0xdeadbeef imm) (.store op 1 2 (BitVec.ofNat 12 imm)) 0)
  for pc in [0, 0x1000, 0xfffffffc] do
    for bits in [0, 1, 2, 1024, 2048, 0x7ffff, 0x80000, 0xfffff] do
      for dest in [0, 5] do
        checks := checks+(← check pc (bank 1 2 bits) (.jal dest (BitVec.ofNat 20 bits)) 0)
        checks := checks+(← check pc (bank 1 2 bits) (.lui dest (BitVec.ofNat 20 bits)) 0)
        checks := checks+(← check pc (bank 1 2 bits) (.auipc dest (BitVec.ofNat 20 bits)) 0)
    for mode in [:16] do
      checks := checks+(← check pc (bank 1 2 mode) (.fence 31 17 (BitVec.ofNat 4 mode) 0 15) 0)
    checks := checks+(← check pc (bank 1 2 3) .ecall 0)
    checks := checks+(← check pc (bank 1 2 3) .ebreak 0)
  let mut seed : Nat := 0x73656d61
  for cycle in [:10000] do
    seed := (1664525*seed+1013904223)%modulus
    let registers := bank seed ((seed*1103515245+12345)%modulus) cycle
    let dest := BitVec.ofNat 5 (seed%32)
    let source := BitVec.ofNat 5 (seed/32%32)
    let imm := BitVec.ofNat 12 (seed/64%4096)
    let instruction := match cycle%6 with
      | 0 => Instruction.aluReg (registerOps[seed%10]?.getD .add) dest source 2
      | 1 => .aluImm (immediateOps[seed%6]?.getD .add) dest source imm
      | 2 => .branch (branchOps[seed%6]?.getD .eq) source 2 imm
      | 3 => .load (loadOps[seed%5]?.getD .byte) dest source imm
      | 4 => .store (storeOps[seed%3]?.getD .byte) source 2 imm
      | _ => .jalr dest source imm
    checks := checks+(← check (seed/4*4) registers instruction (seed ^^^ 0xa5807fff))
  for word in [0, 1, 0xffffffff, 0x02000033, 0x0000100f, 0x00101073] do
    let state := physicalState 0xfffffffc (bank 1 2 3)
    let actual := step state (BitVec.ofNat 32 word)
    unless observe actual = Expected.mk 2 0xfffffffc (stateBank state) #[0, 0] && actual.word.toNat = word do
      throw (IO.userError "Illegal raw instruction did not trap precisely")
    checks := checks+1
  -- Destination/source overlap must still use pre-instruction operands; a
  -- pending load captures its address before later overwriting the base register.
  for instruction in [Instruction.jalr 1 1 0, .aluReg .add 1 1 2,
      .aluImm .add 1 1 1, .load .word 1 1 0, .store .word 1 1 0] do
    checks := checks+(← check 0x1000 (bank 0x2001 0xffffffff 73) instruction 0xaabbccdd)
  return checks

def context (state : Semantics.State) (instruction : Instruction) : Semantics.Context :=
  ⟨state, encode instruction, instruction, decode_encode instruction⟩

/-- Actual alternative semantic functions, each with one targeted defect. -/
def mutant (mode : Nat) (c : Semantics.Context) : Outcome :=
  match mode, c.instruction with
  | 0, .jalr dest source imm => transfer c (read c.state.registers source+signedImmediate imm) (some dest)
  | 1, .branch _ _ _ offset => transfer c (c.state.pc+branchOffset offset) none
  | 2, .load _ 0 _ _ => .retired c (next c.state)
  | 3, .aluReg .sll dest first second => .retired c (writeNext c.state dest
      (read c.state.registers first <<< (read c.state.registers second).toNat))
  | 4, .shiftImm .rightArithmetic dest source amount => .retired c (writeNext c.state dest
      (read c.state.registers source >>> amount.toNat))
  | 5, .aluImm .sltu dest source imm => .retired c (writeNext c.state dest
      (if (read c.state.registers source).toNat < imm.toNat then 1 else 0))
  | 6, .fence _ _ _ _ _ => .retired c (next c.state)
  | 7, .jal dest offset =>
    match transfer c (c.state.pc+jumpOffset offset) (some dest) with
    | .trapped _ _ reason => .trapped
        {c.state with registers := write c.state.registers dest (c.state.pc+4)} c.word reason
    | other => other
  | 8, .aluImm op dest 0 imm => .retired c (writeNext c.state dest
      (immediateALU op (c.state.registers ⟨0, by decide⟩) imm))
  | 9, .load op dest source imm => .pending (.load {c with state := next c.state}
      op dest (effectiveAddress c.state source imm))
  | _, _ => executeContext c

def mutationFixture (mode pc left right : Nat) (instruction : Instruction) : IO Unit := do
  let registers := bank left right 17
  let c := context (physicalState pc registers) instruction
  let expected := reference pc registers instruction
  unless observe (executeContext c) = expected do throw (IO.userError "Invalid positive mutation fixture")
  unless observe (mutant mode c) ≠ expected do throw (IO.userError s!"Semantic mutation {mode} escaped")

def mutationControls : IO Nat := do
  mutationFixture 0 0x1000 0x2001 0 (.jalr 5 1 0)
  mutationFixture 1 0x1000 1 2 (.branch .eq 1 2 1)
  mutationFixture 2 0x1000 0x10000000 0 (.load .word 0 1 0)
  mutationFixture 3 0x1000 1 32 (.aluReg .sll 5 1 2)
  mutationFixture 4 0x1000 0x80000000 0 (.shiftImm .rightArithmetic 5 1 1)
  mutationFixture 5 0x1000 4096 0 (.aluImm .sltu 5 1 4095)
  mutationFixture 6 0x1000 0 0 (.fence 31 17 15 3 3)
  mutationFixture 7 0x1000 0 0 (.jal 5 1)
  mutationFixture 8 0x1000 0x12345678 0 (.aluImm .add 5 0 0)
  mutationFixture 9 0x1000 0 0 (.load .byte 5 1 0)
  let registers := bank 0x10000000 0 29
  let c := context (physicalState 0xfffffffc registers) (.load .byte 5 1 0)
  let pending := Pending.load c .byte 5 0x10000000
  let expected := reference 0xfffffffc registers c.instruction
  let loaded := finish pending (.loaded 0x80)
  unless observe loaded = responseReference expected none 0x80 do throw (IO.userError "Bad load-extension fixture")
  let zeroExtended := Outcome.retired c (writeNext c.state 5 0x80)
  unless observe zeroExtended ≠ observe loaded do throw (IO.userError "Missing load sign extension escaped")
  let failed := finish pending (.loadFault .accessFault)
  unless observe failed = responseReference expected (some 1) 0 do throw (IO.userError "Bad fault fixture")
  let advancedFault := Outcome.trapped (next c.state) c.word (.loadFault .accessFault 0x10000000)
  unless observe advancedFault ≠ observe failed do throw (IO.userError "Fault advanced the PC")
  unless observe loaded ≠ observe (respond pending false (some (.loaded 0x80))) do
    throw (IO.userError "Unaccepted response changed architecture")
  return 13

end RV32ISemanticsTests

elab "#audit_rv32i_semantics" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.RV32I.Semantics." ||
        name.toString.startsWith "RV32ISemanticsTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved RV32I semantics axioms in {name}: {bad}"
  if count < 100 then throwError "Incomplete RV32I semantics audit"
  logInfo m!"RV32I semantics audit: {count} declarations, standard axioms only."

#audit_rv32i_semantics

def main : IO Unit := do
  let checks ← RV32ISemanticsTests.campaign
  let mutations ← RV32ISemanticsTests.mutationControls
  IO.println s!"RV32I semantics: {checks} independent integer/array instruction and response checks; {mutations} semantic mutation controls rejected."
