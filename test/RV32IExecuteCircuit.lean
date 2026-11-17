import Lean
import Pinwheel.Hardware.Processor.RV32I.ExecuteCircuitProofs

open Lean Elab Command Pinwheel.Hardware
open Pinwheel.Hardware.Processor.RV32I.ExecuteCircuit
namespace RV32IExecuteCircuitTests

def modulus : Nat := 2^32
def field (word start width : Nat) : Nat := word / 2^start % 2^width
def extend (value width : Nat) : Nat :=
  if value < 2^(width-1) then value else value+modulus-2^width
def signed (value : Nat) : Int := if value < 2^31 then value else (value : Int)-2^32
def wrap (value : Int) : Nat := (value % (2^32 : Int)).toNat
def bit (value : Bool) : Nat := if value then 1 else 0

structure Decoded where
  kind : Nat
  dest : Nat
  source1 : Nat
  source2 : Nat
  immediate : Nat
  deriving Repr, Inhabited

/-- Independent integer opcode/format decoder. No production Instruction,
decoder, kind enumeration, immediate helper, semantics, ALU or Expr operation
participates in any expected value. Mnemonic IDs below are private test data. -/
def decodeReference (word : Nat) : Option Decoded := Id.run do
  let op := word%128
  let d := field word 7 5
  let a := field word 15 5
  let b := field word 20 5
  let f := field word 12 3
  let h := field word 25 7
  let imm := extend (field word 20 12) 12
  let result := fun kind immediate => some (Decoded.mk kind d a b immediate)
  match op with
  | 55 => return result 0 (word/4096*4096)
  | 23 => return result 1 (word/4096*4096)
  | 111 => return result 2 (extend (field word 31 1*2^20 + field word 12 8*2^12 + field word 20 1*2^11 + field word 21 10*2) 21)
  | 103 => return if f = 0 then result 3 imm else none
  | 99 =>
    let some id := (match f with | 0 => some 4 | 1 => some 5 | 4 => some 6 | 5 => some 7 | 6 => some 8 | 7 => some 9 | _ => none) | return none
    return result id (extend (field word 31 1*4096 + field word 7 1*2048 + field word 25 6*32 + field word 8 4*2) 13)
  | 3 =>
    let some id := (match f with | 0 => some 10 | 1 => some 11 | 2 => some 12 | 4 => some 13 | 5 => some 14 | _ => none) | return none
    return result id imm
  | 35 => return if f < 3 then result (15+f) (extend (h*32+d) 12) else none
  | 19 =>
    match f with
    | 0 => return result 18 imm
    | 2 => return result 19 imm
    | 3 => return result 20 imm
    | 4 => return result 21 imm
    | 6 => return result 22 imm
    | 7 => return result 23 imm
    | 1 => return if h = 0 then result 24 b else none
    | 5 => return if h = 0 then result 25 b else if h = 32 then result 26 b else none
    | _ => return none
  | 51 =>
    let some id := (match h, f with
      | 0, 0 => some 27 | 32, 0 => some 28 | 0, 1 => some 29 | 0, 2 => some 30
      | 0, 3 => some 31 | 0, 4 => some 32 | 0, 5 => some 33 | 32, 5 => some 34
      | 0, 6 => some 35 | 0, 7 => some 36 | _, _ => none) | return none
    return result id 0
  | 15 => return if f = 0 then result 37 0 else none
  | 115 => return if word = 115 then result 38 0 else if word = 1048691 then result 39 0 else none
  | _ => return none

def retire (pc dest value : Nat) : Array Nat :=
  #[0,pc%modulus,bit (dest != 0),dest,if dest = 0 then 0 else value%modulus,0,0,0,0,0,0,0]
def trap (cause : Nat) (target : Nat := 0) : Array Nat := #[4,0,0,0,0,0,0,0,0,0,cause,target]
def jump (target dest link : Nat) : Array Nat :=
  if target%4 = 0 then retire target dest link else trap 3 target

def shiftLeft (left amount : Nat) : Nat := left*2^amount%modulus
def shiftRight (left amount : Nat) : Nat := left/2^amount
def arithmeticRight (left amount : Nat) : Nat := wrap (signed left / (2^amount : Int))

/-- Raw-port reference. Operand pins are used literally; register-array tests
below separately establish coherent pre-edge x0/source/overlap inputs. Memory
alignment is deliberately not checked here: this block issues an intent. -/
def reference (word pc left right : Nat) : Array Nat :=
  match decodeReference word with
  | none => trap 0
  | some d =>
    let sequential := (pc+4)%modulus
    let result := fun value => retire sequential d.dest value
    let address := (left+d.immediate)%modulus
    match d.kind with
    | 0 => result d.immediate
    | 1 => result ((pc+d.immediate)%modulus)
    | 2 => jump ((pc+d.immediate)%modulus) d.dest sequential
    | 3 => jump (address/2*2) d.dest sequential
    | 4 | 5 | 6 | 7 | 8 | 9 =>
      let taken := match d.kind with
        | 4 => left == right | 5 => left != right
        | 6 => signed left < signed right | 7 => signed left ≥ signed right
        | 8 => left < right | _ => left ≥ right
      if taken then jump ((pc+d.immediate)%modulus) 0 0 else retire sequential 0 0
    | 10 | 11 | 12 | 13 | 14 =>
      let size := if d.kind = 10 || d.kind = 13 then 0 else if d.kind = 12 then 2 else 1
      #[1,0,0,0,0,address,size,bit (d.kind = 10 || d.kind = 11),0,d.dest,0,0]
    | 15 | 16 | 17 => #[2,0,0,0,0,address,d.kind-15,0,right,0,0,0]
    | 18 => result address
    | 19 => result (bit (signed left < signed d.immediate))
    | 20 => result (bit (left < d.immediate))
    | 21 => result (Nat.xor left d.immediate)
    | 22 => result (Nat.lor left d.immediate)
    | 23 => result (Nat.land left d.immediate)
    | 24 => result (shiftLeft left d.immediate)
    | 25 => result (shiftRight left d.immediate)
    | 26 => result (arithmeticRight left d.immediate)
    | 27 => result ((left+right)%modulus)
    | 28 => result ((left+modulus-right)%modulus)
    | 29 => result (shiftLeft left (right%32))
    | 30 => result (bit (signed left < signed right))
    | 31 => result (bit (left < right))
    | 32 => result (Nat.xor left right)
    | 33 => result (shiftRight left (right%32))
    | 34 => result (arithmeticRight left (right%32))
    | 35 => result (Nat.lor left right)
    | 36 => result (Nat.land left right)
    | 37 => #[3,0,0,0,0,0,0,0,0,0,0,0]
    | 38 => trap 1
    | 39 => trap 2
    | _ => trap 0

def pins (word pc left right : Nat) : Values Input
  | _, .instruction => BitVec.ofNat 32 word | _, .pc => BitVec.ofNat 32 pc
  | _, .operand1 => BitVec.ofNat 32 left | _, .operand2 => BitVec.ofNat 32 right
def noRegisters : Values NoRegisters := fun r => nomatch r

def expressions : Array (Sigma fun b => Expr Input NoRegisters b) :=
  outputs.ports.map fun ⟨b,f⟩ => ⟨b,circuit.output f⟩
def actual (word pc left right : Nat) : Array Nat :=
  expressions.map fun ⟨_,e⟩ => (e.eval (pins word pc left right) noRegisters).toNat

structure Coverage where
  checked : Nat := 0
  illegal : Nat := 0
  mnemonics : Array Bool := Array.replicate 40 false
  classes : Array Bool := Array.replicate 5 false
  loadZero : Nat := 0
  targetFault : Nat := 0

def check (word pc left right : Nat) (coverage : Coverage) : IO Coverage := do
  unless [word,pc,left,right].all (· < modulus) do throw (IO.userError "Raw oracle input overflow")
  let expected := reference word pc left right
  let observed := actual word pc left right
  unless observed = expected do
    throw (IO.userError s!"Execute mismatch word={word} pc={pc} left={left} right={right}: {observed} != {expected}")
  let c : Coverage := {
    coverage with
    checked := coverage.checked+1
    classes := coverage.classes.set! (expected[0]!) true
    loadZero := coverage.loadZero + bit (expected[0]! = 1 && expected[9]! = 0)
    targetFault := coverage.targetFault + bit (expected[0]! = 4 && expected[10]! = 3)}
  match decodeReference word with
  | none => return {c with illegal := c.illegal+1}
  | some d => return {c with mnemonics := c.mnemonics.set! d.kind true}

-- Independent raw instruction construction, without the production encoder.
def rWord (f high dest first second : Nat) : Nat := high*2^25+second*2^20+first*2^15+f*2^12+dest*128+51
def iWord (opcode f dest first imm : Nat) : Nat := imm*2^20+first*2^15+f*2^12+dest*128+opcode
def sWord (f first second imm : Nat) : Nat := imm/32*2^25+second*2^20+first*2^15+f*2^12+imm%32*128+35
def bWord (f first second halfOffset : Nat) : Nat :=
  halfOffset/2048*2^31+halfOffset/16%64*2^25+second*2^20+first*2^15+f*2^12+halfOffset%16*256+halfOffset/1024%2*128+99
def jWord (dest halfOffset : Nat) : Nat :=
  halfOffset/2^19*2^31+halfOffset%1024*2^21+halfOffset/1024%2*2^20+halfOffset/2048%256*4096+dest*128+111
def lcg (seed : Nat) : Nat := (1664525*seed+1013904223)%modulus
def boundaries : Array Nat := #[0,1,2,3,31,32,33,63,255,65535,0x7fffffff,0x80000000,0xfffffffe,0xffffffff]
def registerCodes : Array (Nat × Nat) := #[(0,0),(0,32),(1,0),(2,0),(3,0),(4,0),(5,0),(5,32),(6,0),(7,0)]

def campaign : IO Coverage := do
  let mut c : Coverage := {}
  -- Exhaust legal/reserved opcode/funct fields with arbitrary operand pins.
  for opcode in [:128] do
    for f in [:8] do
      for high in [:128] do
        let raw := high*2^25+(opcode*3+f)%32*2^20+(high+f)%32*2^15+f*4096+(opcode+high)%32*128+opcode
        c ← check raw ((high*0x10204081)%modulus) (lcg raw) (lcg (lcg raw)) c
  for left in boundaries do
    for right in boundaries do
      for (f,high) in registerCodes do
        for dest in [0,1,2,31] do c ← check (rWord f high dest 1 2) 0xfffffffc left right c
      for f in [0,1,4,5,6,7] do
        for offset in [0,1,2,2047,2048,4095] do c ← check (bWord f 1 2 offset) 0xfffffffc left right c
  -- Every immediate bit pattern, across arithmetic, memory and JALR.
  for imm in [:4096] do
    let left := boundaries[imm%boundaries.size]!
    let right := lcg imm
    let dest := imm%32
    for f in [0,2,3,4,6,7] do c ← check (iWord 19 f dest 1 imm) 0xfffffffc left right c
    for f in [0,1,2,4,5] do c ← check (iWord 3 f dest 1 imm) 0x100 left right c
    for f in [:3] do c ← check (sWord f 1 2 imm) 0x100 left right c
    c ← check (iWord 103 0 dest 1 imm) 0xfffffffc left right c
    c ← check (iWord 15 0 dest (imm/32%32) imm) 0x100 left right c
  for left in boundaries do
    for amount in [:32] do
      for (f,high) in [(1,0),(5,0),(5,32)] do
        for dest in [0,31] do c ← check (iWord 19 f dest 1 (high*32+amount)) 0x40 left 0xffffffff c
  for bits in [0,1,1023,1024,2047,2048,2^19-1,2^19,2^20-1] do
    for dest in [0,1,31] do
      for pc in [0,1,2,3,0xfffffffc,0xffffffff] do
        c ← check (jWord dest bits) pc 0x12345678 0x87654321 c
        c ← check (bits*4096+dest*128+55) pc 0xffffffff 0xffffffff c
        c ← check (bits*4096+dest*128+23) pc 0xffffffff 0xffffffff c
  for k in [:20] do c ← check (jWord (k%32) (2^k)) 0xfffffffc 0 0 c
  for system in [115,1048691] do
    c ← check system 0xfffffffc 0xffffffff 0xffffffff c
    for k in [:32] do c ← check (Nat.xor system (2^k)) 0xfffffffc 0xffffffff 0xffffffff c
  let mut seed := 0x51ce332
  for _ in [:16384] do
    seed := lcg seed
    c ← check seed (lcg seed) (lcg (lcg seed)) (lcg (lcg (lcg seed))) c
  unless c.mnemonics.all id && c.classes.all id && c.illegal > 100000 && c.loadZero > 0 && c.targetFault > 0 do
    throw (IO.userError "Missing execution instruction/class/fault/x0 coverage")
  return c

def registerRead (bank : Array Nat) (index : Nat) : Nat := if index = 0 then 0 else bank[index]!

/-- Match the decoded source-port contract independently: inapplicable source
indices are zero, while FENCE retains its raw rs1 field without using it. -/
def operandIndices (word : Nat) : Nat × Nat :=
  match decodeReference word with
  | none => (0,0)
  | some d =>
    (if 3 ≤ d.kind && d.kind ≤ 37 then d.source1 else 0,
     if (4 ≤ d.kind && d.kind ≤ 9) || (15 ≤ d.kind && d.kind ≤ 17) ||
         (27 ≤ d.kind && d.kind ≤ 36) then d.source2 else 0)

def registerArrayChecks : IO Nat := do
  let mut count := 0
  for seed in [:16] do
    let bank := (Array.range 32).map fun k => lcg (seed*137+k*0x10204081)
    -- The unused array slot0 deliberately contains garbage. Reads of x0 must
    -- nevertheless supply zero, and no retired write may alter that slot.
    for (dest,first,second) in [(0,0,0),(1,1,2),(2,1,2),(1,1,1),(31,31,31),(31,0,31),(31,31,0),(1,0,0)] do
      let mut words := registerCodes.map fun (f,h) => rWord f h dest first second
      words := words ++ #[iWord 19 0 dest first 4095, iWord 19 3 dest first 4095,
        iWord 103 0 dest first 1, iWord 3 0 dest first 4095, iWord 3 2 dest first 1,
        sWord 0 first second 4095, sWord 1 first second 1, sWord 2 first second 3,
        bWord 0 first second 1, bWord 1 first second 1, bWord 4 first second 2048,
        bWord 7 first second 4095, jWord dest 1, iWord 15 0 dest first 0xfff]
      for word in words do
        let (first,second) := operandIndices word
        let left := registerRead bank first
        let right := registerRead bank second
        let _ ← check word 0xfffffffc left right {}
        let result := actual word 0xfffffffc left right
        let after := if result[2]! = 1 then bank.set! result[3]! result[4]! else bank
        unless after[0]! = bank[0]! do throw (IO.userError "Architectural zero slot was written")
        count := count+1
  return count

/-- A dependent integer-register sequence exercises old operand capture,
overlapping writeback, backward branches, link values, JALR bit clearing and
address wrap. This is a test harness for combinational results, not a CPU or a
memory-service model; it stops on the explicit EBREAK result. -/
def program : Array Nat := #[
  iWord 19 0 1 0 5, iWord 19 0 2 0 1, rWord 0 0 2 2 1,
  iWord 19 0 1 1 4095, bWord 1 1 0 4092, jWord 3 4, 0,
  iWord 19 0 3 3 1, iWord 103 0 4 3 11, 0x800002b7,
  iWord 19 5 5 5 (32*32+31), iWord 19 3 6 5 4095,
  rWord 4 0 7 5 2, 1048691]

def programs : IO Nat := do
  let mut total := 0
  for base in [0,4,0x7fffffe0,0xffffffe0] do
    let mut bank := Array.replicate 32 0 |>.set! 0 0xdeadbeef
    let mut pc := base
    let mut finished := false
    for _ in [:40] do
      unless finished do
        let relative := (pc+modulus-base)%modulus
        unless relative%4 = 0 && relative/4 < program.size do throw (IO.userError "Program PC escaped retained image")
        let word := program[relative/4]!
        let (first,second) := operandIndices word
        let left := registerRead bank first
        let right := registerRead bank second
        let _ ← check word pc left right {}
        let result := actual word pc left right
        if result[0]! = 0 then
          if result[2]! = 1 then bank := bank.set! result[3]! result[4]!
          pc := result[1]!
        else
          unless result[0]! = 4 && result[10]! = 2 do throw (IO.userError "Program ended outside EBREAK")
          finished := true
        total := total+1
    unless finished && pc = (base+52)%modulus && bank[0]! = 0xdeadbeef && bank[1]! = 0 &&
        bank[2]! = 16 && bank[3]! = (base+25)%modulus && bank[4]! = (base+36)%modulus &&
        bank[5]! = 0xffffffff && bank[6]! = 0 && bank[7]! = 0xffffffef do
      throw (IO.userError s!"Integer-register program result mismatch at base {base}: {bank}")
  return total

abbrev E (w : Nat) := Expr Input NoRegisters w

/-- Corrupt actual expression endpoints. Correct outputs are checked against
the unchanged independent oracle at each witness before trying the mutant. -/
def mutant (mode : Nat) : Bundle Input NoRegisters := fun f =>
  let word : E 32 := .input .instruction
  let pc : E 32 := .input .pc
  let left : E 32 := .input .operand1
  let right : E 32 := .input .operand2
  match f with
  | .classification =>
    if mode = 0 || mode = 9 || mode = 14 then .lit 0
    else if mode = 10 || mode = 12 then .lit 4 else circuit.output .classification
  | .nextPC => if mode = 1 then pc else if mode = 16 then WordOps.add pc (.lit 4) else circuit.output .nextPC
  | .writeEnable => if mode = 2 || mode = 13 then .lit 1 else circuit.output .writeEnable
  | .writeRd => if mode = 21 then .slice 15 5 (by decide) word else circuit.output .writeRd
  | .writeData =>
    if mode = 3 then WordOps.add left right
    else if mode = 4 then .concat (.lit (0#31)) (.ult left right)
    else if mode = 5 then WordOps.shiftLeftBy left (.slice 0 6 (by decide) right)
    else if mode = 6 then WordOps.shiftRightBy left (.slice 0 5 (by decide) right)
    else circuit.output .writeData
  | .address => if mode = 7 then WordOps.add left (.concat (.lit (0#20)) (.slice 20 12 (by decide) word))
    else if mode = 17 then left else circuit.output .address
  | .size => if mode = 19 then .lit 2 else circuit.output .size
  | .signedLoad => if mode = 18 then .lit 1 else circuit.output .signedLoad
  | .storeData => if mode = 8 then .band right (.lit 255) else circuit.output .storeData
  | .loadRd => if mode = 20 then .lit 0 else circuit.output .loadRd
  | .trapCause => if mode = 15 then .lit 2 else circuit.output .trapCause
  | .trapTarget => if mode = 11 then left else circuit.output .trapTarget

def mutations : IO Nat := do
  let probes := #[
    (0,0,0,0,0), (1,iWord 19 0 1 1 1,0xfffffffc,7,9),
    (2,iWord 19 0 0 1 1,0,7,9), (3,rWord 0 32 3 1 2,0,5,2),
    (4,rWord 2 0 3 1 2,0,0x80000000,0), (5,rWord 1 0 3 1 2,0,1,32),
    (6,rWord 5 32 3 1 2,0,0x80000000,1), (7,iWord 3 0 3 1 4095,0,0,0),
    (8,sWord 0 1 2 0,0,0,0x12345678), (9,iWord 3 0 0 1 0,0,0,0),
    (10,iWord 103 0 3 1 0,0,1,0), (11,iWord 103 0 3 1 0,0,3,0),
    (12,bWord 1 1 2 1,0,7,7), (13,jWord 3 1,0,0,0),
    (14,iWord 15 0 31 17 0xfff,0,0xffffffff,0xffffffff), (15,115,0,0,0),
    (16,iWord 3 0 3 1 0,0x100,0,0), (17,0,0,0x12345678,0),
    (18,iWord 3 2 3 1 0,0,0,0), (19,iWord 3 0 3 1 0,0,0,0),
    (20,iWord 3 0 31 1 0,0,0,0), (21,iWord 19 0 7 9 1,0,5,0)]
  for (mode,word,pc,left,right) in probes do
    let _ ← check word pc left right {}
    let wrong := outputs.ports.map fun ⟨_,f⟩ => ((mutant mode f).eval (pins word pc left right) noRegisters).toNat
    unless wrong != reference word pc left right do throw (IO.userError s!"Expression mutation {mode} escaped")
  return probes.size

inductive BoundInput : Nat → Type where
  | low : BoundInput 16
  | left : BoundInput 32
inductive BoundRegister : Nat → Type where
  | high : BoundRegister 16
  | pc : BoundRegister 32
  | right : BoundRegister 32

def replacement : {b : Nat} → Input b → Expr BoundInput BoundRegister b
  | _, .instruction => .concat (.reg BoundRegister.high) (.input BoundInput.low)
  | _, .pc => .reg BoundRegister.pc | _, .operand1 => .input BoundInput.left | _, .operand2 => .reg BoundRegister.right
def replaceRegister : {b : Nat} → NoRegisters b → Expr BoundInput BoundRegister b := fun r => nomatch r

def binding : IO Nat := do
  let bound := outputs.ports.map fun ⟨b,f⟩ => (⟨b,(circuit.output f).bind replacement replaceRegister⟩ : Sigma fun b => Expr BoundInput BoundRegister b)
  for k in [:512] do
    let word := if k%2 = 0 then rWord (k%8) (if k%16 = 0 then 32 else 0) (k%32) 1 2 else lcg k
    let pc := (modulus-4+k)%modulus
    let left := boundaries[k%boundaries.size]!
    let right := lcg word
    let i : Values BoundInput := fun p => match p with
      | .low => BitVec.ofNat 16 word | .left => BitVec.ofNat 32 left
    let s : Values BoundRegister := fun p => match p with
      | .high => BitVec.ofNat 16 (word/65536) | .pc => BitVec.ofNat 32 pc | .right => BitVec.ofNat 32 right
    let actual := bound.map fun ⟨_,e⟩ => (e.eval i s).toNat
    unless actual = reference word pc left right do throw (IO.userError "Substituted register/input execution mismatch")
  return 512

def descriptors : IO Unit := do
  unless inputs.ports.map Sigma.fst = #[32,32,32,32] && registers.size = 0 &&
      outputs.ports.map Sigma.fst = #[3,32,1,5,32,32,2,1,32,5,2,32] do
    throw (IO.userError "Incorrect complete execution interface widths")
  unless outputs.ports.map (fun f => outputs.label f.2) =
      #["classification","next_pc","write_enable","write_rd","write_data","address","size","signed_load","store_data","load_rd","trap_cause","trap_target"] do
    throw (IO.userError "Changed execution output order/labels")

end RV32IExecuteCircuitTests

elab "#audit_rv32i_execute_circuit" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.RV32I.ExecuteCircuit." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.RV32I.ExecuteCircuit" ||
        name.toString.startsWith "RV32IExecuteCircuitTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved execution circuit axioms in {name}: {bad}"
  if count < 100 then throwError "Incomplete execution circuit audit"
  logInfo m!"Execution circuit audit: {count} declarations, standard axioms only."

#audit_rv32i_execute_circuit

def main (args : List String) : IO Unit := do
  RV32IExecuteCircuitTests.descriptors
  unless args = ["--focused"] do
    let coverage ← RV32IExecuteCircuitTests.campaign
    IO.println s!"Execute circuit: {coverage.checked} raw checks; {coverage.illegal} illegal words; all 40 mnemonics/all 5 classes; {coverage.loadZero} x0 loads; {coverage.targetFault} target faults."
  let registers ← RV32IExecuteCircuitTests.registerArrayChecks
  let programs ← RV32IExecuteCircuitTests.programs
  let binding ← RV32IExecuteCircuitTests.binding
  let mutants ← RV32IExecuteCircuitTests.mutations
  IO.println s!"Execute circuit: {registers} coherent register-array cases; {programs} dependent program steps; {binding} binding checks; {mutants} actual Expr faults rejected."
