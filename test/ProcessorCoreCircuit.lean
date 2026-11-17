import Lean
import Pinwheel.Hardware.Processor.CoreCertified
import Pinwheel.Hardware.Processor.CoreCircuitRequests

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Processor

namespace ProcessorCoreCircuitTests

open CoreInterface

def pins (row : Array Nat) : Values Input := fun {b} p => BitVec.ofNat b row[(inputs.position p).val]!
def bank (values : Array Nat) : Values CoreCircuit.Register := fun {b} p =>
  BitVec.ofNat b values[(CoreCircuit.registers.position p).val]!
def capture (d : Interface P) (v : Values P) : Array Nat :=
  d.ports.map (fun ⟨_,p⟩ => (v p).toNat)

def phaseCode : CoreModel.Phase → Nat
  | .fetchRequest => 0 | .fetchResponse => 1 | .execute _ => 2 | .dataRequest _ => 3
  | .dataResponse _ => 4 | .fence _ => 5 | .terminal _ => 6

/-- Full physical expectations come from the established controller contract.
Inactive instruction/fault storage retains its old bits until capture or reset. -/
def expectedBank (i : Values Input) (s : CoreModel.State) (raw : Array Nat) : Array Nat := Id.run do
  if i reset = 1 then return Array.replicate 37 0
  let next := CoreModel.step (decode i) s
  let mut values := (Array.ofFn fun k : Fin 31 => (next.arch.registers k).toNat) ++
    #[phaseCode next.phase,next.arch.pc.toNat,raw[33]!,raw[34]!,raw[35]!,raw[36]!]
  if phaseCode s.phase == 1 && i fetchResponseValid = 1 && i fetchResponseFault = 0 then
    values := values.set! 33 (i fetchResponseData).toNat
  match CoreModel.event (decode i) s with
  | some (.trapped fault _) =>
      values := ((values.set! 34 (causeCode fault.cause).toNat).set! 35 (faultAddress fault).toNat).set! 36 fault.word.isSome.toNat
  | _ => pure ()
  return values

def checkEdge (s : CoreModel.State) (raw : Array Nat) (row : Array Nat) : IO (CoreModel.State × Array Nat) := do
  unless raw.size == 37 && row.size == 12 do throw (IO.userError "Malformed core edge fixture")
  let i : Values Input := pins row
  let state : Values CoreCircuit.Register := bank raw
  let expectedPre := capture outputs (outputValues i s)
  let actualPre := capture outputs (CoreCircuit.circuit.observe i state)
  unless actualPre == expectedPre do
    throw (IO.userError s!"Core pre-output mismatch phase{raw[31]!} input{row}: expected{expectedPre}, got{actualPre}")
  let expected := expectedBank i s raw
  let actual := capture CoreCircuit.registers (CoreCircuit.circuit.step i state)
  unless actual == expected do
    throw (IO.userError s!"Core register mismatch phase{raw[31]!} input{row}: expected{expected}, got{actual}")
  let next := CoreModel.step (decode i) s
  let expectedPost := capture outputs (outputValues i next)
  let actualPost := capture outputs (CoreCircuit.circuit.observe i (bank actual))
  unless actualPost == expectedPost do
    throw (IO.userError s!"Core post-output mismatch input{row}: expected{expectedPost}, got{actualPost}")
  return (next, actual)

def emptyRow : Array Nat := Array.replicate 12 0
def instruction (word : Nat) : Array Nat := (emptyRow.set! 2 1).set! 4 word
def service (atomic fault data : Nat) : Array Nat :=
  (((emptyRow.set! 5 1).set! 6 atomic).set! 7 fault).set! 8 data
def response (fault data : Nat) : Array Nat := ((emptyRow.set! 9 1).set! 10 fault).set! 11 data

def opcodeI (imm rs1 funct rd opcode : Nat) : Nat :=
  (imm%4096)*2^20 + rs1*2^15 + funct*2^12 + rd*2^7 + opcode
def opcodeS (imm rs1 rs2 funct : Nat) : Nat :=
  (imm/32)*2^25 + rs2*2^20 + rs1*2^15 + funct*2^12 + (imm%32)*2^7 + 0x23

def traces : IO Nat := do
  let words := #[0x000100b7,opcodeI 128 0 0 2 0x13,opcodeS 1 1 2 0,
    opcodeI 1 1 0 3 0x03,opcodeI 1 1 4 4 0x03,opcodeI 4 1 2 0 0x03,
    0x400002b7,opcodeS 4 5 3 2,0x0000000f,0x00100073]
  let mut checks := 0
  for mode in [:8] do
    let mut model := CoreModel.initial
    let mut raw := Array.replicate 37 0
    for index in [:words.size] do
      let (s,b) ← checkEdge model raw (emptyRow.set! 1 1)
      model := s; raw := b; checks := checks+1
      -- Unowned data and fetch replies must have no effect on their unrelated phases.
      let fetched := ((instruction words[index]!).set! 9 1).set! 11 0xdeadbeef
      let (s,b) ← checkEdge model raw fetched
      model := s; raw := b; checks := checks+1
      let (s,b) ← checkEdge model raw (response 0 0xdeadbeef)
      model := s; raw := b; checks := checks+1
      match model.phase with
      | .dataRequest _ =>
        for _ in [:mode] do
          let (s,b) ← checkEdge model raw (instruction 0xffffffff)
          model := s; raw := b; checks := checks+1
        let value := if index == 3 then 0xffffff80 else if index == 4 then 128 else 0xdeadbeef
        let (s,b) ← checkEdge model raw (service (mode%2) 0 value)
        model := s; raw := b; checks := checks+1
        if mode%2 == 0 then
          let (s,b) ← checkEdge model raw (service 1 1 0)
          model := s; raw := b; checks := checks+1
          let (s,b) ← checkEdge model raw (response 0 value)
          model := s; raw := b; checks := checks+1
      | .fence _ =>
        let (s,b) ← checkEdge model raw emptyRow
        model := s; raw := b; checks := checks+1
      | _ => pure ()
    unless model.arch.registers ⟨2,by decide⟩ = 0xffffff80 &&
        model.arch.registers ⟨3,by decide⟩ = 128 && (CoreModel.terminal model).isSome do
      throw (IO.userError "Directed core trace did not reach the expected register/trap state")
    let (s,b) ← checkEdge model raw (emptyRow.set! 0 1)
    unless phaseCode s.phase == 0 && b.all (· == 0) do throw (IO.userError "Core reset failed")
    checks := checks+1
  return checks

def dirtyReset : IO Nat := do
  let mut checks := 0
  for p in [:8] do
    let raw := (Array.range 37 |>.map fun k => (0x9abcdef0+k)%2^32).set! 31 p
    let i : Values Input := pins (emptyRow.set! 0 1)
    let after := capture CoreCircuit.registers (CoreCircuit.circuit.step i (bank raw))
    unless after.all (· == 0) do throw (IO.userError "Dirty core reset did not clear every register")
    let actual := capture outputs (CoreCircuit.circuit.observe i (bank raw))
    unless actual == #[1] ++ Array.replicate 29 0 do throw (IO.userError "Dirty reset leaked an offer or commit")
    checks := checks+1
  return checks

def singleInstruction (pc word : Nat) (reply : Array Nat) (resetAt : Option Nat := none) : IO Nat := do
  let arch : RV32I.Semantics.State := ⟨BitVec.ofNat 32 pc, fun k => BitVec.ofNat 32 (0x10000+k.val*4)⟩
  let mut model : CoreModel.State := ⟨arch,.fetchRequest⟩
  let mut raw := (Array.ofFn (fun k : Fin 31 => (arch.registers k).toNat)) ++ #[0,pc,0x55555555,9,0xdeadbeef,1]
  let mut checks := 0
  let traffic := #[emptyRow,emptyRow.set! 1 1,emptyRow,instruction word,emptyRow,emptyRow,
    reply,emptyRow,response 0 0x80,response 1 0,response 2 0,response 3 0,emptyRow]
  for cycle in [:traffic.size] do
    let row := if resetAt == some cycle then traffic[cycle]!.set! 0 1 else traffic[cycle]!
    let (next,bank) ← checkEdge model raw row
    model := next; raw := bank
    checks := checks+1
  return checks

def faultAndStallCases : IO Nat := do
  let words := #[0,0x00000073,0x00100073,opcodeI 1 1 0 1 0x67,opcodeI 0 1 2 0 0x03,
    opcodeI 0 1 2 5 0x03,opcodeS 0 1 2 2,0x0000000f,0x000002ef,0x00001063,
    opcodeI 2048 0 0 0 0x13,opcodeI 4095 1 0 1 0x13]
  let mut checks := 0
  for pc in [0,2,0xfffffffc] do
    for word in words do
      for atomic in [:2] do
        for fault in [:4] do
          checks := checks + (← singleInstruction pc word (service atomic fault 0x80))
  for word in words do
    for cycle in [:13] do
      checks := checks + (← singleInstruction 0 word (service 0 0 0xfeedface) (some cycle))
  return checks

def controlMutation (mode : Nat) : {b : Nat} → CoreCircuit.Control b → CoreCircuit.E b
  | _, .at ⟨0,_⟩ => if mode == 0 then .reg CoreCircuit.phase else CoreCircuit.controlNext (.at ⟨0,by decide⟩)
  | _, .at k => CoreCircuit.controlNext (.at k)

def mutated (mode : Nat) : Circuit Input CoreCircuit.Register Output where
  next r := match r with
    | .left r => CoreCircuit.circuit.next (.left r)
    | .right r => controlMutation mode r
  output o := match o with
    | .at ⟨11,_⟩ => if mode == 1 then .lit 1 else CoreCircuit.circuit.output retireValid
    | .at ⟨5,_⟩ => if mode == 2 then .lit 0 else CoreCircuit.circuit.output dataWrite
    | .at ⟨15,_⟩ => if mode == 3 then .lit 1 else CoreCircuit.circuit.output retireWriteEnable
    | .at ⟨18,_⟩ => if mode == 4 then .lit 0 else CoreCircuit.circuit.output trapValid
    | .at k => CoreCircuit.circuit.output (.at k)

def controls : IO Nat := do
  let mut rejected := 0
  for (mode,p,w,row) in [(0,4,0,emptyRow.set! 0 1), (1,0,0,emptyRow),
      (2,3,opcodeS 0 1 2 2,emptyRow),(3,5,0x0000000f,emptyRow),(4,2,0,emptyRow)] do
    let raw := (Array.replicate 37 0).set! 31 p |>.set! 33 w
    let i : Values Input := pins row
    let s : Values CoreCircuit.Register := bank raw
    let good := (capture CoreCircuit.registers (CoreCircuit.circuit.step i s), capture outputs (CoreCircuit.circuit.observe i s))
    let bad := (capture CoreCircuit.registers ((mutated mode).step i s), capture outputs ((mutated mode).observe i s))
    if good == bad then throw (IO.userError s!"Core Expr fault escaped: {mode}")
    rejected := rejected+1
  return rejected

end ProcessorCoreCircuitTests

elab "#audit_processor_core" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.Processor.CoreCircuit." ||
        name.toString.startsWith "Pinwheel.Hardware.Processor.CoreInterface." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.CoreCircuit" ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.CoreCertified" ||
        name.toString.startsWith "_private.Pinwheel.Hardware.Processor.CoreInterface" ||
        name.toString.startsWith "ProcessorCoreCircuitTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved processor core axioms in {name}: {bad}"
  if count < 568 then throwError "Incomplete processor core audit"
  logInfo m!"Processor core audit: {count} declarations, standard axioms only."

#audit_processor_core

def main : IO Unit := do
  let count ← ProcessorCoreCircuitTests.traces
  let resets ← ProcessorCoreCircuitTests.dirtyReset
  let faults ← ProcessorCoreCircuitTests.faultAndStallCases
  let rejected ← ProcessorCoreCircuitTests.controls
  IO.println s!"Core circuit: {count+faults} complete register/pre/post-output trace edges, {resets} dirty-phase reset cases, {rejected} actual Expr faults rejected."
