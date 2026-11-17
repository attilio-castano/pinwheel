import Lean
import Pinwheel.Hardware.Processor.SystemCircuitArchitecture

open Lean Elab Command Pinwheel.Hardware Pinwheel.Hardware.Processor

namespace ProcessorArchitecturalEventTests
open CoreInterface

/-- A numeric register-array fixture, independent of instruction evaluation. -/
def oldRegisters (k : Fin 31) : RV32I.Word := BitVec.ofNat 32 (1000 + 17*k.val)
def after (destination value : Nat) : RV32I.Semantics.State :=
  ⟨68,fun k => if k.val+1 = destination then BitVec.ofNat 32 value else oldRegisters k⟩
def pins (row : Array Nat) : Values Input := fun {b} p => BitVec.ofNat b row[(inputs.position p).val]!
def raw (phase word : Nat) : Values CoreCircuit.Register := fun {b} p =>
  let index := (CoreCircuit.registers.position p).val
  BitVec.ofNat b (if index < 31 then 1000+17*index else #[phase,64,word,9,0xdeadbeef,1][index-31]!)
def idle : Array Nat := Array.replicate 12 0

def sameEvent (actual expected : CoreModel.Event) : Bool :=
  match actual,expected with
  | .reset,.reset => true
  | .retired word path state,.retired expectedWord expectedPath expectedState =>
      word == expectedWord && decide (path = expectedPath) && state.pc == expectedState.pc &&
        (Array.ofFn fun k : Fin 31 => (state.registers k).toNat) ==
          (Array.ofFn fun k : Fin 31 => (expectedState.registers k).toNat)
  | .trapped fault path,.trapped expectedFault expectedPath =>
      decide (fault = expectedFault) && decide (path = expectedPath)
  | _,_ => false

def sameEvents (actual expected : List CoreModel.Event) : Bool :=
  match actual,expected with
  | [],[] => true
  | [actual],[expected] => sameEvent actual expected
  | _,_ => false

/-- Only the named output expression is corrupted; state transitions and all
other output expressions remain those of the actual core constructor. -/
def invertedPort (port : Nat) : Circuit Input CoreCircuit.Register Output :=
  { CoreCircuit.circuit with output := fun o =>
      if (outputs.position o).val = port then .inv (CoreCircuit.circuit.output o)
      else CoreCircuit.circuit.output o }

structure Fixture where
  name : String
  phase : Nat
  word : Nat
  row : Array Nat
  expected : List CoreModel.Event
  mutations : List Nat

/-- Raw instruction integers and explicit expected arithmetic/transactions.
No Decode, Semantics.step/finish, CoreModel.tick/event or expected outputValues
are used by this oracle. Full RF comparison detects writes outside the target. -/
def fixtures : List Fixture :=
  [ ⟨"addi",2,0x00710093,idle,[.retired 0x00710093 .execute (after 1 1024)], [11,13,14,15,16,17]⟩,
    ⟨"ecall",2,0x00000073,idle,[.trapped ⟨64,some 0x73,.instruction .environmentCall⟩ (some .execute)],
      [18,19,20,21,22]⟩,
    ⟨"misaligned-jal",2,0x002000ef,idle,
      [.trapped ⟨64,some 0x002000ef,.instruction (.instructionAddressMisaligned 66)⟩ (some .execute)],[23]⟩,
    ⟨"atomic-load-x0",3,0x00314003,((idle.set! 5 1).set! 6 1).set! 8 0x1234fedc,
      [.retired 0x00314003 (.data .atomic (.load 1020 .byte false) (.success 0x1234fedc)) (after 0 0)],[]⟩,
    ⟨"atomic-store-payload",3,0x003100a3,((idle.set! 5 1).set! 6 1).set! 8 0xdeadbeef,
      [.retired 0x003100a3 (.data .atomic (.store 1018 .byte 1034) (.success 0xdeadbeef)) (after 0 0)],[]⟩,
    ⟨"deferred-load-fault",4,0x00012183,((idle.set! 9 1).set! 10 2).set! 11 0xabcdef01,
      [.trapped ⟨64,some 0x00012183,.instruction (.loadFault .accessFault 1017)⟩
        (some (.data .deferred (.load 1017 .word false) (.fault .accessFault)))],[]⟩,
    ⟨"fence",5,0x0000000f,idle,[.retired 0x0000000f .fence (after 0 0)],[]⟩,
    ⟨"unowned-reply",3,0x00314003,(idle.set! 9 1).set! 11 0xfedcba98,[],[11]⟩,
    ⟨"reset-cancels",7,0xffffffff,idle.set! 0 1,[.reset],[0]⟩ ]

def main : IO Unit := do
  let mut negatives := 0
  for f in fixtures do
    let i : Values Input := pins f.row
    let r : Values CoreCircuit.Register := raw f.phase f.word
    let actual := CoreCircuit.Events.events i r
    unless sameEvents actual f.expected do throw (IO.userError s!"Independent architectural event mismatch: {f.name}")
    for port in f.mutations do
      let changed := CoreCircuit.Events.extract i r ((invertedPort port).observe i r)
      if sameEvents changed f.expected then
        throw (IO.userError s!"Actual Expr event corruption escaped: {f.name}/port{port}")
      negatives := negatives+1
  IO.println s!"Architectural events: {fixtures.length} independent exact event/full-RF fixtures, {negatives} actual Expr output faults rejected."

elab "#audit_architectural_events" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name,_) in env.constants.toList do
    let text := name.toString
    if text.startsWith "Pinwheel.Hardware.Processor.CoreCircuit.Events." ||
        text.startsWith "Pinwheel.Hardware.Processor.CoreEventFacts." ||
        text.startsWith "Pinwheel.Hardware.Processor.SystemCircuit." ||
        text.startsWith "_private.Pinwheel.Hardware.Processor.CoreCircuitEvents" ||
        text.startsWith "_private.Pinwheel.Hardware.Processor.CoreCircuitAccounting" ||
        text.startsWith "_private.Pinwheel.Hardware.Processor.CoreCircuitProgress" ||
        text.startsWith "_private.Pinwheel.Hardware.Processor.CoreEventFacts" ||
        text.startsWith "_private.Pinwheel.Hardware.Processor.SystemCircuitArchitecture" ||
        text.startsWith "ProcessorArchitecturalEventTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Nonstandard architectural event axiom in {name}: {bad}"
  if count < 300 then throwError "Incomplete architectural event audit"
  logInfo m!"Architectural event audit: {count} declarations, standard axioms only."

#audit_architectural_events
end ProcessorArchitecturalEventTests

def main := ProcessorArchitecturalEventTests.main
