import Pinwheel.Hardware.Reactive.CoreProofs
import Pinwheel.Hardware.Execution.Emit
import Pinwheel.Hardware.Reactive.Interface

namespace Pinwheel.Hardware.Reactive

namespace Core

def inputs : Array (Sigma Input) :=
  #[⟨1, .reset⟩, ⟨1, .start⟩, ⟨2, .incoming⟩, ⟨1, .write⟩, ⟨2, .bank⟩, ⟨8, .address⟩, ⟨64, .data⟩]
def inputLabel : {w : Nat} → Input w → String
  | _, .reset => "reset" | _, .start => "start" | _, .incoming => "incoming"
  | _, .write => "write" | _, .bank => "bank" | _, .address => "address" | _, .data => "data"
def registers (memory : Array (Sigma M)) : Array (Sigma (Register M)) :=
  Reactive.registers.map (fun ⟨w, r⟩ => ⟨w, .core r⟩) ++ memory.map (fun ⟨w, r⟩ => ⟨w, .memory r⟩) ++
    #[⟨3, .idleLevels⟩, ⟨3, .idleEnabled⟩, ⟨8, .last⟩]
def registerLabel (label : {w : Nat} → M w → String) : {w : Nat} → Register M w → String
  | _, .core r => Reactive.registerLabel r | _, .memory r => label r
  | _, .idleLevels => "idle_levels" | _, .idleEnabled => "idle_enabled" | _, .last => "last"

/-- Emit the proved bindings as named wires, avoiding exponential tree expansion.
The adapter and CIRCT translation remain outside Lean's proof boundary. -/
def moduleText (name : String) (f : Frontend M) (memory : Array (Sigma M))
    (label : {w : Nat} → M w → String) : Except String String := do
  let regName : {w : Nat} → Register M w → String := fun r => "%r_" ++ registerLabel label r
  let inpName : {w : Nat} → Input w → String := fun i => "%" ++ inputLabel i
  let (result, buffer) ← (do
    let current ← Hardware.Emit.expression inpName regName (f.read memoryReg (coreReg .pc))
    let baseName : {w : Nat} → Reactive.Input w → String := fun port => match port with
      | .reset => "%reset" | .start => "%start" | .incoming => "%incoming"
      | .idleLevels => "%r_idle_levels" | .idleEnabled => "%r_idle_enabled" | .last => "%r_last"
      | .current => current | .successor => current
    let coreName : {w : Nat} → Reactive.Register w → String := fun r => regName (.core r)
    let address ← Hardware.Emit.expression baseName coreName Reactive.target
    let successor ← Hardware.Emit.expression (fun _ => address) regName
      (f.read memoryReg (.input .address))
    let schedName : {w : Nat} → Reactive.Input w → String := fun port => match port with
      | .successor => successor | _ => baseName port
    let write ← Hardware.Emit.expression inpName regName (memoryInputs (M := M) .write)
    let busy ← Hardware.Emit.expression inpName regName (memoryInputs (M := M) .busy)
    let bank ← Hardware.Emit.expression inpName regName (memoryInputs (M := M) .indexBank)
    let memName : {w : Nat} → Execution.Input w → String := fun port => match port with
      | .write => write | .busy => busy | .indexBank => bank | .address => "%address"
      | .data => "%data" | .readA => address | .readB => address
    let mut declarations : Array String := #[]
    for ⟨w, r⟩ in registers memory do
      let value ← match r with
        | .core r => Hardware.Emit.expression schedName coreName (Reactive.circuit.next r)
        | .memory r => Hardware.Emit.expression memName (fun r => regName (.memory r)) (f.next r)
        | _ => Hardware.Emit.expression inpName regName ((circuit f).next r)
      declarations := declarations.push s!"    {regName r} = seq.compreg {value}, %clock : i{w}"
    let mut outputs : Array String := #[]
    for ⟨_, o⟩ in Reactive.outputs do
      outputs := outputs.push (← Hardware.Emit.expression schedName coreName (Reactive.circuit.output o))
    return (declarations, outputs) : Hardware.Emit.M _).run {}
  let ports := #["in %clk : i1"] ++ inputs.map (fun ⟨w, i⟩ => s!"in %{inputLabel i} : i{w}") ++
    Reactive.outputs.map (fun ⟨w, o⟩ => s!"out {Reactive.outputLabel o} : i{w}")
  let output := "    hw.output " ++ String.intercalate ", " result.2.toList ++ " : " ++
    String.intercalate ", " (Reactive.outputs.toList.map (fun ⟨w, _⟩ => s!"i{w}"))
  return "module attributes {circt.loweringOptions = \"disallowPackedArrays,disallowLocalVariables,locationInfoStyle=none\"} {\n  hw.module @" ++ name ++
    "(" ++ String.intercalate ", " ports.toList ++ ") {\n    %clock = seq.to_clock %clk\n" ++
    String.intercalate "\n" (buffer.lines ++ result.1 ++ #[output]).toList ++ "\n  }\n}\n"

def directModule : Except String String :=
  moduleText "pinwheel_reactive_direct" direct Execution.directRegisters Execution.directRegisterLabel

def indexedModule : Except String String :=
  moduleText "pinwheel_reactive_indexed" indexed Execution.indexedRegisters Execution.indexedRegisterLabel

end Core
end Pinwheel.Hardware.Reactive
