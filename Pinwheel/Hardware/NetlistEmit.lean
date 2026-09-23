import Pinwheel.Hardware.Netlist
import Pinwheel.Hardware.Emit

namespace Pinwheel.Hardware.Netlist

/-- Emit the body once. Diagnostic consumers may reuse its operation cache to
identify existing expressions without adding observations or changing RTL. -/
def emitBody (registers : Array (Sigma R)) (outputs : Array (Sigma O))
    (rn : {w : Nat} → R w → String) :
    {I : Nat → Type} → Netlist R O I → ({w : Nat} → I w → String) →
      Emit.M (Array String × Array String)
  | _, .letWire e body, names => do
    let value ← Emit.expression names rn e
    emitBody registers outputs rn body (fun p => match p with
      | .input p => names p | .wire => value)
  | _, .finish c, names => do
    let mut declarations := #[]
    for ⟨w, r⟩ in registers do
      let value ← Emit.expression names rn (c.next r)
      declarations := declarations.push s!"    {rn r} = seq.compreg {value}, %clock : i{w}"
    let values ← outputs.mapM fun ⟨_, o⟩ => Emit.expression names rn (c.output o)
    return (declarations, values)

def moduleText (name : String) (n : Netlist R O I)
    (inputs : Array (Sigma I)) (registers : Array (Sigma R)) (outputs : Array (Sigma O))
    (inputLabel : {w : Nat} → I w → String) (registerLabel : {w : Nat} → R w → String)
    (outputLabel : {w : Nat} → O w → String) : Except String String := do
  let (result, buffer) ← (emitBody registers outputs
    (fun r => "%r_" ++ registerLabel r) n (fun p => "%" ++ inputLabel p)).run {}
  let ports := #["in %clk : i1"] ++ inputs.map (fun ⟨w, p⟩ => s!"in %{inputLabel p} : i{w}") ++
    outputs.map (fun ⟨w, p⟩ => s!"out {outputLabel p} : i{w}")
  let out := "    hw.output " ++ String.intercalate ", " result.2.toList ++ " : " ++
    String.intercalate ", " (outputs.map (fun ⟨w, _⟩ => s!"i{w}")).toList
  return "module attributes {circt.loweringOptions = \"disallowPackedArrays,disallowLocalVariables,locationInfoStyle=none\"} {\n  hw.module @" ++ name ++ "(" ++
    String.intercalate ", " ports.toList ++ ") {\n    %clock = seq.to_clock %clk\n" ++
    String.intercalate "\n" (buffer.lines ++ result.1 ++ #[out]).toList ++ "\n  }\n}\n"

end Pinwheel.Hardware.Netlist
