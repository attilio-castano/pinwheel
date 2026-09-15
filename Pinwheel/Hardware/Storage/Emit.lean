import Pinwheel.Hardware.Storage.Small

namespace Pinwheel.Hardware.Storage
open Loader Machine

def physicalLabel : {w : Nat} → Small.Register w → String
  | _, .control r => "loader_" ++ Loader.registerLabel r
  | _, .core r => Reactive.registerLabel r
  | _, .word b k => s!"bank{if b then 1 else 0}_word{k.toNat}"
  | _, .index b k => s!"bank{if b then 1 else 0}_index{k.toNat}"
  | _, .idle b => s!"bank{if b then 1 else 0}_idle"
  | _, .last b => s!"bank{if b then 1 else 0}_last"

def physicalBank (b : Bool) : Array (Sigma Small.Register) :=
  Array.ofFn (fun k : Fin 32 => ⟨64, .word b (BitVec.ofFin k)⟩) ++
  Array.ofFn (fun k : Fin 256 => ⟨5, .index b (BitVec.ofFin k)⟩) ++ #[⟨6, .idle b⟩, ⟨8, .last b⟩]

def physicalNext : Small.Register w → Expr Store.Input Store.Register w
  | .word _ k => Store.next (.word (BitVec.ofNat 6 k.toNat))
  | .index _ k => .slice 0 5 (by decide) (Store.next (.index k))
  | .idle _ => Store.next .idle
  | .last _ => Store.next .last
  | .control _ | .core _ => .lit 0

def moduleText : Except String String := do
  let pn : {w : Nat} → Small.Register w → String := fun r => "%r_" ++ physicalLabel r
  let rn : {w : Nat} → Machine.Register w → String := fun r => "%logical_" ++ Machine.registerLabel r
  let hn : {w : Nat} → Machine.Input w → String := fun i => if inputLabel i == "command" then "%checked_command" else "%" ++ inputLabel i
  let cn : {w : Nat} → Reactive.Register w → String := fun r => rn (.core r)
  let ln : {w : Nat} → Loader.Register w → String := fun r => rn (.control r)
  let (result, buffer) ← (do
    for ⟨w, r⟩ in Machine.registers do
      let value ← Hardware.Emit.expression (fun i => "%" ++ inputLabel i) pn (Small.logical r)
      modify fun buf => {buf with lines := buf.lines.push s!"    {rn r} = hw.wire {value} : i{w}"}
    let command ← Hardware.Emit.expression (fun i => "%" ++ inputLabel i) pn (Small.inputs Machine.Input.command)
    modify fun buf => {buf with lines := buf.lines.push s!"    %checked_command = hw.wire {command} : i3"}
    let busy ← Hardware.Emit.expression (fun _ => "%init") cn Reactive.running
    let li : {w : Nat} → Loader.Input w → String := fun p => match p with
      | .init => "%init" | .reset => "%reset" | .busy => busy | .command => "%checked_command" | .data => "%data"
    let selected ← Hardware.Emit.expression hn rn selectedGate
    let read (address : String) : Hardware.Emit.M String :=
      Hardware.Emit.expression (I := Cut) (R := Machine.Register) (fun p => match p with | Cut.selection => selected | Cut.address => address) rn
        (Execution.readTree 6 (fun k => .mux (.input Cut.selection) (.reg (.memory true (.word k))) (.reg (.memory false (.word k))))
          (Execution.readTree 8 (fun k => .mux (.input Cut.selection) (.reg (.memory true (.index k))) (.reg (.memory false (.index k)))) (.input Cut.address)))
    let current ← read (cn .pc)
    let reset ← Hardware.Emit.expression hn rn (baseInputs .reset)
    let start ← Hardware.Emit.expression li ln Loader.startGate
    let idleLevels ← Hardware.Emit.expression hn rn (baseInputs .idleLevels)
    let idleEnabled ← Hardware.Emit.expression hn rn (baseInputs .idleEnabled)
    let last ← Hardware.Emit.expression hn rn (baseInputs .last)
    let base : {w : Nat} → Reactive.Input w → String := fun p => match p with
      | .reset => reset | .start => start | .incoming => "%incoming" | .idleLevels => idleLevels
      | .idleEnabled => idleEnabled | .last => last | .current => current | .successor => current
    let address ← Hardware.Emit.expression base cn Reactive.target
    let successor ← read address
    let si : {w : Nat} → Reactive.Input w → String := fun p => match p with
      | .successor => successor | _ => base p
    let mut declarations := #[]
    for ⟨w, r⟩ in Loader.registers do
      let value ← Hardware.Emit.expression li ln (Loader.circuit.next r)
      declarations := declarations.push s!"    {pn (.control r)} = seq.compreg {value}, %clock : i{w}"
    for ⟨w, r⟩ in Reactive.registers do
      let value ← Hardware.Emit.expression si cn (Reactive.circuit.next r)
      declarations := declarations.push s!"    {pn (.core r)} = seq.compreg {value}, %clock : i{w}"
    for b in #[false, true] do
      let write ← Hardware.Emit.expression hn rn (memoryInputs b .write)
      let mi : {w : Nat} → Store.Input w → String := fun p => match p with
        | .write => write | .cursor => ln .cursor | .data => "%data" | .address => address
      for ⟨w, r⟩ in physicalBank b do
        let value ← Hardware.Emit.expression mi (fun r => rn (.memory b r)) (physicalNext r)
        declarations := declarations.push s!"    {pn r} = seq.compreg {value}, %clock : i{w}"
    let mut out := #[]
    for ⟨_, o⟩ in Machine.outputs do
      out := out.push (← match o with
        | .control o => Hardware.Emit.expression li ln (Loader.circuit.output o)
        | .core o => Hardware.Emit.expression si cn (Reactive.circuit.output o))
    return (declarations, out) : Hardware.Emit.M _).run {}
  let ports := #["in %clk : i1"] ++ Machine.inputs.map (fun ⟨w, i⟩ => s!"in %{inputLabel i} : i{w}") ++
    Machine.outputs.map (fun ⟨w, o⟩ => s!"out {outputLabel o} : i{w}")
  let out := "    hw.output " ++ String.intercalate ", " result.2.toList ++ " : " ++
    String.intercalate ", " (Machine.outputs.toList.map (fun ⟨w, _⟩ => s!"i{w}"))
  return "module attributes {circt.loweringOptions = \"disallowPackedArrays,disallowLocalVariables,locationInfoStyle=none\"} {\n  hw.module @pinwheel_atomic_small(" ++
    String.intercalate ", " ports.toList ++ ") {\n    %clock = seq.to_clock %clk\n" ++
    String.intercalate "\n" (buffer.lines ++ result.1 ++ #[out]).toList ++ "\n  }\n}\n"

end Pinwheel.Hardware.Storage
