import Pinwheel.Hardware.Loader.Contract

namespace Pinwheel.Hardware.Loader

def registers : Array (Sigma Register) := #[⟨1, .active⟩, ⟨1, .valid⟩, ⟨1, .pending⟩, ⟨9, .cursor⟩]
def registerLabel : {w : Nat} → Register w → String
  | _, .active => "active" | _, .valid => "valid" | _, .pending => "pending" | _, .cursor => "cursor"
def outputs : Array (Sigma Output) := registers.map (fun ⟨w, r⟩ => ⟨w, .state r⟩) ++
  #[⟨1, .push⟩, ⟨1, .commit⟩, ⟨1, .start⟩, ⟨1, .rejected⟩]
def outputLabel : {w : Nat} → Output w → String
  | _, .state r => registerLabel r | _, .push => "push" | _, .commit => "commit"
  | _, .start => "start" | _, .rejected => "rejected"

namespace Store
def registers : Array (Sigma Register) :=
  Array.ofFn (fun k : Fin 64 => ⟨64, .word (BitVec.ofFin k)⟩) ++
  Array.ofFn (fun k : Fin 256 => ⟨6, .index (BitVec.ofFin k)⟩) ++ #[⟨6, .idle⟩, ⟨8, .last⟩]
def registerLabel : {w : Nat} → Register w → String
  | _, .word k => s!"word{k.toNat}" | _, .index k => s!"index{k.toNat}"
  | _, .idle => "idle" | _, .last => "last"
end Store

namespace Machine
def inputs : Array (Sigma Input) :=
  #[⟨1, .init⟩, ⟨1, .reset⟩, ⟨3, .command⟩, ⟨64, .data⟩, ⟨2, .incoming⟩]
def inputLabel : {w : Nat} → Input w → String
  | _, .init => "init" | _, .reset => "reset" | _, .command => "command"
  | _, .data => "data" | _, .incoming => "incoming"
def registers : Array (Sigma Register) :=
  Loader.registers.map (fun ⟨w, r⟩ => ⟨w, .control r⟩) ++
  Reactive.registers.map (fun ⟨w, r⟩ => ⟨w, .core r⟩) ++
  #[false, true].flatMap (fun b => Store.registers.map (fun ⟨w, r⟩ => ⟨w, .memory b r⟩))
def registerLabel : {w : Nat} → Register w → String
  | _, .control r => "loader_" ++ Loader.registerLabel r
  | _, .core r => Reactive.registerLabel r
  | _, .memory b r => s!"bank{if b then 1 else 0}_" ++ Store.registerLabel r
def outputs : Array (Sigma Output) :=
  Loader.outputs.map (fun ⟨w, o⟩ => ⟨w, .control o⟩) ++ Reactive.outputs.map (fun ⟨w, o⟩ => ⟨w, .core o⟩)
def outputLabel : {w : Nat} → Output w → String
  | _, .control o => "loader_" ++ Loader.outputLabel o | _, .core o => Reactive.outputLabel o

inductive Cut : Nat → Type where | selection : Cut 1 | address : Cut 8

/-- Named read/target cut points implement Machine.circuit without expanding its trees.
The serializer and CIRCT remain an independently tested translation boundary. -/
def moduleText : Except String String := do
  let rn : {w : Nat} → Register w → String := fun r => "%r_" ++ registerLabel r
  let hn : {w : Nat} → Input w → String := fun i => "%" ++ inputLabel i
  let cn : {w : Nat} → Reactive.Register w → String := fun r => rn (.core r)
  let ln : {w : Nat} → Loader.Register w → String := fun r => rn (.control r)
  let (result, buffer) ← (do
    let busy ← Hardware.Emit.expression (fun _ => "%init") cn Reactive.running
    let li : {w : Nat} → Loader.Input w → String := fun p => match p with
      | .init => "%init" | .reset => "%reset" | .busy => busy | .command => "%command" | .data => "%data"
    let selected ← Hardware.Emit.expression hn rn selectedGate
    let read (address : String) : Hardware.Emit.M String :=
      Hardware.Emit.expression (I := Cut) (R := Register) (fun p => match p with | Cut.selection => selected | Cut.address => address) rn
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
      declarations := declarations.push s!"    {ln r} = seq.compreg {value}, %clock : i{w}"
    for ⟨w, r⟩ in Reactive.registers do
      let value ← Hardware.Emit.expression si cn (Reactive.circuit.next r)
      declarations := declarations.push s!"    {cn r} = seq.compreg {value}, %clock : i{w}"
    for b in #[false, true] do
      let write ← Hardware.Emit.expression hn rn (memoryInputs b .write)
      let mi : {w : Nat} → Store.Input w → String := fun p => match p with
        | .write => write | .cursor => ln .cursor | .data => "%data" | .address => address
      for ⟨w, r⟩ in Store.registers do
        let name := rn (.memory b r)
        let value ← Hardware.Emit.expression mi (fun r => rn (.memory b r)) (Store.next r)
        declarations := declarations.push s!"    {name} = seq.compreg {value}, %clock : i{w}"
    let mut out := #[]
    for ⟨_, o⟩ in outputs do
      out := out.push (← match o with
        | .control o => Hardware.Emit.expression li ln (Loader.circuit.output o)
        | .core o => Hardware.Emit.expression si cn (Reactive.circuit.output o))
    return (declarations, out) : Hardware.Emit.M _).run {}
  let ports := #["in %clk : i1"] ++ inputs.map (fun ⟨w, i⟩ => s!"in %{inputLabel i} : i{w}") ++
    outputs.map (fun ⟨w, o⟩ => s!"out {outputLabel o} : i{w}")
  let out := "    hw.output " ++ String.intercalate ", " result.2.toList ++ " : " ++
    String.intercalate ", " (outputs.toList.map (fun ⟨w, _⟩ => s!"i{w}"))
  return "module attributes {circt.loweringOptions = \"disallowPackedArrays,disallowLocalVariables,locationInfoStyle=none\"} {\n  hw.module @pinwheel_atomic_indexed(" ++
    String.intercalate ", " ports.toList ++ ") {\n    %clock = seq.to_clock %clk\n" ++
    String.intercalate "\n" (buffer.lines ++ result.1 ++ #[out]).toList ++ "\n  }\n}\n"

end Machine
end Pinwheel.Hardware.Loader
