import Pinwheel.Hardware.Storage.CacheContract
import Pinwheel.Hardware.Loader.Emit

namespace Pinwheel.Hardware.Loader.Machine.CachedEmit
open Machine

inductive CacheInput : Nat → Type where
  | busy : CacheInput 1 | oldPC : CacheInput 8 | newPC : CacheInput 8
  | successor : CacheInput 64 | current : CacheInput 64

def update : Expr CacheInput Register 64 :=
  .mux (Execution.bor (.inv (.input .busy)) (.inv (.equal (.input .newPC) (.input .oldPC))))
    (.input .successor) (.input .current)

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
    let current := "%r_cached_word"
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
    let mut nextPC := ""
    for ⟨w, r⟩ in Reactive.registers do
      let value ← Hardware.Emit.expression si cn (Reactive.circuit.next r)
      if Reactive.registerLabel r == "pc" then nextPC := value
      declarations := declarations.push s!"    {cn r} = seq.compreg {value}, %clock : i{w}"
    let ci : {w : Nat} → CacheInput w → String := fun p => match p with
      | .busy => busy | .oldPC => cn .pc | .newPC => nextPC | .successor => successor | .current => current
    let cached ← Hardware.Emit.expression ci (fun _ => "%init") update
    declarations := declarations.push s!"    {current} = seq.compreg {cached}, %clock : i64"
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
  return "module attributes {circt.loweringOptions = \"disallowPackedArrays,disallowLocalVariables,locationInfoStyle=none\"} {\n  hw.module @pinwheel_atomic_cached(" ++
    String.intercalate ", " ports.toList ++ ") {\n    %clock = seq.to_clock %clk\n" ++
    String.intercalate "\n" (buffer.lines ++ result.1 ++ #[out]).toList ++ "\n  }\n}\n"

end Pinwheel.Hardware.Loader.Machine.CachedEmit
