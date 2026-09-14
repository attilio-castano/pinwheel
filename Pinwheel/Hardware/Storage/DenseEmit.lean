import Pinwheel.Hardware.Storage.DenseStore
import Pinwheel.Hardware.Storage.CacheEmit
import Pinwheel.Hardware.Storage.Emit

namespace Pinwheel.Hardware.Storage.Dense

def registers (small : Bool) : Array (Sigma Register) :=
  ((List.range (if small then 32 else 64)).toArray.map (fun k => ⟨55, .word (BitVec.ofNat 6 k)⟩)) ++
  Array.ofFn (fun k : Fin 256 => ⟨6, .index (BitVec.ofFin k)⟩) ++ #[⟨6, .idle⟩, ⟨8, .last⟩]
def registerLabel : {w : Nat} → Register w → String
  | _, .word k => s!"word{k.toNat}" | _, .index k => s!"index{k.toNat}"
  | _, .idle => "idle" | _, .last => "last"
end Pinwheel.Hardware.Storage.Dense

namespace Pinwheel.Hardware.Loader.Machine.DenseEmit
open Machine
open Pinwheel.Hardware.Storage


def moduleText (small : Bool := false) (cached : Bool := false) : Except String String := do
  let rn : {w : Nat} → Register w → String := fun {w} r => match w, r with
    | _, .memory _ (.word _) => "%logical_" ++ registerLabel r
    | _, .memory _ (.index _) => (if small then "%logical_" else "%r_") ++ registerLabel r
    | _, _ => "%r_" ++ registerLabel r
  let hn : {w : Nat} → Input w → String := fun i => if small && inputLabel i == "command" then "%checked_command" else "%" ++ inputLabel i
  let cn : {w : Nat} → Reactive.Register w → String := fun r => rn (.core r)
  let ln : {w : Nat} → Loader.Register w → String := fun r => rn (.control r)
  let (result, buffer) ← (do
    if small then
      let command ← Hardware.Emit.expression (fun i => "%" ++ inputLabel i)
        (fun r => "%r_" ++ Storage.physicalLabel r) (Storage.Small.inputs Input.command)
      modify fun buf => {buf with lines := buf.lines.push s!"    %checked_command = hw.wire {command} : i3"}
    for b in #[false, true] do
      let dn : {w : Nat} → Dense.Register w → String := fun r => "%r_bank" ++ (if b then "1" else "0") ++ "_" ++ Dense.registerLabel r
      for k in List.range 64 do
        let value ← if small && k >= 32 then
          Hardware.Emit.expression (I := Input) (R := Dense.Register) hn dn (Expr.lit (4#64))
        else Hardware.Emit.expression (I := Input) (R := Dense.Register) hn dn (Dense.expandExpr (.reg (.word (BitVec.ofNat 6 k))))
        modify fun buf => {buf with lines := buf.lines.push s!"    {rn (.memory b (.word (BitVec.ofNat 6 k)))} = hw.wire {value} : i64"}
      if small then
        for k in List.range 256 do
          let value ← Hardware.Emit.expression hn (fun _ => "%r_bank" ++ (if b then "1" else "0") ++ s!"_index{k}")
            (I := Input) (R := Storage.Small.Register) (.concat (.lit (0#1)) (.reg (.index b (BitVec.ofNat 8 k)) : Expr Input Storage.Small.Register 5))
          modify fun buf => {buf with lines := buf.lines.push s!"    {rn (.memory b (.index (BitVec.ofNat 8 k)))} = hw.wire {value} : i6"}
    let busy ← Hardware.Emit.expression (fun _ => "%init") cn Reactive.running
    let li : {w : Nat} → Loader.Input w → String := fun p => match p with
      | .init => "%init" | .reset => "%reset" | .busy => busy | .command => hn .command | .data => "%data"
    let selected ← Hardware.Emit.expression hn rn selectedGate
    let read (address : String) : Hardware.Emit.M String :=
      Hardware.Emit.expression (I := Cut) (R := Register) (fun p => match p with | Cut.selection => selected | Cut.address => address) rn
        (Execution.readTree 6 (fun k => .mux (.input Cut.selection) (.reg (.memory true (.word k))) (.reg (.memory false (.word k))))
          (Execution.readTree 8 (fun k => .mux (.input Cut.selection) (.reg (.memory true (.index k))) (.reg (.memory false (.index k)))) (.input Cut.address)))
    let current ← if cached then pure "%r_cached_word" else read (cn .pc)
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
    if cached then
      let ci : {w : Nat} → CachedEmit.CacheInput w → String := fun p => match p with
        | .busy => busy | .oldPC => cn .pc | .newPC => nextPC | .successor => successor | .current => current
      let value ← Hardware.Emit.expression ci (fun _ => "%init") CachedEmit.update
      declarations := declarations.push s!"    %r_cached_word = seq.compreg {value}, %clock : i64"
    for b in #[false, true] do
      let write ← Hardware.Emit.expression hn rn (memoryInputs b .write)
      let mi : {w : Nat} → Store.Input w → String := fun p => match p with
        | .write => write | .cursor => ln .cursor | .data => "%data" | .address => address
      let dn : {w : Nat} → Dense.Register w → String := fun r => match r with
        | .index k => if small then rn (.memory b (.index k)) else "%r_bank" ++ (if b then "1" else "0") ++ "_" ++ Dense.registerLabel r
        | _ => "%r_bank" ++ (if b then "1" else "0") ++ "_" ++ Dense.registerLabel r
      for ⟨w, r⟩ in Dense.registers small do
        let name := "%r_bank" ++ (if b then "1" else "0") ++ "_" ++ Dense.registerLabel r
        match w, r with
        | _, .index k =>
          let value ← if small then Hardware.Emit.expression mi dn (.slice 0 5 (by decide) (Dense.next (.index k)))
            else Hardware.Emit.expression mi dn (Dense.next (.index k))
          declarations := declarations.push s!"    {name} = seq.compreg {value}, %clock : i{if small then 5 else 6}"
        | _, r =>
          let value ← Hardware.Emit.expression mi dn (Dense.next r)
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
  return "module attributes {circt.loweringOptions = \"disallowPackedArrays,disallowLocalVariables,locationInfoStyle=none\"} {\n  hw.module @pinwheel_atomic_" ++ (if small then "small_" else "") ++ "dense" ++ (if cached then "_cached" else "") ++ "(" ++
    String.intercalate ", " ports.toList ++ ") {\n    %clock = seq.to_clock %clk\n" ++
    String.intercalate "\n" (buffer.lines ++ result.1 ++ #[out]).toList ++ "\n  }\n}\n"

end Pinwheel.Hardware.Loader.Machine.DenseEmit
