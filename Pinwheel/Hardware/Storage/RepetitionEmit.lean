import Pinwheel.Hardware.Storage.RepetitionStore

namespace Pinwheel.Hardware.Loader.Machine.RepetitionEmit
open Machine Storage

inductive Select : Nat → Type where | selected : Select 1
inductive Bank : Nat → Type where | field : Bool → Repetition.Register w → Bank w

def moduleText : Except String String := do
  let rn : {w : Nat} → Register w → String := fun r => "%r_" ++ registerLabel r
  let hn : {w : Nat} → Input w → String := fun i => match i with | .command => "%checked_command" | .data => "%checked_data" | _ => "%" ++ inputLabel i
  let cn : {w : Nat} → Reactive.Register w → String := fun r => rn (.core r)
  let ln : {w : Nat} → Loader.Register w → String := fun r => rn (.control r)
  let (result, buffer) ← (do
    let raw : {w : Nat} → Input w → String := fun i => "%" ++ inputLabel i
    let command ← Hardware.Emit.expression raw rn Repetition.hostCommand
    let data ← Hardware.Emit.expression raw rn Repetition.hostData
    modify fun buf => {buf with lines := buf.lines ++ #[s!"    %checked_command = hw.wire {command} : i3", s!"    %checked_data = hw.wire {data} : i64"]}
    let busy ← Hardware.Emit.expression (fun _ => "%init") cn Reactive.running
    let li : {w : Nat} → Loader.Input w → String := fun p => match p with
      | .init => "%init" | .reset => "%reset" | .busy => busy | .command => hn .command | .data => hn .data
    let selected ← Hardware.Emit.expression hn rn selectedGate
    let bn : {w : Nat} → Bank w → String := fun r => match r with
      | .field b p => s!"%r_bank{if b then 1 else 0}_" ++ Repetition.label p
    let rr : {w : Nat} → Repetition.Register w → String := fun r => "%chosen_" ++ Repetition.label r
    for ⟨w, r⟩ in Repetition.registers do
      let value ← Hardware.Emit.expression (I := Select) (R := Bank) (fun _ => selected) bn
        (.mux (.input .selected) (.reg (.field true r)) (.reg (.field false r)))
      modify fun buf => {buf with lines := buf.lines.push s!"    {rr r} = hw.wire {value} : i{w}"}
    let read (address : String) : Hardware.Emit.M String :=
      Hardware.Emit.expression (I := Repetition.Input) (R := Repetition.Register) (fun _ => address) rr Repetition.reader
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
    let ci : {w : Nat} → CachedEmit.CacheInput w → String := fun p => match p with
      | .busy => busy | .oldPC => cn .pc | .newPC => nextPC | .successor => successor | .current => current
    let cached ← Hardware.Emit.expression ci (fun _ => "%init") CachedEmit.update
    declarations := declarations.push s!"    {current} = seq.compreg {cached}, %clock : i64"
    for b in #[false, true] do
      let write ← Hardware.Emit.expression hn rn (memoryInputs b .write)
      let mi : {w : Nat} → Store.Input w → String := fun p => match p with
        | .write => write | .cursor => ln .cursor | .data => "%data" | .address => address
      let rn : {w : Nat} → Repetition.BankRegister w → String := fun r => s!"%r_bank{if b then 1 else 0}_" ++ Repetition.bankLabel r
      for ⟨w, r⟩ in Repetition.bankRegisters do
        let value ← Hardware.Emit.expression mi rn (Repetition.next r)
        declarations := declarations.push s!"    {rn r} = seq.compreg {value}, %clock : i{w}"
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
  return "module attributes {circt.loweringOptions = \"disallowPackedArrays,disallowLocalVariables,locationInfoStyle=none\"} {\n  hw.module @pinwheel_atomic_repetition(" ++
    String.intercalate ", " ports.toList ++ ") {\n    %clock = seq.to_clock %clk\n" ++
    String.intercalate "\n" (buffer.lines ++ result.1 ++ #[out]).toList ++ "\n  }\n}\n"

end Pinwheel.Hardware.Loader.Machine.RepetitionEmit
