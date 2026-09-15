import Pinwheel.Hardware.Core

/-! Small deterministic emitter for the represented operations. Its translation is not proved. -/
namespace Pinwheel.Hardware.Emit

structure Buffer where
  serial : Nat := 0
  lines : Array String := #[]
  operations : Std.HashMap String String := {}

abbrev M := StateT Buffer (Except String)

private def bindOp (operation : String) : M String := do
  let s : Buffer ← get
  if let some name := s.operations[operation]? then return name
  let name := s!"%v{s.serial}"
  set ({
    serial := s.serial + 1
    lines := s.lines.push s!"    {name} = {operation}"
    operations := s.operations.insert operation name } : Buffer)
  return name

/-- Traverses exactly the Expr constructors interpreted by Expr.eval. -/
def expression (inputName : {w : Nat} → I w → String)
    (registerName : {w : Nat} → R w → String) {w : Nat} (e : Expr I R w) : M String := do
  match w, e with
  | 0, _ => throw "CIRCT emission requires positive signal widths"
  | _, .input i => return inputName i
  | _, .reg r => return registerName r
  | w, .lit v => bindOp s!"hw.constant {v.toNat} : i{w}"
  | _, .concat (a := a) (b := b) x y =>
    let hi ← expression inputName registerName x
    let lo ← expression inputName registerName y
    bindOp s!"comb.concat {hi}, {lo} : i{a}, i{b}"
  | w, .inv x =>
    let a ← expression inputName registerName x
    let ones ← bindOp s!"hw.constant {2^w - 1} : i{w}"
    bindOp s!"comb.xor {a}, {ones} : i{w}"
  | w, .band x y =>
    let a ← expression inputName registerName x
    let b ← expression inputName registerName y
    bindOp s!"comb.and {a}, {b} : i{w}"
  | w, .sub x y =>
    let a ← expression inputName registerName x
    let b ← expression inputName registerName y
    bindOp s!"comb.sub {a}, {b} : i{w}"
  | _, .zero (w := v) x =>
    let a ← expression inputName registerName x
    let z ← bindOp s!"hw.constant 0 : i{v}"
    bindOp s!"comb.icmp eq {a}, {z} : i{v}"
  | _, .slice (w := v) start len _ x =>
    let a ← expression inputName registerName x
    bindOp s!"comb.extract {a} from {start} : (i{v}) -> i{len}"
  | _, .equal (w := v) x y =>
    let a ← expression inputName registerName x
    let b ← expression inputName registerName y
    bindOp s!"comb.icmp eq {a}, {b} : i{v}"
  | _, .ult (w := v) x y =>
    let a ← expression inputName registerName x
    let b ← expression inputName registerName y
    bindOp s!"comb.icmp ult {a}, {b} : i{v}"
  | w, .mux c t f =>
    let select ← expression inputName registerName c
    let yes ← expression inputName registerName t
    let no ← expression inputName registerName f
    bindOp s!"comb.mux {select}, {yes}, {no} : i{w}"

private def inputName : {w : Nat} → Countdown.Input w → String
  | _, .reset => "%reset"
  | _, .load => "%load"
  | _, .duration => "%duration"

private def registerName : {w : Nat} → Countdown.Register w → String
  | _, .remaining => "%r_remaining"
  | _, .active => "%r_active"

/-- The module adapter declares ports/registers; all logic comes from Countdown.circuit. -/
def countdown : Except String String := do
  let (ports, buffer) ← (do
    let remaining ← expression inputName registerName (Countdown.circuit.next .remaining)
    let active ← expression inputName registerName (Countdown.circuit.next .active)
    let outRemaining ← expression inputName registerName (Countdown.circuit.output .remaining)
    let outActive ← expression inputName registerName (Countdown.circuit.output .active)
    let outBoundary ← expression inputName registerName (Countdown.circuit.output .boundary)
    return (remaining, active, outRemaining, outActive, outBoundary) : M _).run {}
  let (remaining, active, outRemaining, outActive, outBoundary) := ports
  return "module {\n" ++
    "  hw.module @pinwheel_countdown(in %clk : i1, in %reset : i1, in %load : i1, in %duration : i8, out remaining : i8, out active : i1, out boundary : i1) {\n" ++
    "    %clock = seq.to_clock %clk\n" ++
    String.intercalate "\n" buffer.lines.toList ++ "\n" ++
    s!"    %r_remaining = seq.compreg {remaining}, %clock : i8\n" ++
    s!"    %r_active = seq.compreg {active}, %clock : i1\n" ++
    s!"    hw.output {outRemaining}, {outActive}, {outBoundary} : i8, i1, i1\n" ++
    "  }\n}\n"

/-- The adapter enumerates ports/registers; expression emission supplies every next-state gate. -/
def moduleText (name : String) (c : Circuit I R O)
    (inputs : Array (Sigma I)) (registers : Array (Sigma R)) (outputs : Array (Sigma O))
    (inputLabel : {w : Nat} → I w → String) (registerLabel : {w : Nat} → R w → String)
    (outputLabel : {w : Nat} → O w → String) : Except String String := do
  let (result, buffer) ← (do
    let mut declarations : Array String := #[]
    for ⟨w, r⟩ in registers do
      let value ← expression (fun i => "%" ++ inputLabel i) (fun r => "%r_" ++ registerLabel r) (c.next r)
      declarations := declarations.push s!"    %r_{registerLabel r} = seq.compreg {value}, %clock : i{w}"
    let mut values : Array String := #[]
    for ⟨_, o⟩ in outputs do
      values := values.push (← expression (fun i => "%" ++ inputLabel i) (fun r => "%r_" ++ registerLabel r) (c.output o))
    return (declarations, values) : M _).run {}
  let ports := inputs.map (fun ⟨w, i⟩ => s!"in %{inputLabel i} : i{w}") ++
    outputs.map (fun ⟨w, o⟩ => s!"out {outputLabel o} : i{w}")
  let clockPort := if registers.isEmpty then #[] else #["in %clk : i1"]
  let clockLine := if registers.isEmpty then #[] else #["    %clock = seq.to_clock %clk"]
  let outLine := "    hw.output " ++ String.intercalate ", " result.2.toList ++ " : " ++
    String.intercalate ", " (outputs.map (fun ⟨w, _⟩ => s!"i{w}")).toList
  return "module attributes {circt.loweringOptions = \"disallowPackedArrays,disallowLocalVariables,locationInfoStyle=none\"} {\n  hw.module @" ++ name ++ "(" ++ String.intercalate ", " (clockPort ++ ports).toList ++ ") {\n" ++
    String.intercalate "\n" (clockLine ++ buffer.lines ++ result.1 ++ #[outLine]).toList ++ "\n  }\n}\n"

def coreInputs : Array (Sigma Core.Input) :=
  #[⟨1, .initialize⟩, ⟨1, .reset⟩, ⟨1, .start⟩, ⟨1, .commit⟩, ⟨1, .sample⟩, ⟨3, .idle⟩] ++
    Array.ofFn (fun k : Fin 32 => ⟨16, .word k⟩)

def coreRegisters : Array (Sigma Core.Register) :=
  Array.ofFn (fun k : Fin 32 => ⟨16, .word k⟩) ++
    #[⟨3, .idle⟩, ⟨1, .valid⟩, ⟨2, .status⟩, ⟨5, .pc⟩, ⟨8, .remaining⟩, ⟨1, .timerActive⟩, ⟨3, .levels⟩] ++
    Array.ofFn (fun k : Fin 8 => ⟨1, .sample k⟩)

def coreOutputs : Array (Sigma Core.Output) :=
  #[⟨1, .valid⟩, ⟨2, .status⟩, ⟨5, .pc⟩, ⟨8, .remaining⟩, ⟨1, .timerActive⟩, ⟨3, .levels⟩,
    ⟨1, .busy⟩, ⟨1, .completed⟩, ⟨1, .fault⟩] ++ Array.ofFn (fun k : Fin 8 => ⟨1, .sample k⟩)

def coreInputLabel : {w : Nat} → Core.Input w → String
  | _, .initialize => "initialize" | _, .reset => "reset" | _, .start => "start"
  | _, .commit => "commit" | _, .sample => "sample" | _, .idle => "idle"
  | _, .word k => s!"word{k.val}"

def coreRegisterLabel : {w : Nat} → Core.Register w → String
  | _, .word k => s!"word{k.val}" | _, .idle => "idle" | _, .valid => "valid"
  | _, .status => "status" | _, .pc => "pc" | _, .remaining => "remaining"
  | _, .timerActive => "timer_active" | _, .levels => "levels" | _, .sample k => s!"sample{k.val}"

def coreOutputLabel : {w : Nat} → Core.Output w → String
  | _, .valid => "valid" | _, .status => "status" | _, .pc => "pc" | _, .remaining => "remaining"
  | _, .timerActive => "timer_active" | _, .levels => "levels" | _, .sample k => s!"sample{k.val}"
  | _, .busy => "busy" | _, .completed => "completed" | _, .fault => "fault"

def core : Except String String :=
  moduleText "pinwheel_core" Core.circuit coreInputs coreRegisters coreOutputs
    coreInputLabel coreRegisterLabel coreOutputLabel

inductive WordInput : Nat → Type where | word : WordInput 16
inductive NoRegister : Nat → Type

def decoderCircuit : Circuit WordInput NoRegister Decode.Port where
  next := fun r => nomatch r
  output := Decode.logic (.input .word)

def decoder : Except String String :=
  moduleText "pinwheel_decoder" decoderCircuit #[⟨16, .word⟩] #[]
    #[⟨2, .kind⟩, ⟨3, .levels⟩, ⟨8, .duration⟩, ⟨1, .capture⟩, ⟨3, .slot⟩]
    (fun _ => "word") (fun r => nomatch r)
    (fun p => match p with
      | .kind => "kind" | .levels => "levels" | .duration => "duration"
      | .capture => "capture" | .slot => "slot")

end Pinwheel.Hardware.Emit
