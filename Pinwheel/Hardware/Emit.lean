import Pinwheel.Hardware.Countdown

/-! Small deterministic emitter for the represented operations. Its translation is not proved. -/
namespace Pinwheel.Hardware.Emit

structure Buffer where
  serial : Nat := 0
  lines : Array String := #[]

abbrev M := StateT Buffer (Except String)

private def bindOp (operation : String) : M String := do
  let s : Buffer ← get
  let name := s!"%v{s.serial}"
  set ({ serial := s.serial + 1, lines := s.lines.push s!"    {name} = {operation}" } : Buffer)
  return name

/-- Traverses exactly the Expr constructors interpreted by Expr.eval. -/
def expression (inputName : {w : Nat} → I w → String)
    (registerName : {w : Nat} → R w → String) {w : Nat} (e : Expr I R w) : M String := do
  match w, e with
  | 0, _ => throw "CIRCT emission requires positive signal widths"
  | _, .input i => return inputName i
  | _, .reg r => return registerName r
  | w, .lit v => bindOp s!"hw.constant {v.toNat} : i{w}"
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

end Pinwheel.Hardware.Emit
