import Pinwheel.Hardware.Emit

/-! Target-local native emitter optimization. The logical function remains the
existing safe emitter; native evaluation memoizes expression object identities
before descending. Retained references prevent pointer-address reuse. This is
not a compiler-correctness proof: generated artifacts still require replay and
saved next-state equivalence checks. It adds no circuit storage or signals. -/
namespace Pinwheel.Hardware.Buffered.MemoEmit

structure Buffer (I R : Nat → Type) where
  serial : Nat := 0
  lines : Array String := #[]
  operations : Std.HashMap String String := {}
  pointers : Std.HashMap (Nat × USize) String := {}
  retained : Array (Sigma (Expr I R)) := #[]

abbrev M I R := StateT (Buffer I R) (Except String)

private def bindOp (operation : String) : M I R String := do
  let s : Buffer I R ← get
  if let some name := s.operations[operation]? then return name
  let name := s!"%v{s.serial}"
  set ({s with
    serial := s.serial + 1
    lines := s.lines.push s!"    {name} = {operation}"
    operations := s.operations.insert operation name } : Buffer I R)
  return name

/-- Traverses exactly the Expr constructors interpreted by Expr.eval. -/
unsafe def expression (inputName : {w : Nat} → I w → String)
    (registerName : {w : Nat} → R w → String) {w : Nat} (e : Expr I R w) : M I R String := do
  let key := (w, ptrAddrUnsafe e)
  if let some name := (← get).pointers[key]? then return name
  -- Retain the object before traversing children, so cached addresses cannot be
  -- recycled after a temporary expression leaves scope.
  modify fun s => {s with retained := s.retained.push ⟨w,e⟩}
  let value ← match w, e with
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

  modify fun s => {s with pointers := s.pointers.insert key value}
  return value

unsafe def moduleTextImpl (name : String) (c : Circuit I R O)
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
    return (declarations, values)  : M I R _).run {}
  let ports := inputs.map (fun ⟨w, i⟩ => s!"in %{inputLabel i} : i{w}") ++
    outputs.map (fun ⟨w, o⟩ => s!"out {outputLabel o} : i{w}")
  let clockPort := if registers.isEmpty then #[] else #["in %clk : i1"]
  let clockLine := if registers.isEmpty then #[] else #["    %clock = seq.to_clock %clk"]
  let outLine := "    hw.output " ++ String.intercalate ", " result.2.toList ++ " : " ++
    String.intercalate ", " (outputs.map (fun ⟨w, _⟩ => s!"i{w}")).toList
  return "module attributes {circt.loweringOptions = \"disallowPackedArrays,disallowLocalVariables,locationInfoStyle=none\"} {\n  hw.module @" ++ name ++ "(" ++ String.intercalate ", " (clockPort ++ ports).toList ++ ") {\n" ++
    String.intercalate "\n" (clockLine ++ buffer.lines ++ result.1 ++ #[outLine]).toList ++ "\n  }\n}\n"

@[implemented_by moduleTextImpl]
def moduleText (name : String) (c : Circuit I R O)
    (inputs : Array (Sigma I)) (registers : Array (Sigma R)) (outputs : Array (Sigma O))
    (inputLabel : {w : Nat} → I w → String) (registerLabel : {w : Nat} → R w → String)
    (outputLabel : {w : Nat} → O w → String) : Except String String :=
  Emit.moduleText name c inputs registers outputs inputLabel registerLabel outputLabel

end Pinwheel.Hardware.Buffered.MemoEmit
