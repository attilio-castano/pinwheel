import Pinwheel.Hardware.Emit

/-!
An optional native traversal optimization for the existing, untrusted CIRCT
exporter. The logical API is definitionally the original emitter; that fact is
not a correctness proof for the unsafe implementation selected by the compiler.
Generated RTL still requires its ordinary replay/readback validation.

The cache keys include both object address and signal width. Every cached node
is retained until this module finishes, so its address cannot be recycled while
its entry is live. A hit checks the retained node's width and address. There is
no global cache: a module fixes its input/register naming context. Operation
string interning and depth-first emission order remain the original emitter's.
-/
namespace Pinwheel.Hardware.FastEmit

private structure Entry (I R : Nat → Type) where
  node : Sigma (Expr I R)
  signal : String

private structure Buffer (I R : Nat → Type) extends Emit.Buffer where
  nodes : Std.HashMap (USize × Nat) (Entry I R) := {}

private abbrev M (I R : Nat → Type) := StateT (Buffer I R) (Except String)

private def bindOp (operation : String) : M I R String := do
  let s ← get
  if let some name := s.operations[operation]? then return name
  let name := s!"%v{s.serial}"
  set { s with
    serial := s.serial + 1
    lines := s.lines.push s!"    {name} = {operation}"
    operations := s.operations.insert operation name }
  return name

private unsafe def expression (inputName : {w : Nat} → I w → String)
    (registerName : {w : Nat} → R w → String) {w : Nat} (e : Expr I R w) : M I R String := do
  if w == 0 then throw "CIRCT emission requires positive signal widths"
  let address := ptrAddrUnsafe e
  let key := (address, w)
  let state ← get
  if let some entry := state.nodes[key]? then
    if entry.node.1 == w && ptrAddrUnsafe entry.node.2 == address then
      return entry.signal
    else
      throw "FastEmit identity cache inconsistency"
  let signal ← match w, e with
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
  modify fun state => { state with nodes := state.nodes.insert key ⟨⟨w, e⟩, signal⟩ }
  return signal

/-- Native implementation only. Its pointer cache is fresh for this complete module,
so labels and signal names cannot escape their input/register naming context. -/
unsafe def fastModuleText (name : String) (c : Circuit I R O)
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
    return (declarations, values) : M I R _).run {}
  let ports := inputs.map (fun ⟨w, i⟩ => s!"in %{inputLabel i} : i{w}") ++
    outputs.map (fun ⟨w, o⟩ => s!"out {outputLabel o} : i{w}")
  let clockPort := if registers.isEmpty then #[] else #["in %clk : i1"]
  let clockLine := if registers.isEmpty then #[] else #["    %clock = seq.to_clock %clk"]
  let outLine := "    hw.output " ++ String.intercalate ", " result.2.toList ++ " : " ++
    String.intercalate ", " (outputs.map (fun ⟨w, _⟩ => s!"i{w}")).toList
  return "module attributes {circt.loweringOptions = \"disallowPackedArrays,disallowLocalVariables,locationInfoStyle=none\"} {\n  hw.module @" ++ name ++ "(" ++ String.intercalate ", " (clockPort ++ ports).toList ++ ") {\n" ++
    String.intercalate "\n" (clockLine ++ buffer.lines ++ result.1 ++ #[outLine]).toList ++ "\n  }\n}\n"

/-- Exact logical delegation to the original exporter, with an isolated native
memoized traversal. No native-code preservation theorem is asserted. -/
@[implemented_by fastModuleText]
def moduleText (name : String) (c : Circuit I R O)
    (inputs : Array (Sigma I)) (registers : Array (Sigma R)) (outputs : Array (Sigma O))
    (inputLabel : {w : Nat} → I w → String) (registerLabel : {w : Nat} → R w → String)
    (outputLabel : {w : Nat} → O w → String) : Except String String :=
  Emit.moduleText name c inputs registers outputs inputLabel registerLabel outputLabel

/-- Equality of the logical definitions only; exported text remains untrusted. -/
theorem moduleText_eq (name : String) (c : Circuit I R O)
    (inputs : Array (Sigma I)) (registers : Array (Sigma R)) (outputs : Array (Sigma O))
    (inputLabel : {w : Nat} → I w → String) (registerLabel : {w : Nat} → R w → String)
    (outputLabel : {w : Nat} → O w → String) :
    moduleText name c inputs registers outputs inputLabel registerLabel outputLabel =
      Emit.moduleText name c inputs registers outputs inputLabel registerLabel outputLabel := rfl

end Pinwheel.Hardware.FastEmit
