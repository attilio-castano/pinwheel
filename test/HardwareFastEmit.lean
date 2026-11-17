import Lean
import Pinwheel.Hardware.FastEmit

open Lean Elab Command Pinwheel.Hardware

namespace HardwareFastEmitTests

abbrev Pin (_ : Nat) := Nat
abbrev E := Expr Pin Pin

structure Output (w : Nat) where
  index : Nat
  expression : E w

def output (index : Nat) (e : E w) : Sigma Output := ⟨w, ⟨index, e⟩⟩

def circuit : Circuit Pin Pin Output where
  next := fun {w} r => .mux (.input 0) (.sub (.reg r) (.lit (BitVec.ofNat w 1))) (.input r)
  output := fun o => o.expression

def label (stem : String) {w : Nat} (p : Pin w) : String := s!"{stem}_{w}_{p}"
def outputLabel {w : Nat} (p : Output w) : String := s!"out_{w}_{p.index}"

def ports (widths : List Nat) : Array (Sigma Pin) :=
  (widths.flatMap fun w => [⟨w, 0⟩, ⟨w, 1⟩, ⟨w, 2⟩]).toArray

def emit (fast : Bool) (name stem : String) (inputs registers : Array (Sigma Pin))
    (outputs : Array (Sigma Output)) : Except String String :=
  if fast then FastEmit.moduleText name circuit inputs registers outputs
    (label stem) (label (stem ++ "reg")) outputLabel
  else Emit.moduleText name circuit inputs registers outputs
    (label stem) (label (stem ++ "reg")) outputLabel

def same : Except String String → Except String String → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

/-- Calls both compiled implementations and compares complete bytes, including
operation order, interning, labels, port declarations, clocks and errors. -/
def compare (name stem : String) (inputs registers : Array (Sigma Pin))
    (outputs : Array (Sigma Output)) : IO (Except String String) := do
  let slow := emit false name stem inputs registers outputs
  let fast := emit true name stem inputs registers outputs
  unless same fast slow do throw (IO.userError s!"FastEmit byte mismatch in {name}")
  return fast

@[noinline] def shared (w depth : Nat) : E w :=
  match depth with
  | 0 => .input 1
  | n+1 => let child := shared w n; .band child child

/-- Both recursive calls allocate independently, with structurally identical
leaves. The nonce is deliberately not part of the exported expression. -/
@[noinline] def unshared (w depth nonce : Nat) : E w :=
  match depth with
  | 0 => .input (nonce % 1 + 1)
  | n+1 => .band (unshared w n (nonce*2)) (unshared w n (nonce*2+1))

/-- Every constructor, including full-width/boundary slices and integer literals
above the machine-word range; duplicate outputs exercise exact op interning. -/
def fixtures (w : Nat) : Array (Sigma Output) :=
  let x : E w := .input 1
  let y : E w := .reg 2
  let constant : E w := .lit (BitVec.ofNat w (2^w-1))
  let pair : E (w+w) := .concat x y
  #[output 0 x, output 1 y, output 2 constant, output 3 (.inv x),
    output 4 (.band x y), output 5 (.sub x y), output 6 (.zero x),
    output 7 (.equal x y), output 8 (.ult x y),
    output 9 (.mux (.input 0) (.sub x y) (.inv y)), output 10 pair,
    output 11 (.slice 0 w (by omega) pair), output 12 (.slice w w (by omega) pair),
    output 13 (.slice 0 w (by omega) x),
    output 14 (shared w 9), output 15 (unshared w 7 0),
    output 16 (shared w 9), output 17 (.lit (BitVec.ofNat w (2^w))) ]

def compatibility : IO Nat := do
  let widths := [1,2,3,8,17,31,32,63,64,65,127,128]
  let mut count := 0
  for w in widths do
    for regs in [#[], (#[⟨w, 2⟩] : Array (Sigma Pin))] do
      let result ← compare s!"constructors_{w}" "a" (ports [1,w]) regs (fixtures w)
      match result with
      | .error e => throw (IO.userError s!"Positive-width fixture failed: {e}")
      | .ok _ => pure ()
      count := count+1
  -- The exact same captured Expr objects cross module boundaries with different
  -- naming closures. No memo entry may survive from the first to the second.
  let mixed := (widths.map fixtures).foldl (· ++ ·) #[]
  let a ← compare "mixed_a" "first" (ports widths) (ports widths) mixed
  let b ← compare "mixed_b" "second" (ports widths) (ports widths) mixed
  unless !(same a b) do throw (IO.userError "Module naming contexts were conflated")
  count := count+2
  let _ ← compare "empty" "unused" #[] #[] #[]
  let _ ← compare "registers_only" "a" (ports [1,8]) #[⟨8,2⟩] #[]
  let _ ← compare "inputs_only" "a" (ports [0,1,8]) #[] #[]
  return count+3

/-- A positive result containing a width-zero child must fail too. An unused
width-zero input retains the old emitter's behavior (tested above). -/
def zeroWidths : IO Nat := do
  let bad : Array (Sigma Output) := #[
    output 0 (.lit (0#0)), output 1 (.input (w := 0) 0),
    output 2 (.reg (w := 0) 0), output 3 (.zero (.lit (0#0))),
    output 4 (.equal (.lit (0#0)) (.lit (0#0))),
    output 5 (.concat (.lit (0#0)) (.lit (1#1))),
    output 6 (.concat (.lit (1#1)) (.lit (0#0))),
    output 7 (.slice 0 0 (by decide) (.lit (1#1))),
    output 8 (.mux (.lit (1#1)) (.lit (0#0)) (.lit (0#0))) ]
  for e in bad do
    let result ← compare "zero_width" "a" (ports [0,1]) #[] #[e]
    unless same result (.error "CIRCT emission requires positive signal widths") do
      throw (IO.userError "Zero-width error was masked")
  let result ← compare "zero_register" "a" (ports [0,1]) #[⟨0,0⟩] #[]
  unless same result (.error "CIRCT emission requires positive signal widths") do
    throw (IO.userError "Zero-width register error was masked")
  return bad.size+1

/-- A depth-256 DAG has only 257 nodes but its expanded tree has more than 2^256
leaves. Running this through the public wrapper tests that compiled execution
actually selects the memoized implementation. It does not invoke the original
exponential traversal or establish any theorem about unsafe code. -/
def stress : IO Nat := do
  let start ← IO.monoMsNow
  let depth := 256
  let mut out := #[]
  for w in [1,8,32,65,128] do
    let e := shared w depth
    for k in [:8] do out := out.push (output k e)
  let result := emit true "shared_stress" "x" (ports [1,8,32,65,128]) #[] out
  let text ← match result with
    | .ok text => pure text
    | .error e => throw (IO.userError e)
  let ands := (text.splitOn "\n").filter (fun line => (line.splitOn " = comb.and ").length == 2)
  unless ands.length == 5*depth do throw (IO.userError s!"Lost/cross-width cached operations: {ands.length}")
  -- The exact final signal for each width must occur eight times on hw.output.
  let outputLines := (text.splitOn "\n").filter (·.startsWith "    hw.output ")
  let signals := ((List.range 5).flatMap fun k => List.replicate 8 s!"%v{(k+1)*depth-1}")
  let types := ([1,8,32,65,128].flatMap fun w => List.replicate 8 s!"i{w}")
  let expected := "    hw.output " ++ String.intercalate ", " signals ++ " : " ++
    String.intercalate ", " types
  unless outputLines == [expected] do
    throw (IO.userError "Shared outputs reused a signal from a different width or level")
  let elapsed := (← IO.monoMsNow)-start
  if elapsed > 30000 then throw (IO.userError s!"Shared DAG emission took {elapsed}ms")
  IO.println s!"Shared DAG: 5 widths × {depth} levels, 40 outputs, {ands.length} operations, {elapsed}ms"
  return ands.length

end HardwareFastEmitTests

/-- Audit the safe logical API only. The native replacement is explicitly
unsafe and is validated as an untrusted exporter, never used as proof evidence. -/
elab "#audit_fast_emit" : command => do
  for name in [``FastEmit.moduleText, ``FastEmit.moduleText_eq] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
    unless bad.isEmpty do throwError "Unapproved FastEmit logical axioms in {name}: {bad}"
  logInfo "FastEmit logical API: 2 declarations, standard axioms only; native exporter remains untrusted."

#audit_fast_emit

-- Kernel reduction checks the safe delegation independently of native execution.
example : FastEmit.moduleText "empty" HardwareFastEmitTests.circuit #[] #[] #[]
    (HardwareFastEmitTests.label "i") (HardwareFastEmitTests.label "r")
    HardwareFastEmitTests.outputLabel =
  Emit.moduleText "empty" HardwareFastEmitTests.circuit #[] #[] #[]
    (HardwareFastEmitTests.label "i") (HardwareFastEmitTests.label "r")
    HardwareFastEmitTests.outputLabel := rfl

def main : IO Unit := do
  let comparisons ← HardwareFastEmitTests.compatibility
  let errors ← HardwareFastEmitTests.zeroWidths
  let operations ← HardwareFastEmitTests.stress
  IO.println s!"FastEmit: {comparisons} complete byte comparisons, {errors} zero-width errors, {operations} shared operations."
