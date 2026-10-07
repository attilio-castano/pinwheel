import Pinwheel.Hardware.Buffered.MemoBind
import Pinwheel.Hardware.Buffered.ReactiveEmit

/-! Independent finite qualification of the native substitution cache.
The reference expression is ordinary `Expr.bind`, never `MemoBind.bind`.
These tests exercise native execution and byte emission, not a universal
compiler or native implementation theorem. -/
namespace Pinwheel.Hardware.Buffered.SramMemoBindChecks
open Pinwheel.Hardware

inductive Pin : Nat → Type where
  | value : Nat → Pin w

inductive Register : Nat → Type where
  | value : Nat → Register w

abbrev E := Expr Pin Register

private def pin (k : Nat) : E w := .input (.value k)
private def register (k : Nat) : E w := .reg (.value k)
private def sampled : E 1 := pin 0
private def shared : E 144 := .mux sampled (register 1) (register 2)

private def fixtures : Array (String × Sigma E) :=
  #[("input", ⟨3, pin 1⟩),
    ("register", ⟨144, register 1⟩),
    ("zero_literal", ⟨0, .lit 0⟩),
    ("zero_input", ⟨0, pin 2⟩),
    ("zero_register", ⟨0, register 2⟩),
    ("wide_literal", ⟨144, .lit (BitVec.ofNat 144 (2^143+170))⟩),
    ("concat", ⟨16, .concat (a := 8) (b := 8) (pin 1) (register 2)⟩),
    ("inv", ⟨16, .inv (register 3)⟩),
    ("band", ⟨56, .band (register 1) (.lit 42405)⟩),
    ("sub", ⟨64, .sub (pin 1) (.lit 17)⟩),
    ("slice", ⟨92, .slice 7 92 (by decide) shared⟩),
    ("equal", ⟨1, .equal shared (register 3)⟩),
    ("ult", ⟨1, .ult (pin 2 : E 6) (.lit 16)⟩),
    ("zero", ⟨1, .zero (register 1 : E 8)⟩),
    ("mux", ⟨144, shared⟩),
    ("mux_literal", ⟨144, .mux sampled (.lit 170) (.lit 85)⟩),
    ("mux_mixed", ⟨144, .mux sampled shared (.lit 170)⟩),
    ("mux_reverse", ⟨144, .mux sampled (.lit 85) shared⟩),
    ("shared_equal", ⟨1, .equal shared shared⟩),
    ("shared_slices", ⟨16, .concat (.slice 9 8 (by decide) shared)
      (.slice 47 8 (by decide) shared)⟩),
    ("shared_concat", ⟨288, .concat shared shared⟩),
    ("shared_dag", ⟨144, .mux (pin 1) (.mux sampled shared (register 3))
      (.mux sampled (register 4) shared)⟩),
    ("zero_concat", ⟨144, .concat (a := 0) (b := 144) (.lit 0) shared⟩),
    ("zero_slice", ⟨0, .slice 144 0 (by decide) shared⟩)] ++
    Array.ofFn (fun k : Fin 16 =>
      (s!"indexed_leaf_{k.val}", ⟨144, .mux sampled (register k.val) (pin k.val)⟩))

-- The same source leaf binds to different input/register shapes and widths.
-- All reference transformations below use these ordinary expressions directly.
private def inputExpr (mode : Nat) : {w : Nat} → Pin w → E w := fun {w} p =>
  match p with
  | .value k =>
    if mode == 0 then pin k
    else if mode == 1 then .mux (pin 0) (.inv (pin (k+8))) (register (k+16))
    else if mode == 2 then .sub (register (k+8)) (.lit (BitVec.ofNat w (k+3)))
    else .slice 1 w (by omega)
      (.concat (a := 1) (b := w) (.zero (register 0 : E 8)) (pin (k+16)))

private def registerExpr (mode : Nat) : {w : Nat} → Register w → E w := fun {w} r =>
  match r with
  | .value k =>
    if mode == 0 then register k
    else if mode == 1 then .band (register (k+8)) (.lit (BitVec.ofNat w ((2^w-1)/3)))
    else if mode == 2 then .mux (.zero (pin 0 : E 8)) (register (k+16))
      (.sub (pin (k+8)) (.lit (BitVec.ofNat w (k+1))))
    else .inv (.mux (pin 0) (register (k+8)) (pin (k+16)))

private def value (w k seed : Nat) : BitVec w := BitVec.ofNat w (
  if seed == 0 then 0
  else if seed == 1 then 2^w-1
  else if seed == 2 then 2^(w-1)
  else if seed == 3 then (2^w-1)/3
  else if seed == 4 then 2 * ((2^w-1)/3)
  else seed * 104729 + k * 7340033 + 2863311530 + 2^(w-1))

private def inputs (seed salt : Nat) : Values Pin := fun {w} p =>
  match p with
  | .value k => value w k (seed + salt)

private def state (seed salt : Nat) : Values Register := fun {w} r =>
  match r with
  | .value k => value w (k+7) (seed + 3*salt)

inductive Probe : Nat → Type where
  | result : Nat → Probe w

private def emitFixtures : Array (Sigma E) :=
  #[⟨144, register 1⟩, ⟨144, shared⟩, ⟨288, .concat shared shared⟩,
    ⟨1, .equal shared (register 1)⟩]

private def composedFixtures : Array (Sigma E) :=
  emitFixtures ++ #[⟨0, .slice 144 0 (by decide) shared⟩]

private def transform (mode : Nat) (native : Bool) (e : E w) : E w :=
  if native then MemoBind.bind (inputExpr mode) (registerExpr mode) e
  else e.bind (inputExpr mode) (registerExpr mode)

private def output (mode : Nat) (native : Bool) : {w : Nat} → Probe w → E w := fun {w} p =>
  match p with
  | .result k =>
    if let some ⟨v,e⟩ := emitFixtures[k]? then
      if h : v = w then h ▸ transform mode native e else .lit 0
    else .lit 0

private def circuit (mode : Nat) (native : Bool) : Circuit Pin Register Probe where
  next := fun r => .reg r
  output := output mode native

private def emissionInputs : Array (Sigma Pin) :=
  #[1,8,144].flatMap fun w => Array.ofFn (fun k : Fin 19 => ⟨w,.value k.val⟩)

private def emissionRegisters : Array (Sigma Register) :=
  #[1,8,144].flatMap fun w => Array.ofFn (fun k : Fin 19 => ⟨w,.value k.val⟩)

private def emissionOutputs : Array (Sigma Probe) :=
  emitFixtures.mapIdx (fun k ⟨w,_⟩ => ⟨w,.result k⟩)

private def pinLabel : {w : Nat} → Pin w → String := fun {w} p =>
  match p with
  | .value k => s!"input{w}_{k}"

private def registerLabel : {w : Nat} → Register w → String := fun {w} r =>
  match r with
  | .value k => s!"state{w}_{k}"

private def probeLabel : {w : Nat} → Probe w → String := fun p =>
  match p with
  | .result k => s!"probe{k}"

private def checkEmission : IO Nat := do
  let mut checks := 0
  for mode in List.range 4 do
    let safe ← match Emit.moduleText "bind_probe" (circuit mode false)
        emissionInputs emissionRegisters emissionOutputs pinLabel registerLabel probeLabel with
      | .ok text => pure text
      | .error e => throw (IO.userError e)
    for native in [false,true] do
      let viaSafe ← match Emit.moduleText "bind_probe" (circuit mode native)
          emissionInputs emissionRegisters emissionOutputs pinLabel registerLabel probeLabel with
        | .ok text => pure text
        | .error e => throw (IO.userError e)
      let viaMemo ← match MemoEmit.moduleText "bind_probe" (circuit mode native)
          emissionInputs emissionRegisters emissionOutputs pinLabel registerLabel probeLabel with
        | .ok text => pure text
        | .error e => throw (IO.userError e)
      unless safe == viaSafe && safe == viaMemo do
        throw (IO.userError s!"Ordinary bind/native bind or safe/memo emitter byte mismatch: mode={mode}")
      checks := checks + 2
  return checks

end Pinwheel.Hardware.Buffered.SramMemoBindChecks

open Pinwheel.Hardware Pinwheel.Hardware.Buffered.SramMemoBindChecks
open Pinwheel.Hardware.Buffered

unsafe def main : IO Unit := do
  let mut checks := 0
  for (name, ⟨_,e⟩) in fixtures do
    for mode in List.range 4 do
      let actual := MemoBind.bind (inputExpr mode) (registerExpr mode) e
      let direct := MemoBind.bindMemo (inputExpr mode) (registerExpr mode) e
      let reference := e.bind (inputExpr mode) (registerExpr mode)
      for seed in List.range 8 do
        for salt in List.range 4 do
          let i : Values Pin := inputs seed salt
          let s : Values Register := state seed salt
          let expected := reference.eval i s
          unless actual.eval i s == expected do
            throw (IO.userError s!"Public bind mismatch: {name}; mode={mode}; seed={seed}; salt={salt}")
          unless direct.eval i s == expected do
            throw (IO.userError s!"Direct native bind mismatch: {name}; mode={mode}; seed={seed}; salt={salt}")
          checks := checks + 2
  let mut composedChecks := 0
  -- A prospective-state substitution operates on an already adapted DAG.
  -- Qualify both calls independently against two ordinary bind operations.
  for ⟨_,e⟩ in composedFixtures do
    for mode in List.range 4 do
      let second := (mode + 1) % 4
      let actual := MemoBind.bind (inputExpr second) (registerExpr second)
        (MemoBind.bind (inputExpr mode) (registerExpr mode) e)
      let direct := MemoBind.bindMemo (inputExpr second) (registerExpr second)
        (MemoBind.bindMemo (inputExpr mode) (registerExpr mode) e)
      let reference := (e.bind (inputExpr mode) (registerExpr mode)).bind
        (inputExpr second) (registerExpr second)
      for seed in List.range 8 do
        for salt in List.range 4 do
          let i : Values Pin := inputs seed salt
          let s : Values Register := state seed salt
          let expected := reference.eval i s
          unless actual.eval i s == expected && direct.eval i s == expected do
            throw (IO.userError s!"Composed ordinary bind mismatch: mode={mode}; seed={seed}; salt={salt}")
          composedChecks := composedChecks + 2
  let emitted ← checkEmission
  IO.println s!"Memo bind finite checks: {fixtures.size} fixtures; {checks} Expr.bind evaluations; {emitted} byte-identical emitter comparisons."
  IO.println s!"Memo bind composed checks: {composedFixtures.size} fixtures; {composedChecks} two-pass Expr.bind evaluations."
  IO.println "Covers every Expr constructor, shared DAGs, zero/144/288 widths, indexed leaves, four substitutions, boundary values, input/register remapping and safe/native emission. No universal native/compiler/emitter claim."
