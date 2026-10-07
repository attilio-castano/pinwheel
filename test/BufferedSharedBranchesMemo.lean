import Pinwheel.Hardware.Buffered.SharedBranches
import Lean

namespace Pinwheel.Hardware.Buffered.SharedBranches.MemoChecks
open Pinwheel.Hardware

private def row (k : Nat) : Reactive.E 144 := .reg (.word (BitVec.ofNat 6 k))
private def sampled : Reactive.E 1 := .slice 0 1 (by decide) (.reg .stage2)
private def pin : Reactive.E 1 := .slice 1 1 (by decide) (.input .rawInputs)
private def yes : Reactive.E 144 := .lit (BitVec.ofNat 144 170)
private def no : Reactive.E 144 := .lit (BitVec.ofNat 144 85)
private def shared : Reactive.E 144 := .mux sampled (row 0) (row 15)

private def fixtures : Array (String × Sigma Reactive.E) :=
  #[ ("input_command", ⟨3, .input .command⟩),
     ("input_branch", ⟨56, .input .branch⟩),
     ("input_raw", ⟨2, .input .rawInputs⟩),
     ("reg_plain", ⟨16, .reg .scratch⟩),
     ("reg_packed", ⟨144, row 0⟩),
     ("literal_zero_width", ⟨0, .lit 0⟩),
     ("literal_full", ⟨144, yes⟩),
     ("concat", ⟨16, .concat (a := 8) (b := 8) (.reg .remaining) (.reg .cachedDuration)⟩),
     ("inv", ⟨16, .inv (.reg .scratch)⟩),
     ("band", ⟨16, .band (.reg .scratch) (.lit 42405)⟩),
     ("sub", ⟨64, .sub (.input .word) (.lit 17)⟩),
     ("slice", ⟨8, .slice 9 8 (by decide) shared⟩),
     ("equal", ⟨1, .equal shared (row 1)⟩),
     ("ult", ⟨1, .ult (.input .address) (.lit 16)⟩),
     ("zero", ⟨1, .zero (.reg .remaining)⟩),
     ("mux_packed_packed", ⟨144, shared⟩),
     ("mux_plain_plain", ⟨144, .mux sampled yes no⟩),
     ("mux_packed_plain", ⟨144, .mux sampled shared yes⟩),
     ("mux_plain_packed", ⟨144, .mux sampled yes shared⟩),
     ("shared_equal", ⟨1, .equal shared shared⟩),
     ("shared_slices", ⟨16, .concat (.slice 9 8 (by decide) shared)
         (.slice 47 8 (by decide) shared)⟩),
     ("shared_concat", ⟨288, .concat shared shared⟩),
     ("shared_mixed", ⟨144, .mux pin (.mux sampled shared yes)
         (.mux sampled no shared)⟩),
     ("shared_deeper", ⟨144, .mux pin (.mux sampled shared (row 1))
         (.mux sampled (row 2) shared)⟩) ] ++
    Array.ofFn (fun k : Fin 16 => (s!"dictionary_{k.val}", ⟨144, row k.val⟩))

private def state (seed : Nat) : Values Register := fun {w} r => match r with
  | .row k =>
      let ref := (k.toNat + seed) % 16
      let control := (k.toNat * 1193 + seed * 821 + 45) % 2^24
      let word := k.toNat * 7340033 + seed * 104729 + 2863311530
      BitVec.ofNat 92 (word + control * 2^64 + ref * 2^88)
  | .branch k =>
      let reserved := (k.toNat + seed) % 4
      BitVec.ofNat 56 (k.toNat * 17179869191 + seed * 65539 + 77 + reserved * 2^54)
  | .branchWritten => if seed % 2 = 0 then 65535 else 65534
  | .core .stage1 => BitVec.ofNat 2 (seed / 2)
  | .core .stage2 => BitVec.ofNat 2 seed
  | .core .remaining => BitVec.ofNat 8 (seed % 3)
  | .core .scratch => BitVec.ofNat 16 (seed * 8513 + 4660)
  | .core _ => BitVec.ofNat w (seed * 17 + 3)

private def commands : Array (Nat × Nat × Nat) :=
  #[(0, 0, 0), (1, 0, 0), (1, 15, 15), (1, 63, 16),
    (2, 0, 0), (6, 0, 0), (6, 15, 2^55 + 15),
    (6, 16, 2^54), (3, 0, 0), (7, 0, 0)]

private def input (seed raw : Nat) (command : Nat × Nat × Nat) : Values Input :=
  fun {w} p => BitVec.ofNat w (match p with
    | .command => command.1
    | .address => command.2.1
    | .branch => command.2.2
    | .rawInputs => raw
    | .word => 65537 * seed + 4294967311
    | .control => seed * 8513 + 164
    | .count => 16
    | .expectedGeneration => seed
    | .initialize => seed % 2
    | .virtualSpan => 64
    | .txData => seed * 65539
    | .txLength => seed % 33
    | .rxCapacity => 32
    | .idleLevels => seed
    | .idleEnabled => seed / 2
    | .expectedTransfer => seed * 3
    | .readIndex => seed)

inductive Probe : Nat → Type where
  | result : Nat → Probe w

private def transform (native : Bool) (e : Reactive.E w) : E w :=
  if native then adapt e else (rewrite e).expression

private def outputs : Array (Sigma Probe) :=
  fixtures.mapIdx (fun k (_, ⟨w,_⟩) => ⟨w, .result k⟩) |>.filter (fun ⟨w,_⟩ => w > 0)

private def output (native : Bool) : {w : Nat} → Probe w → E w := fun {w} p =>
  match p with
  | .result k =>
    if let some (_, ⟨v,e⟩) := fixtures[k]? then
      if h : v = w then h ▸ transform native e else .lit 0
    else .lit 0

private def circuit (native : Bool) : Circuit Input Register Probe where
  next := fun r => .reg r
  output := output native

private def probeLabel : {w : Nat} → Probe w → String := fun p => match p with
  | .result k => s!"probe{k}"

private def checkEmission : IO Nat := do
  let safe ← match Emit.moduleText "memo_probe" (circuit false)
      SharedBranches.inputs SharedBranches.registers outputs
      inputLabel registerLabel probeLabel with
    | .ok text => pure text
    | .error e => throw (IO.userError e)
  let mut comparisons := 0
  for native in [false, true] do
    let viaSafe ← match Emit.moduleText "memo_probe" (circuit native)
        SharedBranches.inputs SharedBranches.registers outputs
        inputLabel registerLabel probeLabel with
      | .ok text => pure text
      | .error e => throw (IO.userError e)
    let viaMemo ← match MemoEmit.moduleText "memo_probe" (circuit native)
        SharedBranches.inputs SharedBranches.registers outputs
        inputLabel registerLabel probeLabel with
      | .ok text => pure text
      | .error e => throw (IO.userError e)
    unless safe == viaSafe && safe == viaMemo do
      throw (IO.userError "Safe rewrite/native rewrite or safe emitter/memo emitter byte mismatch")
    comparisons := comparisons + 2
  return comparisons

end Pinwheel.Hardware.Buffered.SharedBranches.MemoChecks

open Pinwheel.Hardware Pinwheel.Hardware.Buffered.SharedBranches
open Pinwheel.Hardware.Buffered.SharedBranches.MemoChecks

-- Public main is the only execution entry; compilation does not run these checks.
unsafe def main : IO Unit := do
  let mut checks := 0
  for (name, ⟨_,e⟩) in fixtures do
    let actual := adapt e
    let direct := MemoAdapt.adaptMemo e
    let reference := e.bind inputExpr registerExpr
    for seed in List.range 8 do
      for command in commands do
        for raw in List.range 4 do
          let i : Values Input := input seed raw command
          let s : Values Register := state seed
          unless actual.eval i s == reference.eval i s do
            throw (IO.userError s!"Expr.bind mismatch: {name}; seed={seed}; cmd={command}; raw={raw}")
          unless direct.eval i s == reference.eval i s do
            throw (IO.userError s!"Direct native rewrite mismatch: {name}; seed={seed}; cmd={command}; raw={raw}")
          checks := checks + 2
  let emitted ← checkEmission
  IO.println s!"Memo rewrite finite checks: {fixtures.size} fixtures; {checks} Expr.bind evaluations; {emitted} byte-identical emitter comparisons."
  IO.println "Covers every Expr constructor, four mux forms, shared graphs, zero/distinct widths, all16 dictionary refs, reserved bits, command1/2/6 mappings and sampled inputs. No universal native/compiler/emitter claim."
