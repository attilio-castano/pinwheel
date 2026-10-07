import Pinwheel.Hardware.Buffered.MemoEval

/-! Independent finite qualification of the batch evaluation cache.
The reference always maps unchanged ordinary `Expr.eval` directly. The public
API and explicit unsafe implementation are both compared against it. -/
namespace Pinwheel.Hardware.Buffered.SramMemoEvalChecks
open Pinwheel.Hardware

inductive Pin : Nat → Type where
  | value : Nat → Pin w

inductive Register : Nat → Type where
  | value : Nat → Register w

abbrev E := Expr Pin Register

private def expressions (w : Nat) : Array (Sigma E) :=
  let x : E w := .input (.value 0)
  let y : E w := .reg (.value 1)
  let shared : E w := .sub (.band (.inv x) y) (.lit 1)
  let duplicated : E w := .band shared shared
  let condition : E 1 := .ult x y
  let joined : E (w+w) := .concat shared shared
  #[⟨w,x⟩, ⟨w,y⟩, ⟨w,.lit 0⟩, ⟨w,.lit (BitVec.ofNat w (2^w-1))⟩,
    ⟨w,.inv x⟩, ⟨w,.band x y⟩, ⟨w,.sub x y⟩, ⟨w,shared⟩,
    ⟨w,duplicated⟩, ⟨w,shared⟩, ⟨w,duplicated⟩,
    ⟨w+w,joined⟩, ⟨w,.slice w w (by omega) joined⟩,
    ⟨0,.slice (w+w) 0 (by omega) joined⟩,
    ⟨1,.equal x y⟩, ⟨1,.equal shared shared⟩,
    ⟨1,condition⟩, ⟨1,.zero shared⟩,
    ⟨w,.mux condition shared duplicated⟩,
    ⟨w,.mux (.lit 0) x y⟩, ⟨w,.mux (.lit 1) x y⟩,
    ⟨w,.mux (.zero x) (.mux condition shared x) (.mux condition y shared)⟩,
    ⟨0+w,.concat (a := 0) (b := w) (.lit 0) shared⟩,
    ⟨w,.concat (a := w) (b := 0) shared (.lit 0)⟩]

private def value (w k seed : Nat) : BitVec w := BitVec.ofNat w (
  if seed % 8 == 0 then 0
  else if seed % 8 == 1 then 2^w-1
  else if seed % 8 == 2 then 1
  else if seed % 8 == 3 then 2^(w-1)
  else if seed % 8 == 4 then (2^w-1)/3
  else if seed % 8 == 5 then 2 * ((2^w-1)/3)
  else if seed % 8 == 6 then 2^w + 1
  else seed * 104729 + k * 7340033 + 2863311530 + 2^(w-1))

private def inputs (seed : Nat) : Values Pin := fun {w} p =>
  match p with | .value k => value w k seed

private def state (seed : Nat) : Values Register := fun {w} r =>
  match r with | .value k => value w (k+7) seed

private def ordinary (i : Values Pin) (s : Values Register)
    (es : Array (Sigma E)) : Array Nat :=
  es.map fun ⟨_,e⟩ => (e.eval i s).toNat

private unsafe def compare (label : String) (i : Values Pin) (s : Values Register)
    (es : Array (Sigma E)) : IO Nat := do
  let expected := ordinary i s es
  unless MemoEval.evalMany i s es == expected do
    throw (IO.userError s!"Public batch evaluation mismatch: {label}")
  unless MemoEval.evalManyMemo i s es == expected do
    throw (IO.userError s!"Direct native batch evaluation mismatch: {label}")
  return 2 * es.size

end Pinwheel.Hardware.Buffered.SramMemoEvalChecks

open Pinwheel.Hardware Pinwheel.Hardware.Buffered.SramMemoEvalChecks

unsafe def main : IO Unit := do
  let roots := (List.range 289).toArray.flatMap expressions
  let mut checks := 0
  checks := checks + (← compare "empty" (inputs 0) (state 0) #[])
  for seed in List.range 8 do
    checks := checks + (← compare s!"all widths input{seed} register{7-seed}"
      (inputs seed) (state (7-seed)) roots)
  -- Reuse the identical source objects while changing inputs and registers
  -- independently; return to an earlier valuation to catch cross-batch state.
  for (a,b) in [(0,0),(7,0),(7,7),(0,7),(0,0)] do
    checks := checks + (← compare s!"cache isolation input{a} register{b}"
      (inputs a) (state b) roots)
  checks := checks + (← compare "root order reversed" (inputs 3) (state 5) roots.reverse)
  -- Fresh batches vary width and source allocation, including widths zero
  -- and one, while the preceding batches have released their local caches.
  for seed in List.range 64 do
    let fresh := expressions ((seed*37) % 289)
    checks := checks + (← compare s!"fresh batch{seed}" (inputs seed) (state (seed+3)) fresh)
  IO.println s!"Memo evaluation finite checks: {roots.size} roots; {checks} ordinary Expr.eval comparisons; widths0–288, all constructors, shared DAGs, multiple roots, boundary values, independent input/register changes and batch isolation passed."
  IO.println "Logical laws use ordinary Expr.eval and standard kernel axioms. Finite execution checks do not prove universal native or compiler correctness."
