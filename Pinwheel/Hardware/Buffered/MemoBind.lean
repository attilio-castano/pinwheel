import Pinwheel.Hardware.Circuit

/-! Expression substitution with target-local native DAG preservation.
The kernel definition is ordinary `Expr.bind`. Native evaluation caches source
objects only within one invocation, retains them, and checks result widths.
Finite independent bind and emitter comparisons qualify this execution path;
this is not a universal native compiler-correctness theorem. -/
namespace Pinwheel.Hardware.Buffered.MemoBind
open Pinwheel.Hardware

structure Cache (I R J S : Nat → Type) where
  entries : Std.HashMap (Nat × USize) (Sigma (Expr J S)) := {}
  retained : Array (Sigma (Expr I R)) := #[]

private def checked (w : Nat) : Sigma (Expr J S) → Option (Expr J S w)
  | ⟨v, e⟩ => if h : v = w then some (h ▸ e) else none

private unsafe def visit (input : {w : Nat} → I w → Expr J S w)
    (register : {w : Nat} → R w → Expr J S w) (e : Expr I R w) :
    StateM (Cache I R J S) (Expr J S w) := do
  let key := (w, ptrAddrUnsafe e)
  if let some value := ((← get).entries[key]?).bind (checked w) then return value
  modify fun s => {s with retained := s.retained.push ⟨w,e⟩}
  let value ← (match (motive := (w : Nat) → Expr I R w →
      StateM (Cache I R J S) (Expr J S w)) w, e with
    | _, .input p => pure (input p)
    | _, .reg r => pure (register r)
    | _, .lit v => pure (.lit v)
    | _, .concat x y => do return .concat (← visit input register x) (← visit input register y)
    | _, .inv x => do return .inv (← visit input register x)
    | _, .band x y => do return .band (← visit input register x) (← visit input register y)
    | _, .sub x y => do return .sub (← visit input register x) (← visit input register y)
    | _, .slice start len h x => do return .slice start len h (← visit input register x)
    | _, .equal x y => do return .equal (← visit input register x) (← visit input register y)
    | _, .ult x y => do return .ult (← visit input register x) (← visit input register y)
    | _, .zero x => do return .zero (← visit input register x)
    | _, .mux c t f => do
      return .mux (← visit input register c) (← visit input register t) (← visit input register f))
  modify fun s => {s with entries := s.entries.insert key ⟨w,value⟩}
  return value

unsafe def bindMemo (input : {w : Nat} → I w → Expr J S w)
    (register : {w : Nat} → R w → Expr J S w) (e : Expr I R w) : Expr J S w :=
  (visit input register e).run' {}

@[implemented_by bindMemo]
def bind (input : {w : Nat} → I w → Expr J S w)
    (register : {w : Nat} → R w → Expr J S w) (e : Expr I R w) : Expr J S w :=
  e.bind input register

theorem eval_bind (input : {w : Nat} → I w → Expr J S w)
    (register : {w : Nat} → R w → Expr J S w) (e : Expr I R w)
    (i : Values J) (s : Values S) :
    (bind input register e).eval i s =
      e.eval (fun p => (input p).eval i s) (fun r => (register r).eval i s) :=
  Expr.eval_bind input register e i s

end Pinwheel.Hardware.Buffered.MemoBind
