import Pinwheel.Hardware.Circuit

/-! Batch expression evaluation with a native cache local to one batch.
The logical definition maps ordinary `Expr.eval`. Native evaluation retains
source objects and checks cached widths; inputs and registers remain fixed
throughout that batch. Finite independent comparisons qualify this execution
path, rather than proving universal native compiler correctness. -/
namespace Pinwheel.Hardware.Buffered.MemoEval
open Pinwheel.Hardware

structure Cache (I R : Nat → Type) where
  entries : Std.HashMap (Nat × USize) (Sigma BitVec) := {}
  retained : Array (Sigma (Expr I R)) := #[]

private def checked (w : Nat) : Sigma BitVec → Option (BitVec w)
  | ⟨v, x⟩ => if h : v = w then some (h ▸ x) else none

private unsafe def visit (i : Values I) (r : Values R) (e : Expr I R w) :
    StateM (Cache I R) (BitVec w) := do
  let key := (w, ptrAddrUnsafe e)
  if let some value := ((← get).entries[key]?).bind (checked w) then return value
  modify fun s => {s with retained := s.retained.push ⟨w,e⟩}
  let value ← (match (motive := (w : Nat) → Expr I R w →
      StateM (Cache I R) (BitVec w)) w, e with
    | _, .input p => pure (i p)
    | _, .reg p => pure (r p)
    | _, .lit x => pure x
    | _, .concat x y => do return (← visit i r x) ++ (← visit i r y)
    | _, .inv x => do return ~~~(← visit i r x)
    | _, .band x y => do return (← visit i r x) &&& (← visit i r y)
    | _, .sub x y => do return (← visit i r x) - (← visit i r y)
    | _, .slice start len _ x => do return (← visit i r x).extractLsb' start len
    | _, .equal x y => do return BitVec.ofBool (decide ((← visit i r x) = (← visit i r y)))
    | _, .ult x y => do return BitVec.ofBool (decide ((← visit i r x).toNat < (← visit i r y).toNat))
    | _, .zero x => do return BitVec.ofBool (decide ((← visit i r x) = 0))
    | _, .mux c t f => do
      if (← visit i r c) = 1 then visit i r t else visit i r f)
  modify fun s => {s with entries := s.entries.insert key ⟨w,value⟩}
  return value

unsafe def evalManyMemo (i : Values I) (r : Values R)
    (es : Array (Sigma (Expr I R))) : Array Nat :=
  ((es.mapM fun ⟨_,e⟩ => do return (← visit i r e).toNat) :
    StateM (Cache I R) (Array Nat)).run' {}

@[implemented_by evalManyMemo]
def evalMany (i : Values I) (r : Values R)
    (es : Array (Sigma (Expr I R))) : Array Nat :=
  es.map fun ⟨_,e⟩ => (e.eval i r).toNat

theorem evalMany_eq (i : Values I) (r : Values R)
    (es : Array (Sigma (Expr I R))) :
    evalMany i r es = es.map (fun ⟨_,e⟩ => (e.eval i r).toNat) := rfl

theorem evalMany_size (i : Values I) (r : Values R)
    (es : Array (Sigma (Expr I R))) : (evalMany i r es).size = es.size := by
  simp [evalMany]

theorem evalMany_get (i : Values I) (r : Values R)
    (es : Array (Sigma (Expr I R))) (k : Nat) :
    (evalMany i r es)[k]? = es[k]?.map (fun ⟨_,e⟩ => (e.eval i r).toNat) := by
  simp [evalMany]

end Pinwheel.Hardware.Buffered.MemoEval
