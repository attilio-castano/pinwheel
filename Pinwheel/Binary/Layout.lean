import Pinwheel.Binary.RecordProofs

namespace Pinwheel.Binary
open Engine.Reactive.Counted

/-- Preorder layout records: emit=0, sequence=1, repeat=2. No implicit or discarded nodes. -/
def putCode : Code → List Byte
  | .emit t => putFin (by decide) (0 : Fin 3) ++ putTemplate t
  | .seq a b => putFin (by decide) (1 : Fin 3) ++ putCode a ++ putCode b
  | .repeat n body => putFin (by decide) (2 : Fin 3) ++ putFin (by decide) n ++ putCode body

/-- Parser recursion is bounded independently of untrusted input. Whole-image validation also
checks total node count, nesting, and execution span before constructing a loaded program. -/
def getCode : Nat → Reader Code
  | 0 => fun _ => none
  | fuel + 1 => do
    let tag ← getFin 3
    match tag.val with
    | 0 => return .emit (← getTemplate)
    | 1 => return .seq (← getCode fuel) (← getCode fuel)
    | _ => return .repeat (← getFin 8) (← getCode fuel)

attribute [local simp] List.append_assoc Bind.bind Pure.pure Functor.map
  StateT.bind StateT.pure StateT.map fin_law template_law

theorem code_law (c : Code) (fuel : Nat) (h : c.nodes ≤ fuel) (rest : List Byte) :
    getCode fuel (putCode c ++ rest) = some (c, rest) := by
  induction c generalizing fuel rest
  all_goals cases fuel <;> simp_all [Code.nodes, putCode, getCode]
  all_goals simp (disch := omega) [*]
  done

end Pinwheel.Binary
