import Pinwheel.Binary.Basic

namespace Pinwheel.Binary

def putList (put : α → List Byte) (xs : List α) : List Byte := xs.flatMap put

def getList (get : Reader α) : Nat → Reader (List α)
  | 0 => pure []
  | n + 1 => do return (← get) :: (← getList get n)

attribute [local simp] List.append_assoc Bind.bind Pure.pure Functor.map
  StateT.bind StateT.pure StateT.map

theorem list_law (put : α → List Byte) (get : Reader α) (h : Law put get)
    (xs : List α) (rest : List Byte) :
    getList get xs.length (putList put xs ++ rest) = some (xs, rest) := by
  induction xs generalizing rest
  all_goals simp_all [putList, getList, show ∀ a r, get (put a ++ r) = some (a, r) from h]
  done

def putVector (put : α → List Byte) (v : Vector α n) : List Byte := putList put v.toList

def getVector (get : Reader α) (n : Nat) : Reader (Vector α n) := do
  let xs ← getList get n
  if h : xs.length = n then return ⟨xs.toArray, by simpa using h⟩ else fun _ => none

theorem vector_law (put : α → List Byte) (get : Reader α) (h : Law put get)
    (v : Vector α n) (rest : List Byte) :
    getVector get n (putVector put v ++ rest) = some (v, rest) := by
  simp [putVector, getVector, Vector.toArray_toList, show getList get n (putList put v.toList ++ rest) = some (v.toList, rest)
    from (by simpa using list_law put get h v.toList rest)]
  done

end Pinwheel.Binary
