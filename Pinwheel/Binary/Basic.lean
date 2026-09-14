import Std

/-! Byte-aligned version-zero codecs. Every parser preserves the unconsumed suffix. -/
namespace Pinwheel.Binary

abbrev Byte := Fin 256
abbrev Reader (α : Type) := StateT (List Byte) Option α

def putFin {n : Nat} (h : n ≤ 256) (a : Fin n) : List Byte := [⟨a.val, by omega⟩]

def getFin (n : Nat) : Reader (Fin n) := fun bytes =>
  match bytes with
  | [] => none
  | b :: rest => if h : b.val < n then some (⟨b.val, h⟩, rest) else none

def putBool (b : Bool) : List Byte := [if b then 1 else 0]

def getBool : Reader Bool := do
  let b ← getFin 2
  return b.val == 1

def putBits {n : Nat} (h : 2 ^ n ≤ 256) (a : BitVec n) : List Byte := putFin h a.toFin

def getBits (n : Nat) : Reader (BitVec n) := do
  let value ← getFin (2 ^ n)
  return BitVec.ofFin value

/-- The prefix law is stronger than a standalone round trip: concatenated records remain parseable. -/
def Law (put : α → List Byte) (get : Reader α) : Prop :=
  ∀ value rest, get (put value ++ rest) = some (value, rest)

theorem fin_law (n : Nat) (h : n ≤ 256) (value : Fin n) (rest : List Byte) :
    getFin n (putFin h value ++ rest) = some (value, rest) := by
  simp [getFin, putFin, value.isLt]
  done

theorem bool_law (value : Bool) (rest : List Byte) :
    getBool (putBool value ++ rest) = some (value, rest) := by
  cases value <;> simp [putBool, getBool, Functor.map, StateT.map, getFin]
  done

theorem bits_law (n : Nat) (h : 2 ^ n ≤ 256) (value : BitVec n) (rest : List Byte) :
    getBits n (putBits h value ++ rest) = some (value, rest) := by
  simp [putBits, getBits, Functor.map, StateT.map, fin_law]
  done

def putOption (put : α → List Byte) : Option α → List Byte
  | none => putBool false
  | some a => putBool true ++ put a

def getOption (get : Reader α) : Reader (Option α) := do
  if ← getBool then return some (← get) else return none

theorem option_law (put : α → List Byte) (get : Reader α) (h : Law put get)
    (value : Option α) (rest : List Byte) :
    getOption get (putOption put value ++ rest) = some (value, rest) := by
  cases value <;> simp [putOption, getOption, List.append_assoc, Bind.bind, Pure.pure,
    StateT.bind, StateT.pure, bool_law, show ∀ a r, get (put a ++ r) = some (a, r) from h]
  done

end Pinwheel.Binary
