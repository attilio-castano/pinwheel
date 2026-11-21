import Lean
import Pinwheel.Hardware.WordOps

open Lean Elab Command
open Pinwheel.Hardware Pinwheel.Hardware.WordOps

namespace HardwareWordOpsTests

inductive Input (w n : Nat) : Nat → Type where
  | word : Input w n w
  | amount : Input w n n

inductive Register (w : Nat) : Nat → Type where
  | word : Register w w

def pins (w n x amount : Nat) : Values (Input w n) := fun p => match p with
  | .word => BitVec.ofNat w x
  | .amount => BitVec.ofNat n amount

def state (w y : Nat) : Values (Register w) := fun p => match p with
  | .word => BitVec.ofNat w y

abbrev E (w n b : Nat) := Expr (Input w n) (Register w) b

def left (w n : Nat) : E w n w := .input .word
def right (w n : Nat) : E w n w := .reg .word
def amount (w n : Nat) : E w n n := .input .amount

/-- Independent integer oracle. It uses division/remainder for individual bits,
not BitVec operations, WordOps definitions, or their proved rewrite lemmas. -/
def signed (w x : Nat) : Int :=
  if 0 < w ∧ 2^(w-1) ≤ x then (x : Int) - (2^w : Nat) else x

def normalize (w : Nat) (x : Int) : Nat := (x % (2^w : Nat)).toNat

def bitwise (w x y : Nat) (f : Bool → Bool → Bool) : Nat :=
  (List.range w).foldl (fun total k =>
    if f (x / 2^k % 2 == 1) (y / 2^k % 2 == 1) then total + 2^k else total) 0

def expectedPair (w x y : Nat) : Array Nat :=
  #[(x+y) % 2^w, bitwise w x y (· || ·), bitwise w x y (· != ·),
    if signed w x < signed w y then 1 else 0,
    if 0 < w ∧ 2^(w-1) ≤ x then 1 else 0]

def expectedShifts (w x k : Nat) : Array Nat :=
  #[(x * 2^k) % 2^w, x / 2^k, normalize w (signed w x / (2^k : Nat))]

def requireEqual (actual expected : Array Nat) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError s!"{label}: expected {expected}, got {actual}")

def checkPair (w rawX rawY : Nat) : IO Unit := do
  let x := rawX % 2^w
  let y := rawY % 2^w
  let i : Values (Input w 0) := pins w 0 x 0
  let s : Values (Register w) := state w y
  let l := left w 0
  let r := right w 0
  let actual := #[(add l r).eval i s |>.toNat, (wordOr l r).eval i s |>.toNat,
    (wordXor l r).eval i s |>.toNat, (signedLess l r).eval i s |>.toNat,
    (signBit l).eval i s |>.toNat]
  requireEqual actual (expectedPair w x y) s!"pair w{w} x{x} y{y}"

def checkShifts (w n rawX rawAmount : Nat) : IO Unit := do
  let x := rawX % 2^w
  let k := rawAmount % 2^n
  let i : Values (Input w n) := pins w n x rawAmount
  let s : Values (Register w) := state w 0
  let l := left w n
  let a := amount w n
  let fixed := #[(shiftLeft rawAmount l).eval i s |>.toNat,
    (shiftRight rawAmount l).eval i s |>.toNat,
    (arithmeticRight rawAmount l).eval i s |>.toNat]
  let varying := #[(shiftLeftBy l a).eval i s |>.toNat,
    (shiftRightBy l a).eval i s |>.toNat,
    (arithmeticRightBy l a).eval i s |>.toNat]
  requireEqual fixed (expectedShifts w x rawAmount) s!"fixed w{w} x{x} amount{rawAmount}"
  requireEqual varying (expectedShifts w x k) s!"variable w{w} x{x} n{n} amount{k}"

def boundaries (w : Nat) : List Nat :=
  [0, 1, 2, 3, 2^(w-1)-1, 2^(w-1), 2^(w-1)+1, 2^w-2, 2^w-1,
    0x55555555, 0xaaaaaaaa, 0x80000001, 0xdeadbeef, 0xffffffff]

def campaign : IO (Nat × Nat) := do
  let mut pairs := 0
  let mut shifts := 0
  -- Complete small widths include zero-width words and shift amounts.
  for w in [:5] do
    for x in [:2^w] do
      for y in [:2^w] do
        checkPair w x y
        pairs := pairs+1
      for n in [:5] do
        for k in [:2^n] do
          checkShifts w n x k
          shifts := shifts+1
  for w in [1, 5, 8, 17, 31, 32, 33, 64] do
    for x in boundaries w do
      for y in boundaries w do
        checkPair w x y
        pairs := pairs+1
      for n in [0, 1, 2, 5, 6, 8] do
        for k in [0, 1, 2, w-1, w, w+1, 31, 32, 33, 63, 64, 127, 255] do
          checkShifts w n x k
          shifts := shifts+1
  -- Deterministic arithmetic generator; no relation to expression evaluation.
  let mut seed := 0x13579bdf
  for k in [:1000] do
    seed := (1664525*seed + 1013904223) % 2^32
    let x := seed
    seed := (1664525*seed + 1013904223) % 2^32
    checkPair 32 x seed
    checkShifts 32 5 x (k % 32)
    checkShifts 32 8 x (seed % 256)
    pairs := pairs+1
    shifts := shifts+2
  return (pairs, shifts)

/-- Actual expression faults, rejected by concrete value disagreement with the
independent oracle. Type or parser failures cannot count as a successful probe. -/
def reject (name : String) (actual expected : Nat) : IO Unit := do
  unless actual != expected do throw (IO.userError s!"Mutation escaped: {name}")

def mutations : IO Nat := do
  let l := left 8 4
  let r := right 8 4
  let a := amount 8 4
  let evaluate : {b : Nat} → E 8 4 b → Nat → Nat → Nat → Nat :=
    fun e x y k => (e.eval (pins 8 4 x k) (state 8 y)).toNat
  reject "addition loses carry into top bit"
    (evaluate (.band (add l r) (.lit 127)) 127 1 0) (expectedPair 8 127 1)[0]!
  reject "OR replaced by XOR" (evaluate (wordXor l r) 1 1 0) (expectedPair 8 1 1)[1]!
  reject "XOR replaced by OR" (evaluate (wordOr l r) 1 1 0) (expectedPair 8 1 1)[2]!
  reject "signed less replaced by unsigned" (evaluate (.ult l r) 128 0 0) (expectedPair 8 128 0)[3]!
  reject "arithmetic right loses sign" (evaluate (shiftRightBy l a) 128 0 1) (expectedShifts 8 128 1)[2]!
  reject "left shifts in wrong direction" (evaluate (shiftRightBy l a) 3 0 1) (expectedShifts 8 3 1)[0]!
  reject "arithmetic overshift zeroed" (evaluate (shiftRightBy l a) 255 0 8) (expectedShifts 8 255 8)[2]!
  let truncated : E 32 6 32 := shiftLeftBy (left 32 6) (.slice 0 5 (by decide) (amount 32 6))
  reject "generic amount silently masked to five bits"
    ((truncated.eval (pins 32 6 1 32) (state 32 0)).toNat) (expectedShifts 32 1 32)[0]!
  return 8

/-- Arbitrary input and register rewiring follows the common Expr substitution
theorem; no operation-specific primitive interpretation is assumed. -/
theorem bound_add (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (x y : Expr I R w)
    (i : Values J) (s : Values S) :
    ((add x y).bind input register).eval i s =
      (x.bind input register).eval i s + (y.bind input register).eval i s := by
  simp only [Expr.eval_bind, add_eval]

theorem bound_boolean_signed (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (x y : Expr I R w)
    (i : Values J) (s : Values S) :
    ((wordOr x y).bind input register).eval i s =
      (x.bind input register).eval i s ||| (y.bind input register).eval i s ∧
    ((wordXor x y).bind input register).eval i s =
      (x.bind input register).eval i s ^^^ (y.bind input register).eval i s ∧
    ((signedLess x y).bind input register).eval i s =
      BitVec.ofBool (decide (((x.bind input register).eval i s).toInt <
        ((y.bind input register).eval i s).toInt)) := by
  simp only [Expr.eval_bind, wordOr_eval, wordXor_eval, signedLess_toInt, and_self]

example : (arithmeticRightBy (left 8 4) (amount 8 4)).eval (pins 8 4 128 8) (state 8 0) = 255 := by
  decide +kernel

example : (shiftLeftBy (left 32 6) (amount 32 6)).eval (pins 32 6 1 32) (state 32 0) = 0 := by
  decide +kernel

end HardwareWordOpsTests

elab "#audit_word_ops" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Pinwheel.Hardware.WordOps." ||
        name.toString.startsWith "_private.Pinwheel.Hardware.WordOps." ||
        name.toString.startsWith "HardwareWordOpsTests." then
      count := count+1
      let axioms ← collectAxioms name
      let bad := axioms.filter fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound
      unless bad.isEmpty do throwError "Unapproved word-operation axioms in {name}: {bad}"
  if count < 35 then throwError "Incomplete word-operation audit"
  logInfo m!"Word operations: {count} declarations, standard axioms only."

#audit_word_ops

def main : IO Unit := do
  let (pairs, shifts) ← HardwareWordOpsTests.campaign
  let mutants ← HardwareWordOpsTests.mutations
  IO.println s!"Word operations: {pairs} independent pair cases, {shifts} fixed/variable shift cases, {mutants} actual-expression mutations rejected."
