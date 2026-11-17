import Pinwheel.Hardware.Circuit

/-! Derived combinational word operations. These are ordinary `Expr` trees:
there are no new primitives or backend obligations. Every width, including zero,
is supported. Shift amounts are unsigned and are not implicitly masked; logical
overshifts produce zero and arithmetic overshifts replicate the sign bit.
-/
namespace Pinwheel.Hardware.WordOps

def add (x y : Expr I R w) : Expr I R w := .sub x (.sub (.lit 0) y)

def wordOr (x y : Expr I R w) : Expr I R w := .inv (.band (.inv x) (.inv y))

def wordXor (x y : Expr I R w) : Expr I R w :=
  .band (wordOr x y) (.inv (.band x y))

/-- Width transport changes no wires or values. -/
def cast (h : a = b) (x : Expr I R a) : Expr I R b := h ▸ x

def signBit (x : Expr I R w) : Expr I R 1 :=
  if h : 0 < w then .slice (w-1) 1 (by omega) x else .lit 0

def signedLess (x y : Expr I R w) : Expr I R 1 :=
  wordXor (wordXor (signBit x) (signBit y)) (.ult x y)

def shiftLeft (amount : Nat) (x : Expr I R w) : Expr I R w :=
  if amount = 0 then x else if h : amount < w then
    cast (by omega) (.concat (.slice 0 (w-amount) (by omega) x) (.lit (0#amount)))
  else .lit 0

def shiftRight (amount : Nat) (x : Expr I R w) : Expr I R w :=
  if amount = 0 then x else if h : amount < w then
    cast (by omega) (.concat (.lit (0#amount)) (.slice amount (w-amount) (by omega) x))
  else .lit 0

def arithmeticRight (amount : Nat) (x : Expr I R w) : Expr I R w :=
  .mux (signBit x) (.inv (shiftRight amount (.inv x))) (shiftRight amount x)

/-- A barrel network with one stage per amount bit. `stride` is the weight of
the low bit. Each stage is a fixed shift and a mux, never a decoded lookup table. -/
def barrel (fixed : Nat → Expr I R w → Expr I R w) (stride : Nat)
    (x : Expr I R w) : {n : Nat} → Expr I R n → Expr I R w
  | 0, _ => x
  | n+1, amount =>
    barrel fixed (2*stride)
      (.mux (.slice 0 1 (by omega) amount) (fixed stride x) x)
      (.slice 1 n (by omega) amount)

def shiftLeftBy (x : Expr I R w) (amount : Expr I R n) : Expr I R w :=
  barrel shiftLeft 1 x amount

def shiftRightBy (x : Expr I R w) (amount : Expr I R n) : Expr I R w :=
  barrel shiftRight 1 x amount

def arithmeticRightBy (x : Expr I R w) (amount : Expr I R n) : Expr I R w :=
  barrel arithmeticRight 1 x amount

@[simp] theorem add_eval (x y : Expr I R w) (i : Values I) (s : Values R) :
    (add x y).eval i s = x.eval i s + y.eval i s := by
  simp [add, Expr.eval]

@[simp] theorem wordOr_eval (x y : Expr I R w) (i : Values I) (s : Values R) :
    (wordOr x y).eval i s = x.eval i s ||| y.eval i s := by
  simp [wordOr, Expr.eval, BitVec.not_and]

@[simp] theorem wordXor_eval (x y : Expr I R w) (i : Values I) (s : Values R) :
    (wordXor x y).eval i s = x.eval i s ^^^ y.eval i s := by
  ext k hk
  simp only [wordXor, wordOr, Expr.eval, BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getElem_xor]
  cases (x.eval i s)[k] <;> cases (y.eval i s)[k] <;> rfl

@[simp] theorem cast_eval (h : a = b) (x : Expr I R a) (i : Values I) (s : Values R) :
    (cast h x).eval i s = (x.eval i s).cast h := by cases h; rfl

@[simp] theorem signBit_eval (x : Expr I R w) (i : Values I) (s : Values R) :
    (signBit x).eval i s = BitVec.ofBool (x.eval i s).msb := by
  by_cases h : 0 < w
  · ext k hk
    have hz : k = 0 := by omega
    subst k
    simp [signBit, h, Expr.eval, BitVec.msb_eq_getLsbD_last]
  · have hw : w = 0 := by omega
    subst w
    simp [signBit, Expr.eval, BitVec.msb_eq_getLsbD_last]

@[simp] theorem signedLess_eval (x y : Expr I R w) (i : Values I) (s : Values R) :
    (signedLess x y).eval i s = BitVec.ofBool ((x.eval i s).slt (y.eval i s)) := by
  simp [signedLess, Expr.eval, BitVec.slt_eq_ult, BitVec.ult]

@[simp] theorem shiftLeft_eval (amount : Nat) (x : Expr I R w) (i : Values I) (s : Values R) :
    (shiftLeft amount x).eval i s = x.eval i s <<< amount := by
  by_cases hz : amount = 0
  · simp [shiftLeft, hz]
  by_cases h : amount < w
  · simp only [shiftLeft, hz, ↓reduceIte, h, ↓reduceDIte, cast_eval, Expr.eval]
    exact (BitVec.shiftLeft_eq_concat_of_lt h).symm
  · simp [shiftLeft, hz, h, Expr.eval, BitVec.shiftLeft_eq_zero (by omega : w ≤ amount)]

@[simp] theorem shiftRight_eval (amount : Nat) (x : Expr I R w) (i : Values I) (s : Values R) :
    (shiftRight amount x).eval i s = x.eval i s >>> amount := by
  by_cases hz : amount = 0
  · simp [shiftRight, hz]
  by_cases h : amount < w
  · simp only [shiftRight, hz, ↓reduceIte, h, ↓reduceDIte, cast_eval, Expr.eval]
    exact (BitVec.ushiftRight_eq_extractLsb'_of_lt h).symm
  · simp [shiftRight, hz, h, Expr.eval, BitVec.ushiftRight_eq_zero (by omega : w ≤ amount)]

@[simp] theorem arithmeticRight_eval (amount : Nat) (x : Expr I R w) (i : Values I) (s : Values R) :
    (arithmeticRight amount x).eval i s = (x.eval i s).sshiftRight amount := by
  simp only [arithmeticRight, Expr.eval, signBit_eval, shiftRight_eval]
  cases h : (x.eval i s).msb <;>
    simp [h, BitVec.sshiftRight_eq_of_msb_false, BitVec.sshiftRight_eq_of_msb_true]

/-- Splitting an unsigned amount into its low selector and remaining bits does
not lose high bits, even when those bits encode an overshift. -/
theorem amount_split (x : BitVec (n+1)) :
    x.toNat = 2 * (x.extractLsb' 1 n).toNat +
      (if x.extractLsb' 0 1 = 1 then 1 else 0) := by
  have hx := x.isLt
  have hl : (x.extractLsb' 0 1 = 1) ↔ x.toNat % 2 = 1 := by
    simp [← BitVec.toNat_inj, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_one, hl]
  have ht : x.toNat / 2 < 2 ^ n := by rw [Nat.pow_succ] at hx; omega
  rw [Nat.mod_eq_of_lt ht]
  split <;> omega

/-- The shared barrel proof applies to any additive family of fixed operations. -/
theorem barrel_eval (fixed : Nat → Expr I R w → Expr I R w)
    (operation : Nat → BitVec w → BitVec w)
    (hfixed : ∀ k x, (fixed k x).eval i s = operation k (x.eval i s))
    (hzero : ∀ v, operation 0 v = v)
    (hadd : ∀ a b v, operation b (operation a v) = operation (a+b) v)
    (stride : Nat) (x : Expr I R w) (amount : Expr I R n) :
    (barrel fixed stride x amount).eval i s =
      operation (stride * (amount.eval i s).toNat) (x.eval i s) := by
  induction n generalizing stride x with
  | zero =>
    have hz : (amount.eval i s).toNat = 0 := by have := (amount.eval i s).isLt; simp_all
    simp [barrel, hz, hzero]
  | succ n ih =>
    rw [barrel, ih]
    simp only [Expr.eval, hfixed]
    have hn := congrArg (stride * ·) (amount_split (amount.eval i s))
    by_cases hb : (amount.eval i s).extractLsb' 0 1 = 1
    · simp only [hb, ↓reduceIte, Nat.mul_add, Nat.mul_one] at hn ⊢
      rw [hadd]
      congr 1
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.add_comm] using hn.symm
    · simp only [hb, ↓reduceIte, Nat.add_zero] at hn ⊢
      congr 1
      simpa [Nat.mul_assoc, Nat.mul_left_comm] using hn.symm

@[simp] theorem shiftLeftBy_eval (x : Expr I R w) (amount : Expr I R n)
    (i : Values I) (s : Values R) :
    (shiftLeftBy x amount).eval i s = x.eval i s <<< (amount.eval i s).toNat := by
  simpa [shiftLeftBy] using barrel_eval shiftLeft (fun k v => v <<< k)
    (fun k v => shiftLeft_eval k v i s) BitVec.shiftLeft_zero
    (fun a b v => (BitVec.shiftLeft_add v a b).symm) 1 x amount

@[simp] theorem shiftRightBy_eval (x : Expr I R w) (amount : Expr I R n)
    (i : Values I) (s : Values R) :
    (shiftRightBy x amount).eval i s = x.eval i s >>> (amount.eval i s).toNat := by
  simpa [shiftRightBy] using barrel_eval shiftRight (fun k v => v >>> k)
    (fun k v => shiftRight_eval k v i s) BitVec.ushiftRight_zero
    (fun a b v => (BitVec.shiftRight_add v a b).symm) 1 x amount

@[simp] theorem arithmeticRightBy_eval (x : Expr I R w) (amount : Expr I R n)
    (i : Values I) (s : Values R) :
    (arithmeticRightBy x amount).eval i s = (x.eval i s).sshiftRight (amount.eval i s).toNat := by
  simpa [arithmeticRightBy] using barrel_eval arithmeticRight (fun k v => v.sshiftRight k)
    (fun k v => arithmeticRight_eval k v i s) (fun _ => BitVec.sshiftRight_zero)
    (fun _ _ _ => BitVec.sshiftRight_add.symm) 1 x amount

/-- Signed comparison follows two's-complement integer order. -/
theorem signedLess_toInt (x y : Expr I R w) (i : Values I) (s : Values R) :
    (signedLess x y).eval i s = BitVec.ofBool (decide ((x.eval i s).toInt < (y.eval i s).toInt)) :=
  signedLess_eval x y i s

/-- Substitution can be applied before or after building a variable shifter.
The same `Expr.eval_bind` rewrite works with every evaluation theorem above. -/
theorem shiftLeftBy_bind_eval (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (x : Expr I R w) (amount : Expr I R n)
    (i : Values J) (s : Values S) :
    ((shiftLeftBy x amount).bind input register).eval i s =
      (shiftLeftBy (x.bind input register) (amount.bind input register)).eval i s := by
  simp only [Expr.eval_bind, shiftLeftBy_eval]

theorem shiftRightBy_bind_eval (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (x : Expr I R w) (amount : Expr I R n)
    (i : Values J) (s : Values S) :
    ((shiftRightBy x amount).bind input register).eval i s =
      (shiftRightBy (x.bind input register) (amount.bind input register)).eval i s := by
  simp only [Expr.eval_bind, shiftRightBy_eval]

theorem arithmeticRightBy_bind_eval (input : {b : Nat} → I b → Expr J S b)
    (register : {b : Nat} → R b → Expr J S b) (x : Expr I R w) (amount : Expr I R n)
    (i : Values J) (s : Values S) :
    ((arithmeticRightBy x amount).bind input register).eval i s =
      (arithmeticRightBy (x.bind input register) (amount.bind input register)).eval i s := by
  simp only [Expr.eval_bind, arithmeticRightBy_eval]

end Pinwheel.Hardware.WordOps
