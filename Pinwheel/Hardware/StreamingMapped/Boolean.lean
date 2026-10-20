import Init.Data.BitVec.Bitblast

/-! Pure Boolean functions reconstructed from mapped cells. Generated artifact
proofs instantiate these expressions from actual connected gate inventories. -/
namespace Pinwheel.Hardware.StreamingMapped

inductive Expr (inputs : Nat) where
  | constant : Bool → Expr inputs
  | var : Fin inputs → Expr inputs
  | inv : Expr inputs → Expr inputs
  | conj : Expr inputs → Expr inputs → Expr inputs
  | disj : Expr inputs → Expr inputs → Expr inputs
  | xor : Expr inputs → Expr inputs → Expr inputs
  deriving Repr,DecidableEq

def Expr.eval (values : Fin inputs → Bool) : Expr inputs → Bool
  | .constant value => value
  | .var input => values input
  | .inv input => !(input.eval values)
  | .conj left right => left.eval values && right.eval values
  | .disj left right => left.eval values || right.eval values
  | .xor left right => left.eval values ^^ right.eval values

/-- Three inputs in the order A, B, carry-in. -/
def Expr.triple (expression : Expr 3) (a b carry : Bool) : Bool :=
  expression.eval (fun input => if input.val = 0 then a else if input.val = 1 then b else carry)

structure FullAdderLeaf where
  sum : Bool → Bool → Bool → Bool
  carry : Bool → Bool → Bool → Bool

/-- The mapped leaf must establish both functions for all eight valuations. -/
structure FullAdderLeaf.Correct (leaf : FullAdderLeaf) : Prop where
  sum : ∀ a b carry, leaf.sum a b carry = (a ^^ (b ^^ carry))
  carry : ∀ a b carry, leaf.carry a b carry = Bool.atLeastTwo a b carry

def FullAdderLeaf.fromExpressions (sum carry : Expr 3) : FullAdderLeaf :=
  ⟨sum.triple,carry.triple⟩

/-- A canonical independent witness; generated cells prove this same contract
from their actual Liberty functions and connectivity. -/
def FullAdderLeaf.canonical : FullAdderLeaf :=
  ⟨fun a b carry => a ^^ (b ^^ carry),Bool.atLeastTwo⟩

theorem FullAdderLeaf.canonical_correct : FullAdderLeaf.canonical.Correct := ⟨by intros; rfl,by intros; rfl⟩

end Pinwheel.Hardware.StreamingMapped
