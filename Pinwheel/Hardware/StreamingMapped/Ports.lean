import Pinwheel.Hardware.StreamingMapped.Boolean

/-! Static pin renaming and substitution preserve interpreted Boolean
functions. Generated port certificates prove the expression shape separately. -/
namespace Pinwheel.Hardware.StreamingMapped

def Expr.map (rename : Fin inputs → Fin outputs) : Expr inputs → Expr outputs
  | .constant value => .constant value
  | .var input => .var (rename input)
  | .inv expression => .inv (expression.map rename)
  | .conj left right => .conj (left.map rename) (right.map rename)
  | .disj left right => .disj (left.map rename) (right.map rename)
  | .xor left right => .xor (left.map rename) (right.map rename)

theorem Expr.eval_map (values : Fin outputs → Bool) (rename : Fin inputs → Fin outputs)
    (expression : Expr inputs) :
    (expression.map rename).eval values = expression.eval (values ∘ rename) := by
  induction expression <;> simp_all [map,eval,Function.comp_def]

def Expr.bind (replacement : Fin inputs → Expr outputs) : Expr inputs → Expr outputs
  | .constant value => .constant value
  | .var input => replacement input
  | .inv expression => .inv (expression.bind replacement)
  | .conj left right => .conj (left.bind replacement) (right.bind replacement)
  | .disj left right => .disj (left.bind replacement) (right.bind replacement)
  | .xor left right => .xor (left.bind replacement) (right.bind replacement)

theorem Expr.eval_bind (values : Fin outputs → Bool) (replacement : Fin inputs → Expr outputs)
    (expression : Expr inputs) :
    (expression.bind replacement).eval values =
      expression.eval (fun input => (replacement input).eval values) := by
  induction expression <;> simp_all [bind,eval]

theorem Expr.eval_of_map (actual : Expr outputs) (localExpression : Expr inputs)
    (rename : Fin inputs → Fin outputs) (shape : actual = localExpression.map rename)
    (values : Fin outputs → Bool) :
    actual.eval values = localExpression.eval (values ∘ rename) := by
  rw [shape,eval_map]

end Pinwheel.Hardware.StreamingMapped
