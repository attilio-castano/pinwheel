import Pinwheel.Hardware.Circuit

/-! Fixed-width conjunction trees preserve arbitrary input/pre-edge values.
The eight-by-eight construction has six AND levels and visits every leaf once.
Its denotation is compared with the historical left fold, rather than with
reachable states or a sampled truth table. -/
namespace Pinwheel.Hardware.BalancedConjunction

def eight (f : Fin 8 → Expr I R 1) : Expr I R 1 :=
  .band
    (.band (.band (f 0) (f 1)) (.band (f 2) (f 3)))
    (.band (.band (f 4) (f 5)) (.band (f 6) (f 7)))

def sixtyFour (f : Fin 64 → Expr I R 1) : Expr I R 1 :=
  eight fun block => eight fun position =>
    f ⟨block.val * 8 + position.val, by
      have blockBound := block.isLt
      have positionBound := position.isLt
      omega⟩

def legacySixtyFour (f : Fin 64 → Expr I R 1) : Expr I R 1 :=
  (List.finRange 64).foldl (fun acc index => .band acc (f index)) (.lit 1)

private theorem one_and (value : BitVec 1) : (1 : BitVec 1) &&& value = value := by
  change BitVec.allOnes 1 &&& value = value
  exact BitVec.allOnes_and

/-- Reassociation only: this holds for every input and every register state. -/
theorem sixtyFour_eval (inputs : Values I) (registers : Values R)
    (f : Fin 64 → Expr I R 1) :
    (sixtyFour f).eval inputs registers =
      (legacySixtyFour f).eval inputs registers := by
  simp [sixtyFour, eight, legacySixtyFour, List.finRange, List.ofFn_succ,
    Expr.eval, BitVec.and_assoc]
  change _ = (1 : BitVec 1) &&& _
  rw [one_and]
  rfl

end Pinwheel.Hardware.BalancedConjunction
