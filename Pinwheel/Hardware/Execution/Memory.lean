import Pinwheel.Hardware.Decode

namespace Pinwheel.Hardware.Execution

/-- Balanced read mux: one level per address bit. The zero-width base emits no zero-width wire. -/
def readTree (bits : Nat) (words : BitVec bits → Expr I R w) (address : Expr I R bits) : Expr I R w :=
  match bits with
  | 0 => words 0
  | n + 1 => .mux (.slice 0 1 (by omega) address)
      (readTree n (fun k => words (k ++ (1#1))) (.slice 1 n (by omega) address))
      (readTree n (fun k => words (k ++ (0#1))) (.slice 1 n (by omega) address))

private theorem bit_cases (b : BitVec 1) : b = 0 ∨ b = 1 := by bv_omega

theorem readTree_correct (bits : Nat) (words : BitVec bits → Expr I R w) (address : Expr I R bits)
    (inputs : Values I) (registers : Values R) :
    (readTree bits words address).eval inputs registers =
      (words (address.eval inputs registers)).eval inputs registers := by
  induction bits with
  | zero => simp only [readTree, show address.eval inputs registers = 0 from Subsingleton.elim _ _]
  | succ n ih =>
    simp only [readTree, Expr.eval, ih]
    have h := BitVec.extractLsb'_append_extractLsb' (x := address.eval inputs registers) (w := n) (len := 1)
    rcases bit_cases ((address.eval inputs registers).extractLsb' 0 1) with hb | hb <;> simp_all
    done

end Pinwheel.Hardware.Execution
