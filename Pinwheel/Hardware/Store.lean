import Pinwheel.Hardware.Decode

namespace Pinwheel.Hardware.Store

/-- A register-bank read realized as a finite address-selected mux chain. -/
def readFrom (words : Fin 32 → Expr I R 16) (address : Expr I R 5) :
    (n : Nat) → n ≤ 32 → Expr I R 16
  | 0, _ => .lit 0
  | n + 1, h => .mux (.equal address (.lit (BitVec.ofNat 5 n)))
      (words ⟨n, by omega⟩) (readFrom words address n (by omega))

def read (words : Fin 32 → Expr I R 16) (address : Expr I R 5) : Expr I R 16 :=
  readFrom words address 32 (Nat.le_refl _)

/-- Internal atomic commit: each word captures its new value on the same accepted edge. -/
def write (words image : Fin 32 → Expr I R 16) (accept : Expr I R 1) (slot : Fin 32) : Expr I R 16 :=
  .mux accept (image slot) (words slot)

theorem readFrom_correct (words : Fin 32 → Expr I R 16) (address : Expr I R 5)
    (inputs : Values I) (registers : Values R) (n : Nat) (h : n ≤ 32)
    (within : (address.eval inputs registers).toNat < n) :
    (readFrom words address n h).eval inputs registers =
      (words (address.eval inputs registers).toFin).eval inputs registers := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [readFrom, Expr.eval]
    simp [BitVec.toNat_eq, Nat.mod_eq_of_lt (show n < 32 by omega)]
    split <;> try grind
    have hit : (⟨n, by omega⟩ : Fin 32) = (address.eval inputs registers).toFin :=
      Fin.ext (Eq.symm ‹(address.eval inputs registers).toNat = n›)
    rw [hit]

theorem read_correct (words : Fin 32 → Expr I R 16) (address : Expr I R 5)
    (inputs : Values I) (registers : Values R) :
    (read words address).eval inputs registers =
      (words (address.eval inputs registers).toFin).eval inputs registers := by
  exact readFrom_correct words address inputs registers 32 (Nat.le_refl _)
    (address.eval inputs registers).isLt

end Pinwheel.Hardware.Store
