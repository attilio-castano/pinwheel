import Init.Omega

/-! Small range proofs compose without evaluating a large universal finite
decision procedure or unfolding a flat table at every gate. -/
namespace Pinwheel.Hardware.StreamingPhysical

structure Cover (predicate : Nat → Prop) (start length : Nat) : Prop where
  get : ∀ index, start ≤ index → index < start + length → predicate index

theorem Cover.single {predicate : Nat → Prop} {start : Nat}
    (proof : predicate start) : Cover predicate start 1 := by
  constructor
  intro index low high
  have equal : index = start := by omega
  exact equal ▸ proof

theorem Cover.append {predicate : Nat → Prop} {start left right : Nat}
    (first : Cover predicate start left) (second : Cover predicate (start + left) right) :
    Cover predicate start (left + right) := by
  constructor
  intro index low high
  by_cases split : index < start + left
  · exact first.get index low split
  · exact second.get index (Nat.le_of_not_gt split) (by omega)

end Pinwheel.Hardware.StreamingPhysical
