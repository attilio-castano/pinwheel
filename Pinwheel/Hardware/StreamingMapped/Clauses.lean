import Pinwheel.Hardware.StreamingMapped.ReductionAnd

namespace Pinwheel.Hardware.StreamingMapped.Reduction

theorem xnor_dnf_clause (a b : Bool) : (a && b || !a && !b) = ((a || !b) && (!a || b)) := by
  cases a <;> cases b <;> rfl

theorem xnor_dnf_clause_swap (a b : Bool) : (!a && !b || a && b) = ((a || !b) && (!a || b)) := by
  cases a <;> cases b <;> rfl

end Pinwheel.Hardware.StreamingMapped.Reduction
