import Pinwheel.Engine.ReactiveProofs

namespace Pinwheel.Engine.Reactive

theorem checked_fault (p : Program) (pc : Fin 128) (a : Checked) (remaining : Fin 256)
    (pins : Pins) (slots : Samples) (inputs : Inputs)
    (hp : p.fetch pc = .checked a) (hg : a.guard.ready inputs = false) :
    advance p ⟨.checked pc remaining, pins, slots⟩ inputs = stop p .fault slots := by
  simp [advance, hp, hg]
  done

/-- The guard is checked before terminal capture or control-flow changes. -/
theorem checked_boundary (p : Program) (pc : Fin 128) (a : Checked)
    (pins : Pins) (slots : Samples) (inputs : Inputs)
    (hp : p.fetch pc = .checked a) (hg : a.guard.ready inputs = true) :
    advance p ⟨.checked pc 0, pins, slots⟩ inputs =
      dispatch p pc a.finish (capture slots a.terminalCapture inputs) inputs := by
  simp [advance, hp, hg]
  done

theorem branch_selection (p : Program) (pc yes no : Fin 128) (sample : Fin 8)
    (slots : Samples) (inputs : Inputs) :
    dispatch p pc (.branch sample yes no) slots inputs =
      jump p (if slots[sample.val] then yes else no) slots inputs := rfl

theorem invalid_jump (p : Program) (target : Fin 128) (slots : Samples) (inputs : Inputs)
    (h : p.last.val < target.val) : jump p target slots inputs = stop p .fault slots := by
  simp [jump, show ¬target.val ≤ p.last.val by omega]
  done

theorem qualify_blocked (p : Program) (pc : Fin 128) (q : Qualify)
    (remaining waitLeft : Fin 256) (pins : Pins) (slots : Samples) (inputs : Inputs)
    (hp : p.fetch pc = .qualify q) (hi : q.condition.ready inputs = false) (hw : 0 < waitLeft.val) :
    advance p ⟨.qualifying pc remaining waitLeft, pins, slots⟩ inputs =
      ⟨.qualifying pc q.durationMinusOne ⟨waitLeft.val - 1, by omega⟩, pins, slots⟩ := by
  simp [advance, hp, hi, hw]
  done

theorem qualify_ready_count (p : Program) (pc : Fin 128) (q : Qualify)
    (remaining waitLeft : Fin 256) (pins : Pins) (slots : Samples) (inputs : Inputs)
    (hp : p.fetch pc = .qualify q) (hi : q.condition.ready inputs = true) (hr : 0 < remaining.val) :
    advance p ⟨.qualifying pc remaining waitLeft, pins, slots⟩ inputs =
      ⟨.qualifying pc ⟨remaining.val - 1, by omega⟩ q.budgetMinusOne, pins, slots⟩ := by
  simp [advance, hp, hi, hr]
  done

theorem qualify_ready_boundary (p : Program) (pc : Fin 128) (q : Qualify)
    (waitLeft : Fin 256) (pins : Pins) (slots : Samples) (inputs : Inputs)
    (hp : p.fetch pc = .qualify q) (hi : q.condition.ready inputs = true) :
    advance p ⟨.qualifying pc 0 waitLeft, pins, slots⟩ inputs = next p pc slots inputs := by
  simp [advance, hp, hi]
  done

theorem qualify_timeout (p : Program) (pc : Fin 128) (q : Qualify)
    (remaining : Fin 256) (pins : Pins) (slots : Samples) (inputs : Inputs)
    (hp : p.fetch pc = .qualify q) (hi : q.condition.ready inputs = false) :
    advance p ⟨.qualifying pc remaining 0, pins, slots⟩ inputs = stop p .timeout slots := by
  simp [advance, hp, hi]
  done

end Pinwheel.Engine.Reactive
