import Pinwheel.Hardware.Loader.Control

namespace Pinwheel.Hardware.Loader

theorem gate_correct (i : Inputs) (s : State) : gate.eval i.values s.values = BitVec.ofBool (enabled i) := by
  simp [gate, Expr.eval, Inputs.values, enabled, BitVec.ofBool_and_ofBool, Bool.and_assoc]
  done

theorem word_correct (i : Inputs) (s : State) : wordGate.eval i.values s.values = BitVec.ofBool (goodWord s.cursor i.data) := by
  simp [wordGate, Expr.eval, Inputs.values, State.values, Execution.logic_correct,
    Execution.value, goodWord]
  repeat' (first | rfl | split)
  done


set_option backward.isDefEq.respectTransparency false in
theorem push_correct (i : Inputs) (s : State) : pushGate.eval i.values s.values = BitVec.ofBool (push i s) := by
  simp [pushGate, Expr.eval, gate_correct, word_correct, command, Inputs.values, State.values,
    push, BitVec.ofBool_and_ofBool, Bool.beq_eq_decide_eq, Bool.and_assoc]
  done

set_option backward.isDefEq.respectTransparency false in
theorem commit_correct (i : Inputs) (s : State) : commitGate.eval i.values s.values = BitVec.ofBool (commit i s) := by
  simp [commitGate, Expr.eval, gate_correct, command, Inputs.values, State.values,
    commit, BitVec.ofBool_and_ofBool, Bool.beq_eq_decide_eq, Bool.and_assoc]
  done

set_option backward.isDefEq.respectTransparency false in
theorem start_correct (i : Inputs) (s : State) : startGate.eval i.values s.values = BitVec.ofBool (start i s) := by
  simp [startGate, Expr.eval, gate_correct, command, Inputs.values, State.values,
    start, BitVec.ofBool_and_ofBool, Bool.beq_eq_decide_eq, Bool.and_assoc]
  done

set_option backward.isDefEq.respectTransparency false in
theorem rejected_correct (i : Inputs) (s : State) : rejectedGate.eval i.values s.values = BitVec.ofBool (rejected i s) := by
  simp [rejectedGate, acceptedGate, orGate, Expr.eval, gate_correct, push_correct, commit_correct,
    start_correct, command, Inputs.values, BitVec.ofBool_and_ofBool, Bool.beq_eq_decide_eq, bne,
    rejected, accepted, Bool.and_assoc, Bool.or_assoc]
  done

set_option backward.isDefEq.respectTransparency false in
theorem next_correct (i : Inputs) (s : State) (r : Register w) :
    (circuit.next r).eval i.values s.values = (next i s).values r := by
  cases r <;> simp [circuit, Expr.eval, commit_correct, push_correct, command, stopped,
    committed, advanced, Inputs.values, State.values, next, Bool.beq_eq_decide_eq]
  all_goals repeat' (first | rfl | (split <;> try simp_all))
  done

theorem commit_requires_complete (i : Inputs) (s : State) (h : commit i s = true) :
    i.init = false ∧ i.reset = false ∧ i.busy = false ∧ i.command = 3 ∧ s.pending = true ∧ s.cursor = 322 := by
  simpa [commit, enabled, Bool.and_assoc] using h
  done

theorem commit_next (i : Inputs) (s : State) (h : commit i s = true) :
    next i s = ⟨!s.active, true, false, 0⟩ := by
  rcases commit_requires_complete i s h with ⟨hi, hr, hb, hc, _, _⟩
  simp [next, hi, hr, hb, hc, h]
  done

theorem push_requires_valid (i : Inputs) (s : State) (h : push i s = true) :
    i.init = false ∧ i.reset = false ∧ i.busy = false ∧ i.command = 2 ∧ s.pending = true ∧ s.cursor.toNat < 322 ∧ goodWord s.cursor i.data = true := by
  simpa [push, enabled, Bool.and_assoc] using h
  done

theorem push_next (i : Inputs) (s : State) (h : push i s = true) :
    next i s = {s with cursor := s.cursor - 511} := by
  rcases push_requires_valid i s h with ⟨hi, hr, hb, hc, _, _, _⟩
  simp [next, hi, hr, hb, hc, h, commit]
  done

theorem no_commit_preserves_selection (i : Inputs) (s : State) (hi : i.init = false) (hc : commit i s = false) :
    (next i s).active = s.active ∧ (next i s).valid = s.valid := by
  simp only [next, hi, Bool.false_eq_true, ↓reduceIte, hc]
  repeat' (first | exact ⟨rfl, rfl⟩ | split)
  done

theorem cursor_increment (c : BitVec 9) (h : c.toNat < 322) :
    (c - 511).toNat = c.toNat + 1 := by
  simp [BitVec.toNat_sub]
  omega
  done

theorem cursor_bounded (i : Inputs) (s : State) (h : s.cursor.toNat ≤ 322) :
    (next i s).cursor.toNat ≤ 322 := by
  by_cases hp : push i s = true
  · rw [push_next i s hp]
    have hc := (push_requires_valid i s hp).2.2.2.2.2.1
    change (s.cursor - 511).toNat ≤ 322
    rw [cursor_increment s.cursor hc]
    omega
  · simp only [next, hp]
    repeat' (first | exact h | exact Nat.zero_le _ | split)
  done

end Pinwheel.Hardware.Loader
