import Pinwheel.Hardware.Buffered.SramState
import Pinwheel.Hardware.Buffered.SramExecution
import Pinwheel.Hardware.Buffered.SharedBranchProofs

/-! Coverage facts of the actual SRAM controller expressions. These laws expose
accepted upload provenance and COMMIT's resident-row/dictionary completeness;
they do not assume that SRAM cells or startup responses are zero. -/
namespace Pinwheel.Hardware.Buffered.SramCoverage
open Pinwheel.Hardware

/-- The register-only view used by the controller's actual loader logic. -/
def controlState (s : Values Sram.Register) : Values SharedBranches.Register
  | _, .row k => s (.metadata k) ++ (0 : BitVec 64)
  | _, .branch k => s (.branch k)
  | _, .branchWritten => s .branchWritten
  | _, .core r => s (.core r)

def baseInput (i : Values Sram.Input) : Values Reactive.Input := fun p => i (.base p)

theorem controlRegister_correct (r : SharedBranches.Register w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (Sram.controlRegister r).eval i s = controlState s r := by
  cases r <;> rfl
  done

theorem control_correct (e : SharedBranches.E w) (i : Values Sram.Input)
    (s : Values Sram.Register) :
    (Sram.control e).eval i s = e.eval (baseInput i) (controlState s) := by
  simp only [Sram.control, MemoBind.eval_bind, Expr.eval, controlRegister_correct]
  rfl
  done

private theorem band_one : ∀ a b : BitVec 1, a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  decide +kernel

private theorem either_one : ∀ a b : BitVec 1,
    ~~~(~~~a &&& ~~~b) = 1 ↔ a = 1 ∨ b = 1 := by
  decide +kernel

private theorem bit_one : ∀ a : BitVec 1, a.getLsbD 0 = true ↔ a = 1 := by
  decide +kernel

private theorem inv_one : ∀ a : BitVec 1, ~~~a = 1 ↔ a = 0 := by
  decide +kernel

private theorem ofBool_one (b : Bool) : BitVec.ofBool b = 1 ↔ b = true := by
  cases b <;> decide +kernel

private theorem ofBool_zero (b : Bool) : BitVec.ofBool b = 0 ↔ b = false := by
  cases b <;> decide +kernel

private theorem zero_ne_one : (0 : BitVec 1) ≠ 1 := by decide +kernel

private theorem foldl_one (xs : List α) (f : α → Reactive.E 1) (acc : Reactive.E 1)
    (i : Values Reactive.Input) (s : Values Reactive.Register) :
    (xs.foldl (fun a k => Reactive.both a (f k)) acc).eval i s = 1 ↔
      acc.eval i s = 1 ∧ ∀ k ∈ xs, (f k).eval i s = 1 := by
  induction xs generalizing acc with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih]
    simp only [Reactive.both, Expr.eval, band_one, List.mem_cons, forall_eq_or_imp, and_assoc]
    done

private theorem pack_selected_bit (n : Nat) (f : Fin n → SharedBranches.E 1)
    (i : Values SharedBranches.Input) (s : Values SharedBranches.Register) (k : Fin n) :
    ((SharedBranches.pack f).eval i s).getLsbD k.val = ((f k).eval i s).getLsbD 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => exact Fin.elim0 k
    | succ n =>
      cases n with
      | zero => have hk : k = 0 := Fin.ext (by omega); subst k; rfl
      | succ n =>
        cases k using Fin.cases with
        | zero => simp only [SharedBranches.pack, Expr.eval, Fin.val_zero, BitVec.getLsbD_append]; rfl
        | succ k =>
          have hnot : ¬ (k.val+1 < 1) := by omega
          simpa only [SharedBranches.pack, Expr.eval, BitVec.getLsbD_append, Fin.val_succ,
            hnot, if_false, Nat.add_sub_cancel] using
            ih (n+1) (by omega) (fun j => f j.succ) k
          done

/-- A true coverage conjunction contains every selected row-coverage bit. -/
theorem covered_selected (i : Values Reactive.Input) (s : Values Reactive.Register)
    (h : Reactive.covered.eval i s = 1) (k : Fin 64)
    (hk : k.val < (i .count).toNat) :
    (s .written).getLsbD k.val = true := by
  unfold Reactive.covered at h
  have hbit := ((foldl_one _ _ _ i s).mp h).2 k (by simp)
  simp only [Reactive.either, Expr.eval] at hbit
  rw [either_one] at hbit
  simp only [inv_one, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans k.isLt (by decide +kernel : 64 < 2^7)), hk,
    decide_true, BitVec.ofBool_true, (Ne.symm zero_ne_one), false_or] at hbit
  simpa only [BitVec.getLsbD_extractLsb', Nat.add_zero, show decide (0 < 1) = true from rfl, Bool.true_and] using (bit_one _).mpr hbit
  done

/-- Accepted COMMIT requires every currently live row to have an actual accepted
upload in the pending generation. -/
theorem commit_rows (i : Values Sram.Input) (s : Values Sram.Register)
    (h : Sram.committing.eval i s = 1) (k : BitVec 6)
    (hk : k.toNat < (i (.base .count)).toNat) :
    (s (.core .written)).getLsbD k.toNat = true := by
  simp only [Sram.committing, control_correct, SharedBranches.committing,
    SharedBranches.adapt_correct, Reactive.committing, Reactive.both, Expr.eval,
    band_one] at h
  split at h
  all_goals simp only [band_one, zero_ne_one] at h
  exact covered_selected _ _ h.2.2.2.1 k.toFin hk
  done

private theorem mapped_commit_table (i : Values SharedBranches.Input)
    (s : Values SharedBranches.Register)
    (h : SharedBranches.mappedInput i s .command = 2) : s .branchWritten = 65535 := by
  by_cases hs : s .branchWritten = 65535
  · exact hs
  · simp only [SharedBranches.mappedInput, SharedBranches.inputExpr, SharedBranches.cmd,
      SharedBranches.both, SharedBranches.tableCovered, Expr.eval, hs, decide_false,
      BitVec.ofBool_false] at h
    repeat' split at h
    all_goals simp_all
    done

/-- Accepted COMMIT also requires all sixteen dictionary slots, including
unused slots, to have been written in the pending generation. -/
theorem commit_dictionary (i : Values Sram.Input) (s : Values Sram.Register)
    (h : Sram.committing.eval i s = 1) : s .branchWritten = 65535 := by
  simp only [Sram.committing, control_correct, SharedBranches.committing,
    SharedBranches.adapt_correct, Reactive.committing, Reactive.both, Expr.eval,
    band_one] at h
  split at h
  all_goals try simp only [zero_ne_one] at h
  rename_i haccept
  have hc := haccept.2
  simp only [Reactive.cmd, Expr.eval, ofBool_one] at hc
  exact mapped_commit_table _ _ (of_decide_eq_true hc)
  done

/-- A set row bit in the next actual mask comes from an accepted write to that
row, or from an already set bit. Reset and first-write clearing cannot invent it. -/
theorem row_mask_provenance (i : Values Sram.Input) (s : Values Sram.Register)
    (k : BitVec 6)
    (h : (Sram.circuit.step i s (.core .written)).getLsbD k.toNat = true) :
    (Sram.rowWriting.eval i s = 1 ∧ i (.base .address) = k) ∨
      (s (.core .written)).getLsbD k.toNat = true := by
  simp only [Circuit.step, Sram.circuit, Sram.next, Sram.coreNext, Sram.next_written,
    control_correct, SharedBranches.rowWrittenNext, Expr.eval] at h
  split at h
  · simp at h
  · split at h
    · rw [pack_selected_bit 64 _ _ _ (⟨k.toNat, k.isLt⟩ : Fin 64)] at h
      simp only [SharedBranches.both, Expr.eval, baseInput, controlState,
        BitVec.ofNat_toNat, band_one] at h
      split at h
      · rename_i haccept
        refine Or.inl ⟨?_, ?_⟩
        · simpa only [Sram.rowWriting, control_correct] using haccept.1
        · simpa only [BitVec.setWidth_eq] using of_decide_eq_true ((ofBool_one _).mp haccept.2)
      · split at h
        · simp at h
        · exact Or.inr (by simpa using h)
    · exact Or.inr h
  done

/-- A set dictionary bit in the next actual mask comes from an accepted write to that
slot, or from an already set bit. Reset and first-write clearing cannot invent it. -/
theorem dictionary_mask_provenance (i : Values Sram.Input) (s : Values Sram.Register)
    (k : BitVec 4)
    (h : (Sram.circuit.step i s .branchWritten).getLsbD k.toNat = true) :
    (Sram.tableWriting.eval i s = 1 ∧ (i (.base .address)).extractLsb' 0 4 = k) ∨
      (s .branchWritten).getLsbD k.toNat = true := by
  simp only [Circuit.step, Sram.circuit, Sram.next, Sram.next_branchWritten,
    control_correct, SharedBranches.branchWrittenNext, Expr.eval] at h
  split at h
  · simp at h
  · split at h
    · rw [pack_selected_bit 16 _ _ _ (⟨k.toNat, k.isLt⟩ : Fin 16)] at h
      simp only [SharedBranches.both, Expr.eval, baseInput, controlState,
        BitVec.ofNat_toNat, band_one] at h
      split at h
      · rename_i haccept
        refine Or.inl ⟨?_, ?_⟩
        · simpa only [Sram.tableWriting, control_correct] using haccept.1
        · simpa only [BitVec.setWidth_eq] using of_decide_eq_true ((ofBool_one _).mp haccept.2)
      · split at h
        · simp at h
        · exact Or.inr (by simpa using h)
    · exact Or.inr h
  done

/-- The actual reset expression clears both upload masks without clearing SRAM. -/
theorem masks_reset (i : Values Sram.Input) (s : Values Sram.Register)
    (h : (Sram.control SharedBranches.resetting).eval i s = 1) :
    Sram.circuit.step i s (.core .written) = 0 ∧
      Sram.circuit.step i s .branchWritten = 0 := by
  rw [control_correct] at h
  simp only [Circuit.step, Sram.circuit, Sram.next, Sram.coreNext, Sram.next_written,
    Sram.next_branchWritten, control_correct, SharedBranches.rowWrittenNext,
    SharedBranches.branchWrittenNext, Expr.eval, h, if_true, and_self]
  done

/-- A physical initialization edge establishes empty masks from arbitrary FFs. -/
theorem cold_masks (i : Values Sram.Input) (s : Values Sram.Register)
    (h : i (.base .initialize) = 1) :
    Sram.circuit.step i s (.core .written) = 0 ∧
      Sram.circuit.step i s .branchWritten = 0 := by
  apply masks_reset
  simp [control_correct, SharedBranches.resetting, SharedBranches.raw_correct,
    Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, baseInput, h]
  done

private theorem mapped_command_two (i : Values SharedBranches.Input)
    (s : Values SharedBranches.Register)
    (h : SharedBranches.mappedInput i s .command = 2) : i .command = 2 := by
  simp only [SharedBranches.mappedInput, SharedBranches.inputExpr, Expr.eval] at h
  repeat' split at h
  all_goals simp_all
  done

/-- COMMIT acceptance comes only from the actual COMMIT opcode. -/
theorem commit_command (i : Values Sram.Input) (s : Values Sram.Register)
    (h : Sram.committing.eval i s = 1) : i (.base .command) = 2 := by
  simp only [Sram.committing, control_correct, SharedBranches.committing,
    SharedBranches.adapt_correct, Reactive.committing, Reactive.both, Expr.eval,
    band_one] at h
  split at h
  all_goals try simp only [zero_ne_one] at h
  rename_i haccept
  have hc := haccept.2
  simp only [Reactive.cmd, Expr.eval, ofBool_one] at hc
  exact mapped_command_two _ _ (of_decide_eq_true hc)
  done

/-- An accepted COMMIT does not occupy either SRAM port with a row write. -/
theorem commit_no_row (i : Values Sram.Input) (s : Values Sram.Register)
    (h : Sram.committing.eval i s = 1) : Sram.rowWriting.eval i s = 0 := by
  have hc := commit_command i s h
  simp [Sram.rowWriting, control_correct, SharedBranches.rowWriting,
    SharedBranches.both, SharedBranches.cmd, Expr.eval, baseInput, hc]
  done

/-- An accepted COMMIT does not update a dictionary entry. -/
theorem commit_no_table (i : Values Sram.Input) (s : Values Sram.Register)
    (h : Sram.committing.eval i s = 1) : Sram.tableWriting.eval i s = 0 := by
  have hc := commit_command i s h
  simp [Sram.tableWriting, control_correct, SharedBranches.tableWriting,
    SharedBranches.both, SharedBranches.cmd, Expr.eval, baseInput, hc]
  done

/-- The actual COMMIT checker admits a nonempty resident prefix of at most64. -/
theorem commit_count_bounds (i : Values Sram.Input) (s : Values Sram.Register)
    (h : Sram.committing.eval i s = 1) :
    0 < (i (.base .count)).toNat ∧ (i (.base .count)).toNat ≤ 64 := by
  simp only [Sram.committing, control_correct, SharedBranches.committing,
    SharedBranches.adapt_correct, Reactive.committing, Reactive.both, Expr.eval,
    band_one] at h
  split at h
  all_goals simp only [band_one, zero_ne_one] at h
  have hc := h.2.1
  simp only [Reactive.countValid, Reactive.both, Expr.eval, band_one, inv_one] at hc
  simp only [ofBool_zero] at hc
  simp [SharedBranches.mappedInput, SharedBranches.inputExpr, Expr.eval, baseInput] at hc
  simpa only [← BitVec.toNat_inj, BitVec.toNat_zero, Nat.pos_iff_ne_zero] using hc
  done

/-- Each dictionary slot is present at an accepted COMMIT. -/
theorem commit_dictionary_bit (i : Values Sram.Input) (s : Values Sram.Register)
    (h : Sram.committing.eval i s = 1) (k : BitVec 4) :
    (s .branchWritten).getLsbD k.toNat = true := by
  rw [commit_dictionary i s h]
  exact (by decide +kernel : ∀ k : BitVec 4, (65535 : BitVec 16).getLsbD k.toNat = true) k
  done

/-- Without reset or an accepted row/dictionary upload, both actual masks hold. -/
theorem masks_hold (i : Values Sram.Input) (s : Values Sram.Register)
    (hr : (Sram.control SharedBranches.resetting).eval i s = 0)
    (hw : (Sram.control SharedBranches.writing).eval i s = 0) :
    Sram.circuit.step i s (.core .written) = s (.core .written) ∧
      Sram.circuit.step i s .branchWritten = s .branchWritten := by
  rw [control_correct] at hr hw
  simp only [Circuit.step, Sram.circuit, Sram.next, Sram.coreNext, Sram.next_written,
    Sram.next_branchWritten, control_correct, SharedBranches.rowWrittenNext,
    SharedBranches.branchWrittenNext, Expr.eval, hr, hw, zero_ne_one, if_false,
    controlState, and_self]
  done

/-- COMMIT acceptance excludes the common upload predicate. -/
theorem commit_no_writing (i : Values Sram.Input) (s : Values Sram.Register)
    (h : Sram.committing.eval i s = 1) :
    (Sram.control SharedBranches.writing).eval i s = 0 := by
  have hc := commit_command i s h
  have hd := commit_dictionary i s h
  simp [control_correct, SharedBranches.writing, SharedBranches.adapt_correct,
    Reactive.writing, Reactive.cmd, Reactive.both, Expr.eval, SharedBranches.mappedInput,
    SharedBranches.inputExpr, SharedBranches.cmd, SharedBranches.both,
    SharedBranches.tableCovered, controlState, baseInput, hc, hd]
  done

private theorem mapped_command_seven (i : Values SharedBranches.Input)
    (s : Values SharedBranches.Register) :
    SharedBranches.mappedInput i s .command = 7 ↔ i .command = 7 := by
  simp only [SharedBranches.mappedInput, SharedBranches.inputExpr, Expr.eval]
  repeat' split
  all_goals simp_all [SharedBranches.cmd, SharedBranches.both, Expr.eval]
  all_goals intro hc; simp_all
  done

/-- The adapter changes only upload/checker commands; reset is unchanged. -/
theorem mapped_reset (i : Values SharedBranches.Input) (s : Values SharedBranches.Register) :
    Reactive.resetting.eval (SharedBranches.mappedInput i s) (SharedBranches.expandState s) =
      SharedBranches.resetting.eval i s := by
  simp only [SharedBranches.resetting, SharedBranches.raw_correct,
    Reactive.resetting, Reactive.either, Reactive.cold, Reactive.warm, Reactive.both,
    Reactive.cmd, Expr.eval, mapped_command_seven]
  simp only [SharedBranches.mappedInput, SharedBranches.inputExpr, Expr.eval]
  rfl
  done

def resetting : Sram.E 1 := Sram.control SharedBranches.resetting
def writing : Sram.E 1 := Sram.control SharedBranches.writing

theorem valid_step (i : Values Sram.Input) (s : Values Sram.Register) :
    Sram.circuit.step i s (.core .valid) =
      if resetting.eval i s = 1 ∨ writing.eval i s = 1 then 0
      else if Sram.committing.eval i s = 1 then 1 else s (.core .valid) := by
  change (Sram.adapt (SharedBranches.adapt (Reactive.next .valid))).eval i s = _
  rw [SramExecution.scalar_valid_controlled, control_correct, SharedBranches.adapt_correct]
  simp only [resetting, writing, Sram.committing, control_correct, SharedBranches.writing,
    SharedBranches.committing, SharedBranches.adapt_correct, Reactive.next, Reactive.either,
    Expr.eval, either_one, mapped_reset, SharedBranches.expandState, controlState]
  done

theorem count_step (i : Values Sram.Input) (s : Values Sram.Register) :
    Sram.circuit.step i s (.core .count) =
      if resetting.eval i s = 1 then 0
      else if Sram.committing.eval i s = 1 then i (.base .count) else s (.core .count) := by
  change (Sram.adapt (SharedBranches.adapt (Reactive.next .count))).eval i s = _
  rw [SramExecution.scalar_count_controlled, control_correct, SharedBranches.adapt_correct]
  simp only [resetting, Sram.committing, control_correct, SharedBranches.committing,
    SharedBranches.adapt_correct, Reactive.next, Expr.eval, mapped_reset,
    SharedBranches.expandState, controlState]
  rfl
  done

/-- A valid resident image was admitted with complete actual upload masks. -/
def ValidCoverage (s : Values Sram.Register) : Prop :=
  s (.core .valid) = 1 →
    (∀ k : BitVec 6, k.toNat < (s (.core .count)).toNat →
      (s (.core .written)).getLsbD k.toNat = true) ∧ s .branchWritten = 65535

/-- Every actual controller edge preserves resident coverage, including rejected
commands while busy or retaining a result. -/
theorem valid_next (i : Values Sram.Input) (s : Values Sram.Register)
    (h : ValidCoverage s) : ValidCoverage (Sram.circuit.step i s) := by
  intro hv
  change Sram.circuit.step i s (.core .valid) = 1 at hv
  rw [valid_step] at hv
  split at hv
  · exact (zero_ne_one hv).elim
  · rename_i hn
    have hr : resetting.eval i s = 0 :=
      (BitVec.eq_zero_or_eq_one _).resolve_right (fun h => hn (Or.inl h))
    have hw : writing.eval i s = 0 :=
      (BitVec.eq_zero_or_eq_one _).resolve_right (fun h => hn (Or.inr h))
    have hm := masks_hold i s hr hw
    change (∀ k : BitVec 6, k.toNat < (Sram.circuit.step i s (.core .count)).toNat →
      (Sram.circuit.step i s (.core .written)).getLsbD k.toNat = true) ∧
      Sram.circuit.step i s .branchWritten = 65535
    simp only [count_step, hr, zero_ne_one, if_false, hm.1, hm.2]
    split at hv
    · rename_i hc
      simp only [hc, if_true]
      exact ⟨fun k hk => commit_rows i s hc k hk, commit_dictionary i s hc⟩
    · rename_i hc
      simpa only [hc, if_false] using h hv
  done

theorem cold_resetting (i : Values Sram.Input) (s : Values Sram.Register)
    (h : i (.base .initialize) = 1) : resetting.eval i s = 1 := by
  simp [resetting, control_correct, SharedBranches.resetting, SharedBranches.raw_correct,
    Reactive.resetting, Reactive.cold, Reactive.either, Expr.eval, baseInput, h]
  done

/-- Initialization establishes resident coverage by invalidating the old image. -/
theorem valid_cold (i : Values Sram.Input) (s : Values Sram.Register)
    (h : i (.base .initialize) = 1) : ValidCoverage (Sram.circuit.step i s) := by
  intro hv
  change Sram.circuit.step i s (.core .valid) = 1 at hv
  rw [valid_step] at hv
  simp only [cold_resetting i s h, true_or, if_true, zero_ne_one] at hv
  done

/-- Any post-edge valid state excludes reset and both kinds of accepted upload. -/
theorem valid_post_no_clear (i : Values Sram.Input) (s : Values Sram.Register)
    (h : Sram.circuit.step i s (.core .valid) = 1) :
    resetting.eval i s = 0 ∧ writing.eval i s = 0 := by
  rw [valid_step] at h
  split at h
  · exact (zero_ne_one h).elim
  · rename_i hn
    exact ⟨(BitVec.eq_zero_or_eq_one _).resolve_right (fun h => hn (Or.inl h)),
      (BitVec.eq_zero_or_eq_one _).resolve_right (fun h => hn (Or.inr h))⟩
  done

theorem valid_post_no_row (i : Values Sram.Input) (s : Values Sram.Register)
    (h : Sram.circuit.step i s (.core .valid) = 1) : Sram.rowWriting.eval i s = 0 := by
  have hw := (valid_post_no_clear i s h).2
  simp only [writing, control_correct] at hw
  simp only [Sram.rowWriting, control_correct, SharedBranches.rowWriting,
    SharedBranches.both, Expr.eval, hw]
  simp
  done

/-- Actual arbitrary command histories preserve resident admission coverage. -/
theorem valid_run (inputs : List (Values Reactive.Input)) (s : SramState.State)
    (h : ValidCoverage s.registers) : ValidCoverage (s.run inputs).registers := by
  induction inputs generalizing s with
  | nil => exact h
  | cons i rest ih =>
    exact ih (s.step i) (valid_next (s.inputs i) s.registers h)
  done

/-- Initialized loading derives resident admission for every later history;
no initial coverage mask or memory equality is assumed. -/
theorem initialized_valid (s : SramState.State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) (inputs : List (Values Reactive.Input)) :
    ValidCoverage ((s.step i).run inputs).registers :=
  valid_run inputs (s.step i) (valid_cold (s.inputs i) s.registers hi)

/-- Valid images have a nonempty physical prefix within the64row capacity. -/
def ValidCount (s : Values Sram.Register) : Prop :=
  s (.core .valid) = 1 →
    0 < (s (.core .count)).toNat ∧ (s (.core .count)).toNat ≤ 64

theorem valid_count_next (i : Values Sram.Input) (s : Values Sram.Register)
    (h : ValidCount s) : ValidCount (Sram.circuit.step i s) := by
  intro hv
  change Sram.circuit.step i s (.core .valid) = 1 at hv
  have hr := (valid_post_no_clear i s hv).1
  have hw := (valid_post_no_clear i s hv).2
  change 0 < (Sram.circuit.step i s (.core .count)).toNat ∧
    (Sram.circuit.step i s (.core .count)).toNat ≤ 64
  rw [count_step]
  simp only [hr, zero_ne_one, if_false]
  by_cases hc : Sram.committing.eval i s = 1
  · simpa only [hc, if_true] using commit_count_bounds i s hc
  · have hold := hv
    rw [valid_step] at hold
    simp only [hr, hw, zero_ne_one, false_or, if_false, hc] at hold
    simpa only [hc, if_false] using h hold
  done

theorem valid_count_cold (i : Values Sram.Input) (s : Values Sram.Register)
    (h : i (.base .initialize) = 1) : ValidCount (Sram.circuit.step i s) := by
  intro hv
  change Sram.circuit.step i s (.core .valid) = 1 at hv
  rw [valid_step] at hv
  simp only [cold_resetting i s h, true_or, if_true, zero_ne_one] at hv
  done

theorem valid_count_run (inputs : List (Values Reactive.Input)) (s : SramState.State)
    (h : ValidCount s.registers) : ValidCount (s.run inputs).registers := by
  induction inputs generalizing s with
  | nil => exact h
  | cons i rest ih => exact ih (s.step i) (valid_count_next (s.inputs i) s.registers h)
  done

theorem initialized_count (s : SramState.State) (i : Values Reactive.Input)
    (hi : i .initialize = 1) (inputs : List (Values Reactive.Input)) :
    ValidCount ((s.step i).run inputs).registers :=
  valid_count_run inputs (s.step i) (valid_count_cold (s.inputs i) s.registers hi)

end Pinwheel.Hardware.Buffered.SramCoverage
