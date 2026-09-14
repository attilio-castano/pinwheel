import Pinwheel.Hardware.Loader.MachineProofs

namespace Pinwheel.Hardware.Loader.Machine

/-- Uploads cannot write the currently selected image, including its metadata. -/
theorem active_memory_preserved (i : Inputs) (s : State) (r : Store.Register w) :
    (next i s).memory s.control.active r = s.memory s.control.active r := by
  simp [next, Store.tick, memoryInput]
  done

theorem interrupted_upload_preserves_program (i : Inputs) (s : State)
    (hi : i.init = false) (hc : committing i s = false) (r : Store.Register w) :
    (next i s).control.valid = s.control.valid ∧
    (next i s).memory (next i s).control.active r = s.memory s.control.active r := by
  have h := Loader.no_commit_preserves_selection (controlInput i s) s.control hi hc
  exact ⟨h.2, by simpa only [next, h.1] using active_memory_preserved i s r⟩
  done

theorem commit_does_not_write (i : Inputs) (s : State) (hc : committing i s = true)
    (b : Bool) (r : Store.Register w) : (next i s).memory b r = s.memory b r := by
  have h := (Loader.commit_requires_complete (controlInput i s) s.control hc).2.2.2.1
  simp [next, Store.tick, memoryInput, Loader.push, h]
  done

/-- Commit selects the entire prior staging image, atomically, without starting it. -/
theorem commit_switches_image (i : Inputs) (s : State) (hc : committing i s = true)
    (r : Store.Register w) :
    (next i s).control = ⟨!s.control.active, true, false, 0⟩ ∧
    (next i s).memory (next i s).control.active r = s.memory (!s.control.active) r := by
  have h := Loader.commit_next (controlInput i s) s.control hc
  exact ⟨h, by simpa only [next, h] using commit_does_not_write i s hc (!s.control.active) r⟩
  done

theorem commit_resets_execution (i : Inputs) (s : State) (hc : committing i s = true) :
    (next i s).core = ⟨0, 0, 0, 0,
      ⟨(s.memory (!s.control.active) .idle).extractLsb' 0 3,
        (s.memory (!s.control.active) .idle).extractLsb' 3 3⟩,
      Vector.replicate 16 false⟩ := by
  have hi := (Loader.commit_requires_complete (controlInput i s) s.control hc).1
  simp [next, Reactive.stepValue, Reactive.stopValue, schedulerInput, baseInput, usable, selected,
    hc, controlInput] at hi ⊢
  simp [hi]
  done

theorem initialize_safe (i : Inputs) (s : State) (hi : i.init = true) :
    (next i s).control = {} ∧ (next i s).core = ⟨0, 0, 0, 0, {}, Vector.replicate 16 false⟩ := by
  simp [next, Loader.next, controlInput, hi, Reactive.stepValue, Reactive.stopValue,
    schedulerInput, baseInput, usable]
  done

theorem uncommitted_safe (i : Inputs) (s : State) (hv : s.control.valid = false)
    (hc : committing i s = false) :
    (next i s).core = ⟨0, 0, 0, 0, {}, Vector.replicate 16 false⟩ := by
  simp [next, Reactive.stepValue, Reactive.stopValue, schedulerInput, baseInput, usable, hv, hc]
  done

def PrefixValid (m : Store.Image) (n : Nat) : Prop :=
  ∀ k : BitVec 6, k.toNat < n → Execution.validValue (m (.word k)) = true

theorem prefix_push (m : Store.Image) (c : BitVec 9) (data : BitVec 64)
    (hp : PrefixValid m c.toNat) (hg : goodWord c data = true) :
    PrefixValid (Store.tick ⟨true, c, data, 0⟩ m) (c.toNat + 1) := by
  intro k hk
  simp only [Store.tick, Store.offset, Bool.true_and, beq_iff_eq]
  split
  · rename_i he
    have bound := k.isLt
    simpa [goodWord, he, Nat.mod_eq_of_lt (by omega : k.toNat < 512), show k.toNat < 64 from bound] using hg
  · rename_i he
    apply hp k
    have bound := k.isLt
    have hn : c.toNat ≠ k.toNat := by
      intro hn
      apply he
      apply BitVec.eq_of_toNat_eq
      simpa [Nat.mod_eq_of_lt (by omega : k.toNat < 512)] using hn
    omega
  done

def Valid (s : State) : Prop :=
  s.control.cursor.toNat ≤ 322 ∧
  (s.control.valid = true → PrefixValid (s.memory s.control.active) 64) ∧
  (s.control.pending = true → PrefixValid (s.memory (!s.control.active)) s.control.cursor.toNat)

theorem valid_push (i : Inputs) (s : State) (h : Valid s)
    (hp : Loader.push (controlInput i s) s.control = true) : Valid (next i s) := by
  rcases Loader.push_requires_valid (controlInput i s) s.control hp with ⟨_, _, _, _, ho, hc, hg⟩
  simp only [Valid, next, Loader.push_next _ _ hp]
  rw [cursor_increment _ hc]
  refine ⟨hc, ?_, ?_⟩
  · simpa [PrefixValid, memoryInput, Store.tick] using h.2.1
  · simpa [memoryInput, hp, ho] using prefix_push (s.memory (!s.control.active)) s.control.cursor i.data (h.2.2 ho) hg
  done

theorem valid_commit (i : Inputs) (s : State) (h : Valid s)
    (hc : committing i s = true) : Valid (next i s) := by
  rcases Loader.commit_requires_complete (controlInput i s) s.control hc with ⟨_, _, _, _, ho, he⟩
  simp only [Valid, next, Loader.commit_next _ _ hc]
  refine ⟨by decide, ?_, by simp⟩
  intro _ k hk
  change Execution.validValue ((next i s).memory (!s.control.active) (.word k)) = true
  rw [commit_does_not_write i s hc]
  exact h.2.2 ho k (by simpa [he] using Nat.lt_trans hk (by decide : 64 < 322))
  done

theorem valid_next (i : Inputs) (s : State) (h : Valid s) : Valid (next i s) := by
  by_cases hp : Loader.push (controlInput i s) s.control = true
  · exact valid_push i s h hp
  by_cases hc : committing i s = true
  · exact valid_commit i s h hc
  simp only [Valid, next, Loader.next, hp, show ¬Loader.commit (controlInput i s) s.control = true from hc, Bool.false_eq_true, ↓reduceIte]
  repeat' (first | (split <;> try simp_all [PrefixValid, memoryInput, Store.tick, Valid]) | assumption)
  done

theorem initialize_valid (i : Inputs) (s : State) (hi : i.init = true) : Valid (next i s) := by
  simp [Valid, (initialize_safe i s hi).1]
  done

theorem valid_run (s : State) (requests : List Inputs) (h : Valid s) : Valid (run s requests) := by
  induction requests generalizing s with
  | nil => exact h
  | cons i rest ih => exact ih (next i s) (valid_next i s h)
  done

end Pinwheel.Hardware.Loader.Machine
