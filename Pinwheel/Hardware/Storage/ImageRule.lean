import Pinwheel.Hardware.Storage.Prefetch

/-! A rule on program words, carried by the loader.

A fetch organization may need something of the programs it runs — a condition
on each record, decidable per word. If every word pushed satisfies the rule,
every word of a committed image does, and so does every word the machine reads.
The rule is a parameter; the facts are proved once. -/
namespace Pinwheel.Hardware.Storage.ImageRule
open Loader

variable (R : BitVec 64 → Bool)

/-- The first `n` dictionary words of an image satisfy the rule. -/
def Prefix (m : Store.Image) (n : Nat) : Prop :=
  ∀ k : BitVec 6, k.toNat < n → R (m (.word k)) = true

/-- Every word of a committed image, and every word pushed so far, satisfies the rule. -/
def Images (s : Machine.State) : Prop :=
  (s.control.valid = true → Prefix R (s.memory s.control.active) 64) ∧
  (s.control.pending = true → Prefix R (s.memory (!s.control.active)) s.control.cursor.toNat)

theorem prefix_push (m : Store.Image) (c : BitVec 9) (data : BitVec 64)
    (hp : Prefix R m c.toNat) (hr : R data = true) :
    Prefix R (Store.tick ⟨true, c, data, 0⟩ m) (c.toNat + 1) := by
  intro k hk
  simp only [Store.tick, Store.offset, Bool.true_and, beq_iff_eq]
  split
  · simpa using hr
  · rename_i he
    apply hp k
    have bound := k.isLt
    have hn : c.toNat ≠ k.toNat := by
      intro hn
      apply he
      apply BitVec.eq_of_toNat_eq
      simpa [Nat.mod_eq_of_lt (by omega : k.toNat < 512)] using hn
    omega

theorem pushed (i : Machine.Inputs) (s : Machine.State) (h : Images R s) (hr : R i.data = true)
    (hp : Loader.push (Machine.controlInput i s) s.control = true) : Images R (Machine.next i s) := by
  rcases Loader.push_requires_valid (Machine.controlInput i s) s.control hp with ⟨_, _, _, _, ho, hc, _⟩
  simp only [Images, Machine.next, Loader.push_next _ _ hp]
  rw [Loader.cursor_increment _ hc]
  refine ⟨?_, ?_⟩
  · simpa [Prefix, Machine.memoryInput, Store.tick] using h.1
  · simpa [Machine.memoryInput, hp, ho] using
      prefix_push R (s.memory (!s.control.active)) s.control.cursor i.data (h.2 ho) hr

theorem committed (i : Machine.Inputs) (s : Machine.State) (h : Images R s)
    (hc : Machine.committing i s = true) : Images R (Machine.next i s) := by
  rcases Loader.commit_requires_complete (Machine.controlInput i s) s.control hc with ⟨_, _, _, _, ho, he⟩
  simp only [Images, Machine.next, Loader.commit_next _ _ hc]
  refine ⟨?_, by simp⟩
  intro _ k hk
  change R ((Machine.next i s).memory (!s.control.active) (.word k)) = true
  rw [Machine.commit_does_not_write i s hc]
  exact h.2 ho k (by simpa [he] using Nat.lt_trans hk (by decide : 64 < 322))

/-- The rule survives every edge on which the pushed word, if any, satisfies it. -/
theorem preserved (i : Machine.Inputs) (s : Machine.State) (h : Images R s) (hr : R i.data = true) :
    Images R (Machine.next i s) := by
  by_cases hp : Loader.push (Machine.controlInput i s) s.control = true
  · exact pushed R i s h hr hp
  by_cases hc : Machine.committing i s = true
  · exact committed R i s h hc
  simp only [Images, Machine.next, Loader.next, hp,
    show ¬Loader.commit (Machine.controlInput i s) s.control = true from hc, Bool.false_eq_true, ↓reduceIte]
  repeat' (first | (split <;> try simp_all [Prefix, Machine.memoryInput, Store.tick, Images]) | assumption)

/-- Initialization owes nothing: no image is committed or pending. -/
theorem initialized (i : Machine.Inputs) (s : Machine.State) (hi : i.init = true) :
    Images R (Machine.next i s) := by
  have hctl : (Machine.next i s).control = {} := (Machine.initialize_safe i s hi).1
  simp [Images, hctl]

/-- Every word the machine can read from a committed image satisfies the rule. -/
theorem read_satisfies (s : Machine.State) (h : Images R s) (hv : s.control.valid = true) (a : BitVec 8) :
    R (Loader.Store.read (s.memory s.control.active) a) = true :=
  h.1 hv _ (s.memory s.control.active (.index a)).isLt

end Pinwheel.Hardware.Storage.ImageRule
