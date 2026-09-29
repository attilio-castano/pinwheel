import Pinwheel.Hardware.Storage.PairedImage
import Pinwheel.Hardware.Loader.Proofs

/-! The paired upload protocol has 290 words. The ledger records only accepted
words since the latest begin; it is proof state, not additional hardware.
Contents before an accepted upload remain arbitrary. -/
namespace Pinwheel.Hardware.Storage.PairedLoader
open Pinwheel.Hardware

inductive Slot : Nat → Type where
  | parameter : BitVec 5 → Slot 20
  | row : BitVec 8 → Slot 64
  | boot : Slot 32
  | idle : Slot 6

def offset : Slot w → Nat
  | .parameter k => k.toNat
  | .row k => 32 + k.toNat
  | .boot => 288
  | .idle => 289

abbrev Banks := Bool → Values Slot

def push (i : Loader.Inputs) (good : Bool) (c : Loader.State) : Bool :=
  Loader.enabled i && i.command == 2 && c.pending && c.cursor.toNat < 290 && good

def commit (i : Loader.Inputs) (c : Loader.State) : Bool :=
  Loader.enabled i && i.command == 3 && c.pending && c.cursor == 290

def next (i : Loader.Inputs) (good : Bool) (c : Loader.State) : Loader.State :=
  if i.init then {} else if i.reset then {c with pending := false, cursor := 0}
  else if i.busy then c
  else if i.command == 1 then {c with pending := true, cursor := 0}
  else if i.command == 4 then {c with pending := false, cursor := 0}
  else if commit i c then ⟨!c.active, true, false, 0⟩
  else if push i good c then {c with cursor := c.cursor - 511}
  else c

def write (i : Loader.Inputs) (good : Bool) (c : Loader.State) (banks : Banks) : Banks :=
  fun b {_} slot =>
    if push i good c && b != c.active && c.cursor.toNat == offset slot
    then i.data.extractLsb' 0 _ else banks b slot

structure Ledger where
  active : List (BitVec 64) := []
  staged : List (BitVec 64) := []

def record (i : Loader.Inputs) (good : Bool) (c : Loader.State) (l : Ledger) : Ledger :=
  if i.init then {} else if i.reset then {l with staged := []}
  else if i.busy then l
  else if i.command == 1 || i.command == 4 then {l with staged := []}
  else if commit i c then ⟨l.staged, []⟩
  else if push i good c then {l with staged := l.staged ++ [i.data]}
  else l

def Matches (bank : Values Slot) (words : List (BitVec 64)) : Prop :=
  ∀ {w} (slot : Slot w), bank slot = (words.getD (offset slot) 0).extractLsb' 0 w

/-- Both length and contents are tied to the accepted transcript. Clearing a
ledger on begin/abort/reset makes no claim that physical storage is cleared. -/
structure Invariant (c : Loader.State) (banks : Banks) (l : Ledger) : Prop where
  bounded : c.cursor.toNat ≤ 290
  active : c.valid = true → l.active.length = 290 ∧ Matches (banks c.active) l.active
  staged : c.pending = true → l.staged.length = c.cursor.toNat ∧
    ∀ {w} (slot : Slot w), offset slot < c.cursor.toNat →
      banks (!c.active) slot = (l.staged.getD (offset slot) 0).extractLsb' 0 w

theorem push_requires (i : Loader.Inputs) (good : Bool) (c : Loader.State)
    (h : push i good c = true) :
    i.init = false ∧ i.reset = false ∧ i.busy = false ∧ i.command = 2 ∧
      c.pending = true ∧ c.cursor.toNat < 290 ∧ good = true := by
  simpa [push, Loader.enabled, Bool.and_assoc] using h

theorem push_next (i : Loader.Inputs) (good : Bool) (c : Loader.State)
    (h : push i good c = true) : next i good c = {c with cursor := c.cursor - 511} := by
  obtain ⟨hi, hr, hb, hc, _, _, _⟩ := push_requires i good c h
  simp [next, hi, hr, hb, hc, h, commit]
  done

theorem commit_requires (i : Loader.Inputs) (c : Loader.State) (h : commit i c = true) :
    i.init = false ∧ i.reset = false ∧ i.busy = false ∧ i.command = 3 ∧
      c.pending = true ∧ c.cursor = 290 := by
  simpa [commit, Loader.enabled, Bool.and_assoc] using h

theorem write_active (i : Loader.Inputs) (good : Bool) (c : Loader.State)
    (banks : Banks) (slot : Slot w) : write i good c banks c.active slot = banks c.active slot := by
  simp [write]

theorem offset_lt (slot : Slot w) : offset slot < 290 := by
  cases slot <;> simp only [offset] <;> bv_omega

theorem invariant_next (i : Loader.Inputs) (good : Bool) (c : Loader.State)
    (banks : Banks) (l : Ledger) (h : Invariant c banks l) :
    Invariant (next i good c) (write i good c banks) (record i good c l) := by
  by_cases hp : push i good c = true
  · obtain ⟨hi, hr, hb, hc, hpend, hcur, _⟩ := push_requires i good c hp
    simp [push_next i good c hp, record, hi, hr, hb, hc, commit, hp]
    have hinc := Loader.cursor_increment c.cursor (by omega)
    refine ⟨(show (c.cursor - 511).toNat ≤ 290 from by omega), ?_, ?_⟩
    · simpa only [Matches, write_active] using h.active
    · refine fun _ => ⟨?_, ?_⟩
      · change (l.staged ++ [i.data]).length = (c.cursor - 511).toNat
        simp only [List.length_append, List.length_singleton, hinc, (h.staged hpend).1]
        done
      · intro w slot hk
        change offset slot < (c.cursor - 511).toNat at hk
        by_cases hlt : offset slot < c.cursor.toNat
        · simp [write, hp, show c.cursor.toNat ≠ offset slot from by omega,
            (h.staged hpend).2 slot hlt, List.getElem?_append, (h.staged hpend).1, hlt]
          done
        · have he : c.cursor.toNat = offset slot := by omega
          simp [write, hp, he, (h.staged hpend).1]
          done
  · have hw : write i good c banks = banks := by funext b w slot; simp [write, hp]
    rw [hw]
    by_cases hc : commit i c = true
    · obtain ⟨hi, hr, hb, hcmd, hpend, hcur⟩ := commit_requires i c hc
      simp [next, record, hi, hr, hb, hcmd, hc]
      exact ⟨Nat.zero_le _, fun _ => ⟨by simpa [hcur] using (h.staged hpend).1,
        fun slot => (h.staged hpend).2 slot (by simpa [hcur] using offset_lt slot)⟩, by simp⟩
      done
    · by_cases hi : i.init = true <;> by_cases hr : i.reset = true <;>
        by_cases hb : i.busy = true <;> by_cases h1 : i.command = 1 <;>
        by_cases h4 : i.command = 4 <;>
        simp_all [next, record] <;>
        first | exact h | exact ⟨Nat.zero_le _, h.active, by simp⟩ |
          exact ⟨Nat.zero_le _, by simp, by simp⟩
      done

def imageValues (image : PairedImage.Image) : Values Slot
  | _, .parameter k => image.parameters[k.toNat]
  | _, .row k => image.rows[k.toNat]
  | _, .boot => image.boot
  | _, .idle => image.idle

theorem upload_slot (image : PairedImage.Image) (slot : Slot w) :
    ((PairedImage.upload image).getD (offset slot) 0).extractLsb' 0 w = imageValues image slot := by
  cases slot
  all_goals simp [imageValues, PairedImage.upload, offset, List.getElem?_append,
    show ∀ n : Nat, ¬32 + n < 32 from fun _ => by omega]
  case parameter k =>
    simp [show k.toNat < 32 from k.isLt]
    simp only [BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 20 ≤ 64), BitVec.extractLsb'_eq_self]
    done
  case row k =>
    simp [show k.toNat < 256 from k.isLt]
  case boot =>
    simp only [BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 32 ≤ 64), BitVec.extractLsb'_eq_self]
  case idle =>
    simp only [BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 6 ≤ 64), BitVec.extractLsb'_eq_self]

theorem image_agreement (bank : Values Slot) (image : PairedImage.Image)
    (h : Matches bank (PairedImage.upload image)) :
    (bank : Values Slot) = (imageValues image : Values Slot) :=
  funext fun _ => funext fun slot => (h slot).trans (upload_slot image slot)

theorem invariant_initialize (i : Loader.Inputs) (good : Bool) (c : Loader.State)
    (banks : Banks) (l : Ledger) (hi : i.init = true) :
    Invariant (next i good c) (write i good c banks) (record i good c l) := by
  simpa only [next, record, hi, if_true] using
    (show Invariant {} (write i good c banks) {} from ⟨Nat.zero_le _, by simp, by simp⟩)

end Pinwheel.Hardware.Storage.PairedLoader
