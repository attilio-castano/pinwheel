import Pinwheel.Hardware.Memory

/-! Non-wrapping runtime ranges and incremental full-word destination updates.
Lengths are natural numbers internally and use `a+1` bits at the physical
boundary, so an entire `2^a`-word memory is representable. Copy operations read
a fixed source snapshot; this algebra does not establish source stability for
an in-place physical transfer or implement a controller.
-/
namespace Pinwheel.Hardware.Memory.TransferRange

structure Range (a : Nat) where
  base : BitVec a
  length : Nat
  fits : length ≤ 2^a - base.toNat

namespace Range

def index (r : Range a) (offset : Nat) : BitVec a :=
  BitVec.ofNat a (r.base.toNat + offset)

theorem end_le (r : Range a) : r.base.toNat + r.length ≤ 2^a := by
  have hb := r.base.isLt
  have hf := r.fits
  omega

theorem index_toNat (r : Range a) (h : offset < r.length) :
    (r.index offset).toNat = r.base.toNat + offset := by
  have hb := r.end_le
  simp [index, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : r.base.toNat + offset < 2^a)]

theorem index_injective (r : Range a) (hi : i < r.length) (hj : j < r.length)
    (h : r.index i = r.index j) : i = j := by
  have hn := congrArg BitVec.toNat h
  rw [r.index_toNat hi, r.index_toNat hj] at hn
  omega

theorem index_ne (r : Range a) (hi : i < r.length) (hj : j < r.length) (h : i ≠ j) :
    r.index i ≠ r.index j := fun he => h (r.index_injective hi hj he)

theorem index_succ_toNat (r : Range a) (h : offset + 1 < r.length) :
    (r.index (offset + 1)).toNat = (r.index offset).toNat + 1 := by
  rw [r.index_toNat h, r.index_toNat (by omega)]
  omega

def empty (base : BitVec a) : Range a := ⟨base, 0, Nat.zero_le _⟩
def full (a : Nat) : Range a := ⟨0, 2^a, by simp⟩

def decode (base : BitVec a) (length : BitVec (a+1)) : Option (Range a) :=
  if h : length.toNat ≤ 2^a - base.toNat then some ⟨base, length.toNat, h⟩ else none

def encodedLength (r : Range a) : BitVec (a+1) := BitVec.ofNat (a+1) r.length

theorem encodedLength_toNat (r : Range a) : r.encodedLength.toNat = r.length := by
  have hb := r.end_le
  have hp : 0 < 2^a := Nat.pow_pos (by decide)
  simp [encodedLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (by rw [Nat.pow_succ]; omega : r.length < 2^(a+1))]

theorem decode_encode (r : Range a) : decode r.base r.encodedLength = some r := by
  simp [decode, r.encodedLength_toNat, r.fits]

theorem decode_none_iff (base : BitVec a) (length : BitVec (a+1)) :
    decode base length = none ↔ 2^a - base.toNat < length.toNat := by
  simp [decode]

theorem decode_fields (base : BitVec a) (length : BitVec (a+1)) (range : Range a)
    (h : decode base length = some range) : range.base = base ∧ range.length = length.toNat := by
  simp only [decode] at h
  split at h <;> cases h <;> exact ⟨rfl, rfl⟩

end Range

/-- Exactly `k` successive full-word writes. Bounds are theorem hypotheses, so
the executable update function is total even outside a checked range. -/
def writePrefix (range : Range a) (initial : Contents a w) (value : Nat → BitVec w) : Nat → Contents a w
  | 0 => initial
  | k+1 => (writePrefix range initial value k).write ⟨true, range.index k, value k⟩

theorem prefix_written (range : Range a) (initial : Contents a w) (value : Nat → BitVec w)
    (k : Nat) (hk : k ≤ range.length) (j : Nat) (hj : j < k) :
    writePrefix range initial value k (range.index j) = value j := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    by_cases he : j = k
    · subst j
      exact write_same _ _ rfl
    · rw [writePrefix, write_other _ _ _ (range.index_ne (by omega) (by omega) (Ne.symm he))]
      exact ih (by omega) j (by omega)

theorem prefix_unchanged (range : Range a) (initial : Contents a w) (value : Nat → BitVec w)
    (k : Nat) (address : BitVec a) (h : ∀ j, j < k → range.index j ≠ address) :
    writePrefix range initial value k address = initial address := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [writePrefix, write_other _ _ _ (h k (by omega))]
    exact ih (fun j hj => h j (by omega))

/-- The completed prefix contains exactly its assigned values; every other
address retains the initial destination word. -/
theorem prefix_patch (range : Range a) (initial : Contents a w) (value : Nat → BitVec w)
    (k : Nat) (hk : k ≤ range.length) (address : BitVec a) :
    writePrefix range initial value k address =
      if range.base.toNat ≤ address.toNat ∧ address.toNat < range.base.toNat + k
      then value (address.toNat - range.base.toNat) else initial address := by
  by_cases h : range.base.toNat ≤ address.toNat ∧ address.toNat < range.base.toNat + k
  · rw [if_pos h]
    have hi : range.index (address.toNat - range.base.toNat) = address := by
      apply BitVec.eq_of_toNat_eq
      rw [range.index_toNat (by omega)]
      omega
    have written := prefix_written range initial value k hk
      (address.toNat - range.base.toNat) (by omega)
    rw [hi] at written
    exact written
  · rw [if_neg h]
    apply prefix_unchanged
    intro j hj he
    have hn := congrArg BitVec.toNat he
    rw [range.index_toNat (by omega)] at hn
    omega

/-- A controller-facing invariant that does not depend on the representation
or construction history of the current destination memory. -/
def Patched (range : Range a) (initial : Contents a w) (value : Nat → BitVec w)
    (completed : Nat) (current : Contents a w) : Prop :=
  ∀ address, current address =
    if range.base.toNat ≤ address.toNat ∧ address.toNat < range.base.toNat + completed
    then value (address.toNat - range.base.toNat) else initial address

theorem patched_zero (range : Range a) (initial : Contents a w) (value : Nat → BitVec w) :
    Patched range initial value 0 initial :=
  prefix_patch range initial value 0 (Nat.zero_le _)

/-- One accepted full-word destination write extends the prefix by one and
preserves every word outside that new prefix. -/
theorem patch_step (range : Range a) (initial current : Contents a w) (value : Nat → BitVec w)
    (k : Nat) (hk : k < range.length) (h : Patched range initial value k current) :
    Patched range initial value (k+1) (current.write ⟨true, range.index k, value k⟩) := by
  have he : current = writePrefix range initial value k := by
    funext address
    exact (h address).trans (prefix_patch range initial value k (by omega) address).symm
  rw [he]
  exact prefix_patch range initial value (k+1) (by omega)

def copyValue (sourceRange : Range a) (source : Contents a wi)
    (f : BitVec wi → BitVec wo) (offset : Nat) : BitVec wo :=
  f (source (sourceRange.index offset))

def copyPrefix (sourceRange destinationRange : Range a) (source : Contents a wi)
    (initial : Contents a wo) (f : BitVec wi → BitVec wo) (completed : Nat) : Contents a wo :=
  writePrefix destinationRange initial (copyValue sourceRange source f) completed

theorem copyPrefix_patch (sourceRange destinationRange : Range a) (source : Contents a wi)
    (initial : Contents a wo) (f : BitVec wi → BitVec wo)
    (sameLength : sourceRange.length = destinationRange.length)
    (k : Nat) (hk : k ≤ sourceRange.length) (address : BitVec a) :
    copyPrefix sourceRange destinationRange source initial f k address =
      if destinationRange.base.toNat ≤ address.toNat ∧
          address.toNat < destinationRange.base.toNat + k
      then f (source (sourceRange.index (address.toNat - destinationRange.base.toNat)))
      else initial address :=
  prefix_patch destinationRange initial (copyValue sourceRange source f) k (by omega) address

theorem copyPrefix_written (sourceRange destinationRange : Range a) (source : Contents a wi)
    (initial : Contents a wo) (f : BitVec wi → BitVec wo)
    (sameLength : sourceRange.length = destinationRange.length)
    (k : Nat) (hk : k ≤ sourceRange.length) (j : Nat) (hj : j < k) :
    copyPrefix sourceRange destinationRange source initial f k (destinationRange.index j) =
      f (source (sourceRange.index j)) :=
  prefix_written destinationRange initial (copyValue sourceRange source f) k (by omega) j hj

theorem copyPrefix_unchanged (sourceRange destinationRange : Range a) (source : Contents a wi)
    (initial : Contents a wo) (f : BitVec wi → BitVec wo) (k : Nat) (address : BitVec a)
    (h : ∀ j, j < k → destinationRange.index j ≠ address) :
    copyPrefix sourceRange destinationRange source initial f k address = initial address :=
  prefix_unchanged destinationRange initial (copyValue sourceRange source f) k address h

theorem copy_patch_step (sourceRange destinationRange : Range a) (source : Contents a wi)
    (initial current : Contents a wo) (f : BitVec wi → BitVec wo)
    (sameLength : sourceRange.length = destinationRange.length)
    (k : Nat) (hk : k < sourceRange.length)
    (h : Patched destinationRange initial (copyValue sourceRange source f) k current) :
    Patched destinationRange initial (copyValue sourceRange source f) (k+1)
      (current.write ⟨true, destinationRange.index k, f (source (sourceRange.index k))⟩) :=
  patch_step destinationRange initial current (copyValue sourceRange source f) k (by omega) h

end Pinwheel.Hardware.Memory.TransferRange
