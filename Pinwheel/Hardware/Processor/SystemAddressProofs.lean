import Pinwheel.Hardware.Processor.AddressMap
namespace Pinwheel.Hardware.Processor.AddressMap
variable {rw aw : Nat} {l : Layout rw aw} {a : Access}
theorem Hit.relative_sub (h : Hit l a) :
    (a.address - BitVec.ofNat 32 (l.config.base h.region)).toNat = h.relative := by
  have hb := Nat.lt_of_le_of_lt h.contained.1 a.address.isLt
  have hle : BitVec.ofNat 32 (l.config.base h.region) ≤ a.address := by
    change l.config.base h.region % 2^32 ≤ a.address.toNat
    simpa only [Nat.mod_eq_of_lt hb] using h.contained.1
  simp only [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Hit.relative]
theorem Hit.word_slice (h : Hit l a) :
    (a.address - BitVec.ofNat 32 (l.config.base h.region)).extractLsb' 2 (h.region.wordWidth rw aw) = h.wordAddress := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, h.relative_sub, Hit.wordAddress_toNat]
  rw [Nat.shiftRight_eq_div_pow]
  change (h.relative / 4) % 2^(h.region.wordWidth rw aw) = h.wordIndex
  exact Nat.mod_eq_of_lt h.wordIndex_lt
theorem Hit.offset_slice (h : Hit l a) : a.address.extractLsb' 0 2 = h.offset := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Hit.offset_toNat, h.offset_eq_address]
/-- Fixed-width form avoids rewriting a dependent result width when specializing
an admitted region. The hit's separate wordIndex_lt theorem prevents aliasing. -/
theorem Hit.word_slice_width (h : Hit l a) (w : Nat) :
    (a.address - BitVec.ofNat 32 (l.config.base h.region)).extractLsb' 2 w =
      BitVec.ofNat w h.wordIndex := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, h.relative_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Hit.wordIndex]
end Pinwheel.Hardware.Processor.AddressMap
