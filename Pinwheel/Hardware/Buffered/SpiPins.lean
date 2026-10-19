import Pinwheel.Hardware.Buffered.SpiWord

/-! Pin-entry facts for the canonical SPI words. The transfer bit affects only
the low leaf's MOSI level; all three nonterminal leaves keep outputs enabled.
-/
namespace Pinwheel.Hardware.Buffered.SpiPins
open Pinwheel.Hardware Pinwheel.Program

private def encoded (duration : Fin 256) (leaf : Fin 4) : BitVec 64 :=
  (SpiSource.encodeLinear (SpiSource.leafAt duration leaf)).getD 0

private theorem source_word (c : SpiSource.Config) (leaf : Fin 4) :
    SpiSource.word c (BitVec.ofNat 6 leaf.val) = encoded c.halfCyclesMinusOne leaf := by
  simp [SpiSource.word, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : leaf.val < 64), leaf.isLt, SpiSource.leaf, encoded]

private theorem enable_fields : ∀ duration : Fin 256, ∀ leaf : Fin 4,
    let word := encoded duration leaf
    word.extractLsb' 6 3 = (if leaf.val = 3 then 0 else 7) ∧
    word.extractLsb' 24 1 = 0 ∧ word.extractLsb' 26 3 = 0 := by
  decide +kernel

theorem entry_enabled (c : SpiSource.Config) (leaf : Fin 4)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = SpiSource.word c (BitVec.ofNat 6 leaf.val)) :
    Reactive.entryEnabled.eval i r = if leaf.val = 3 then 0 else 7 := by
  have fields := enable_fields c.halfCyclesMinusOne leaf
  rw [source_word] at word
  simp [Reactive.entryEnabled, Reactive.preserve, Reactive.either, Expr.eval,
    word, fields.1, fields.2.1, fields.2.2]
  by_cases halted : leaf.val = 3 <;> simp [halted]
  done

private theorem release_fields : ∀ duration : Fin 256,
    let word := (SpiSource.encodeLinear (BufferedSPI.release duration)).getD 0
    word.extractLsb' 0 3 = 0 ∧ word.extractLsb' 3 3 = 0 ∧ word.extractLsb' 17 3 = 0 := by
  decide +kernel

theorem release_entry_levels (c : SpiSource.Config)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = SpiSource.word c 2) :
    Reactive.entryLevels.eval i r = 0 := by
  have fields := release_fields c.halfCyclesMinusOne
  change Reactive.entryWord.eval i r =
    (SpiSource.encodeLinear (BufferedSPI.release c.halfCyclesMinusOne)).getD 0 at word
  simp only [Reactive.entryLevels, Reactive.isKind, Reactive.kind, Reactive.preserve,
    Reactive.either, Expr.eval, word, fields.1, fields.2.1, fields.2.2]
  simp
  done

theorem low_entry_pins (c : SpiSource.Config) (i : Values Reactive.Input)
    (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = SpiSource.word c 0) :
    (⟨Reactive.entryLevels.eval i r, Reactive.entryEnabled.eval i r⟩ : Engine.Reactive.Pins) =
      Program.Buffered.shiftPins ⟨0, 7⟩ 0 false false ((Reactive.entryTx.eval i r).getLsbD 0) := by
  simp [Program.Buffered.shiftPins, SpiExecution.low_entry_levels c i r word,
    entry_enabled c (0 : Fin 4) i r word]

theorem high_entry_pins (c : SpiSource.Config) (i : Values Reactive.Input)
    (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = SpiSource.word c 1) :
    (⟨Reactive.entryLevels.eval i r, Reactive.entryEnabled.eval i r⟩ : Engine.Reactive.Pins) =
      Program.Buffered.keepPins ⟨2, 7⟩ ⟨r .levels, r .enabled⟩ 1 0 := by
  simp [Program.Buffered.keepPins, SpiExecution.high_entry_levels c i r word,
    entry_enabled c (1 : Fin 4) i r word]

theorem release_entry_pins (c : SpiSource.Config) (i : Values Reactive.Input)
    (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = SpiSource.word c 2) :
    (⟨Reactive.entryLevels.eval i r, Reactive.entryEnabled.eval i r⟩ : Engine.Reactive.Pins) =
      ⟨0, 7⟩ := by
  simp [release_entry_levels c i r word, entry_enabled c (2 : Fin 4) i r word]

end Pinwheel.Hardware.Buffered.SpiPins
