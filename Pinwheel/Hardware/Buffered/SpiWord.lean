import Pinwheel.Hardware.Buffered.SpiExecution

/-! Kernel certificates for the four canonical SPI words. The certificate uses
the actual Reactive expression graph; transport depends only on the decoded
word, with branch-zero checked separately. -/
namespace Pinwheel.Hardware.Buffered.SpiWord
open Pinwheel.Hardware Pinwheel.Program

private def witnessInput : Values Reactive.Input
  | _, .command => 3
  | _, _ => 0

private def witnessState (word : BitVec 64) : Values Reactive.Register
  | _, .word _ => 0#80 ++ word
  | _, .valid => 1
  | _, _ => 0

private def encoded (duration : Fin 256) (leaf : Fin 4) : BitVec 64 :=
  (SpiSource.encodeLinear (SpiSource.leafAt duration leaf)).getD 0

private theorem witness_word (word : BitVec 64) :
    Reactive.entryWord.eval witnessInput (witnessState word) = word := by
  simp [Reactive.entryWord, Reactive.entryRecord, Reactive.entering, Reactive.starting,
    Reactive.free, Reactive.busy, Reactive.resetting, Reactive.warm, Reactive.cold,
    Reactive.cmd, Reactive.space, Reactive.both, Reactive.either, Expr.eval,
    witnessInput, witnessState, Execution.readTree_correct]
  exact BitVec.extractLsb'_append_eq_right

def expectedKind (leaf : Fin 4) : BitVec 3 :=
  match leaf.val with | 0 => 1 | 1 => 2 | 2 => 0 | _ => 3

set_option maxHeartbeats 4000000 in
private theorem word_certificate : ∀ duration : Fin 256, ∀ leaf : Fin 4,
    let word := encoded duration leaf
    Reactive.canonical.eval witnessInput (witnessState word) = 1 ∧
    word.extractLsb' 0 3 = expectedKind leaf ∧
    word.extractLsb' 29 6 = 0 ∧ word.extractLsb' 35 6 = 0 ∧
    word.extractLsb' 9 8 = (if leaf.val = 3 then 0 else BitVec.ofNat 8 duration.val) ∧
    word.extractLsb' 6 3 = (if leaf.val = 3 then 0 else 7) ∧
    word.extractLsb' 22 2 = (if leaf.val = 1 then 1 else 0) := by
  simp only [Reactive.canonical, Reactive.entryTerminal, Reactive.isKind,
    Reactive.kind, Reactive.entryCapture, Reactive.terminalCapture,
    Reactive.captureCanonical, Reactive.both, Reactive.either, Expr.eval, witness_word]
  decide +kernel
  done

private theorem canonical_congr (i j : Values Reactive.Input)
    (r s : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = Reactive.entryWord.eval j s) :
    Reactive.canonical.eval i r = Reactive.canonical.eval j s := by
  simp only [Reactive.canonical, Reactive.entryTerminal, Reactive.isKind,
    Reactive.kind, Reactive.entryCapture, Reactive.terminalCapture,
    Reactive.captureCanonical, Reactive.both, Reactive.either, Expr.eval, word]
  rfl

private theorem source_word (c : SpiSource.Config) (leaf : Fin 4) :
    SpiSource.word c (BitVec.ofNat 6 leaf.val) = encoded c.halfCyclesMinusOne leaf := by
  simp [SpiSource.word, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : leaf.val < 64), leaf.isLt, SpiSource.leaf, encoded]

theorem canonical (c : SpiSource.Config) (leaf : Fin 4)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = SpiSource.word c (BitVec.ofNat 6 leaf.val)) :
    Reactive.canonical.eval i r = 1 := by
  exact (canonical_congr i witnessInput r
    (witnessState (encoded c.halfCyclesMinusOne leaf))
    ((word.trans (source_word c leaf)).trans (witness_word _).symm)).trans
      (word_certificate c.halfCyclesMinusOne leaf).1

theorem fields (c : SpiSource.Config) (leaf : Fin 4)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = SpiSource.word c (BitVec.ofNat 6 leaf.val)) :
    Reactive.kind.eval i r = expectedKind leaf ∧
    Reactive.entryCapture.eval i r = 0 ∧ Reactive.terminalCapture.eval i r = 0 ∧
    (Reactive.entryWord.eval i r).extractLsb' 9 8 =
      (if leaf.val = 3 then 0 else BitVec.ofNat 8 c.halfCyclesMinusOne.val) ∧
    (Reactive.entryWord.eval i r).extractLsb' 6 3 = (if leaf.val = 3 then 0 else 7) ∧
    (Reactive.entryWord.eval i r).extractLsb' 22 2 = (if leaf.val = 1 then 1 else 0) := by
  simpa only [Reactive.kind, Reactive.entryCapture, Reactive.terminalCapture,
    Expr.eval, word, source_word] using (word_certificate c.halfCyclesMinusOne leaf).2

theorem branches (c : SpiSource.Config) (leaf : Fin 4)
    (i : Values Reactive.Input) (r : Values Reactive.Register)
    (word : Reactive.entryWord.eval i r = SpiSource.word c (BitVec.ofNat 6 leaf.val))
    (branch : Reactive.entryBranch.eval i r = 0) :
    Reactive.branchCanonical.eval i r = 1 ∧ Reactive.nextNormalizes.eval i r = 1 := by
  simp [Reactive.branchCanonical, Reactive.nextNormalizes, Reactive.isKind,
    Reactive.both, Reactive.either, Expr.eval, (fields c leaf i r word).1,
    branch]

end Pinwheel.Hardware.Buffered.SpiWord
