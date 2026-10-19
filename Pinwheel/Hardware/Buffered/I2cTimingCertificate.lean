import Pinwheel.Hardware.Buffered.I2cTimingWord
import Pinwheel.Hardware.Buffered.GenericEncodingCanonical

/-! A symbolic static certificate for every 8-bit I²C duration and wait budget.
The fixed counted layout is reused through proved operand retiming laws. -/
namespace Pinwheel.Hardware.Buffered.I2cTiming
open Pinwheel.Hardware Pinwheel.Program GenericCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

private theorem original_word (index : BitVec 6) :
    (I2cSource.fullWords index).extractLsb' 0 64 = I2cSource.word index := by
  simp (disch := decide) only [I2cSource.fullWords,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_eq_self]

private theorem original_branch (index : BitVec 6) :
    (I2cSource.fullWords index).extractLsb' 88 56 =
      I2cSource.dictionary (I2cSource.branchIndex index) :=
  BitVec.extractLsb'_append_eq_left

private theorem live_row (pc : Program.Buffered.PC) (within : pc.val < 270) :
    ((I2cLayout.coordinates pc).row.setWidth 6).toNat < 50 := by
  have bound := I2cLayout.coordinate_bound pc within
  simp only [BitVec.toNat_setWidth]
  omega

theorem source_record (duration budget : Fin 256) (pc : Program.Buffered.PC)
    (within : pc.val < (source duration budget).code.span) :
    ∃ i, (source duration budget).fetch pc = some i ∧
      fullWords duration budget ((I2cLayout.coordinates pc).row.setWidth 6) =
        GenericLayout.record I2cLayout.coordinates
          ((fullWords duration budget ((I2cLayout.coordinates pc).row.setWidth 6)).extractLsb' 64 24) i := by
  rcases I2cCertificate.layout.sourceRecord pc within with ⟨i, fetch, record⟩
  refine ⟨retime duration budget i, by simp only [fetch_retime, fetch, Option.map_some], ?_⟩
  have image := (congrArg (patchRecord duration budget) record).trans
    (patch_record duration budget I2cLayout.coordinates _ i)
  change patchRecord duration budget (I2cSource.fullWords ((I2cLayout.coordinates pc).row.setWidth 6)) =
    GenericLayout.record I2cLayout.coordinates
      ((I2cSource.fullWords ((I2cLayout.coordinates pc).row.setWidth 6)).extractLsb' 64 24)
      (retime duration budget i) at image
  have formed : fullWords duration budget ((I2cLayout.coordinates pc).row.setWidth 6) =
      GenericLayout.record I2cLayout.coordinates
        ((I2cSource.fullWords ((I2cLayout.coordinates pc).row.setWidth 6)).extractLsb' 64 24)
        (retime duration budget i) := by
    simpa only [fullWords, live_row pc within, ↓reduceIte] using image
  simpa only [I2cCertificate.control_field,
    (full_fields duration budget ((I2cLayout.coordinates pc).row.setWidth 6) (live_row pc within)).2.1] using formed

theorem canonical (duration budget : Fin 256) (pc : Program.Buffered.PC)
    (within : pc.val < (source duration budget).code.span) :
    WordCanonical ((fullWords duration budget ((I2cLayout.coordinates pc).row.setWidth 6)).extractLsb' 0 64) := by
  rcases source_record duration budget pc within with ⟨i, _, record⟩
  have word := congrArg (fun word : BitVec 144 => word.extractLsb' 0 64) record
  have encoded : (fullWords duration budget ((I2cLayout.coordinates pc).row.setWidth 6)).extractLsb' 0 64 =
      GenericEncoding.encode i := by
    simpa only [GenericLayout.record, BitVec.extractLsb'_append_eq_right] using word
  rw [encoded]
  exact GenericEncoding.canonical_instruction i

private theorem branch_retime (duration budget : Fin 256) (word : BitVec 64) (branch : BitVec 56)
    (valid : BranchCanonical word branch) : BranchCanonical (patchWord duration budget word) branch := by
  simpa only [BranchCanonical, Reactive.branchCanonical, Reactive.endpointCanonical,
    Reactive.isKind, Reactive.kind, Reactive.both, Reactive.either, Expr.eval,
    GenericWord.check_word, GenericWord.check_branch, patch_kind] using valid

theorem branchCanonical (duration budget : Fin 256) (pc : Program.Buffered.PC)
    (within : pc.val < (source duration budget).code.span) :
    BranchCanonical ((fullWords duration budget ((I2cLayout.coordinates pc).row.setWidth 6)).extractLsb' 0 64)
      ((fullWords duration budget ((I2cLayout.coordinates pc).row.setWidth 6)).extractLsb' 88 56) := by
  have valid := I2cCertificate.layout.branchCanonical pc within
  dsimp only [I2cCertificate.layout] at valid
  rw [original_word, original_branch] at valid
  simpa only [(full_fields duration budget ((I2cLayout.coordinates pc).row.setWidth 6) (live_row pc within)).1,
    (full_fields duration budget ((I2cLayout.coordinates pc).row.setWidth 6) (live_row pc within)).2.2.1] using
    branch_retime duration budget _ _ valid

theorem normalizes (duration budget : Fin 256) (pc : Program.Buffered.PC)
    (within : pc.val < (source duration budget).code.span) :
    nextNormalizes pc
      ((fullWords duration budget ((I2cLayout.coordinates pc).row.setWidth 6)).extractLsb' 0 64)
      ((fullWords duration budget ((I2cLayout.coordinates pc).row.setWidth 6)).extractLsb' 88 56) = true := by
  have valid := I2cCertificate.layout.normalizes pc within
  dsimp only [I2cCertificate.layout] at valid
  rw [original_word, original_branch] at valid
  simpa only [nextNormalizes,
    (full_fields duration budget ((I2cLayout.coordinates pc).row.setWidth 6) (live_row pc within)).1,
    (full_fields duration budget ((I2cLayout.coordinates pc).row.setWidth 6) (live_row pc within)).2.2.1, patch_kind] using valid

def layout (duration budget : Fin 256) : Layout (source duration budget) where
  count := ⟨50, by decide⟩
  positive := by decide
  words := fullWords duration budget
  map := I2cLayout.coordinates
  initial := I2cLayout.initial_coordinates
  endpoints := I2cCertificate.endpoints
  rowBound := fun pc within => I2cLayout.coordinate_bound pc within
  sourceRecord := source_record duration budget
  canonical := canonical duration budget
  branchCanonical := branchCanonical duration budget
  controlCanonical := by
    intro pc within
    have valid := I2cCertificate.layout.controlCanonical pc within
    dsimp only [I2cCertificate.layout] at valid
    simpa only [(full_fields duration budget ((I2cLayout.coordinates pc).row.setWidth 6) (live_row pc within)).2.1,
      I2cCertificate.control_field] using valid
  normalizes := normalizes duration budget
  successor := by
    intro pc within
    have small : pc.val < 269 := by
      have bound : pc.val + 1 < 270 := within
      omega
    rw [(full_fields duration budget ((I2cLayout.coordinates pc).row.setWidth 6)
      (live_row pc (by omega))).2.2.2]
    simpa only [I2cLayout.row, BitVec.setWidth_eq_extractLsb' (by decide : 6 ≤ 7)] using
      I2cLayout.sequential_coordinates pc small

end Pinwheel.Hardware.Buffered.I2cTiming
