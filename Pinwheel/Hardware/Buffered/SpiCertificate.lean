import Pinwheel.Hardware.Buffered.SpiDispatch
import Pinwheel.Hardware.Buffered.GenericEncodingCanonical

/-! Static encoding and layout certificate for every supported compact SPI
configuration. It contains no controller state, runtime trace or pin agreement. -/
namespace Pinwheel.Hardware.Buffered.SpiCertificate
open Pinwheel.Hardware Pinwheel.Program GenericCertificate

/-- The counted-loop coordinates; all out-of-source endpoints use the hardware
sentinel with cleared loop indices. -/
def coordinates (c : SpiSource.Config) (pc : Program.Buffered.PC) : GenericLayout.Coordinates :=
  if pc.val < SpiCoordinates.bitSpan c + 2 then
    ⟨BitVec.ofNat 7 (SpiCoordinates.physicalPC c pc.val),
     BitVec.ofNat 3 (SpiCoordinates.outer c pc.val),
     BitVec.ofNat 3 (SpiCoordinates.inner c pc.val)⟩
  else ⟨64, 0, 0⟩

private theorem linear_encoding : ∀ duration : Fin 256, ∀ leaf : Fin 4,
    (SpiSource.encodeLinear (SpiSource.leafAt duration leaf)).getD 0 =
      GenericEncoding.encode (SpiSource.leafAt duration leaf) := by
  decide +kernel

theorem word_encoding (c : SpiSource.Config) (leaf : Fin 4) :
    SpiSource.word c (BitVec.ofNat 6 leaf.val) = GenericEncoding.encode (SpiSource.leaf c leaf) := by
  simp only [SpiSource.word, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := leaf.isLt; omega : leaf.val < 64), dif_pos leaf.isLt,
    SpiSource.leaf]
  exact linear_encoding c.halfCyclesMinusOne leaf
  done

private abbrev loopConfig (bytes : Fin 4) : SpiSource.Config := ⟨bytes, 2, by decide⟩

private theorem endpoint_certificate : ∀ bytes : Fin 4, ∀ pc : Program.Buffered.PC,
    (coordinates (loopConfig bytes) pc).row.toNat ≤ 64 ∧
      ((coordinates (loopConfig bytes) pc).row = 64 →
        (coordinates (loopConfig bytes) pc).outer = 0 ∧
        (coordinates (loopConfig bytes) pc).inner = 0) := by
  decide +kernel

private def boundedPC (v : Fin 66) : Program.Buffered.PC :=
  ⟨v.val, Nat.lt_trans v.isLt (by decide)⟩

private theorem control_certificate : ∀ bytes : Fin 4, ∀ v : Fin 66,
    v.val < SpiCoordinates.bitSpan (loopConfig bytes) + 2 →
      controlValid (SpiSource.control (loopConfig bytes)
        ((coordinates (loopConfig bytes) (boundedPC v)).row.setWidth 6))
        (coordinates (loopConfig bytes) (boundedPC v)) = true := by
  decide +kernel

private theorem successor_certificate : ∀ bytes : Fin 4, ∀ v : Fin 65,
    v.val + 1 < SpiCoordinates.bitSpan (loopConfig bytes) + 2 →
      GenericLayout.sequential
        ((SpiSource.control (loopConfig bytes)
          ((coordinates (loopConfig bytes) ⟨v.val, by have := v.isLt; omega⟩).row.setWidth 6)).extractLsb' 0 22)
        (coordinates (loopConfig bytes) ⟨v.val, by have := v.isLt; omega⟩) =
      coordinates (loopConfig bytes) ⟨v.val + 1, by have := v.isLt; omega⟩ := by
  decide +kernel

theorem span (c : SpiSource.Config) :
    (BufferedSPI.program c).code.span = SpiCoordinates.bitSpan c + 2 :=
  (BufferedSPI.geometry c).2.1

theorem live_coordinates (c : SpiSource.Config) (pc : Program.Buffered.PC)
    (within : pc.val < (BufferedSPI.program c).code.span) :
    coordinates c pc =
      ⟨BitVec.ofNat 7 (SpiCoordinates.physicalPC c pc.val),
       BitVec.ofNat 3 (SpiCoordinates.outer c pc.val),
       BitVec.ofNat 3 (SpiCoordinates.inner c pc.val)⟩ := by
  exact if_pos (by simpa only [span] using within)
  done

theorem word_field (c : SpiSource.Config) (k : BitVec 6) :
    (SpiSource.fullWords c k).extractLsb' 0 64 = SpiSource.word c k := by
  simp only [SpiSource.fullWords,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 88),
    BitVec.extractLsb'_append_eq_right]
  done

theorem control_field (c : SpiSource.Config) (k : BitVec 6) :
    (SpiSource.fullWords c k).extractLsb' 64 24 = SpiSource.control c k := by
  simp only [SpiSource.fullWords,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 64 + 24 ≤ 88),
    BitVec.extractLsb'_append_eq_left]
  done

theorem linear_finish (c : SpiSource.Config) (leaf : Fin 4)
    (map : Program.Buffered.PC → GenericLayout.Coordinates) :
    GenericLayout.instructionFinish map (SpiSource.leaf c leaf) = 0 := by
  match leaf with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl

theorem branch_field (c : SpiSource.Config) (k : BitVec 6) :
    (SpiSource.fullWords c k).extractLsb' 88 56 = 0 := by
  exact BitVec.extractLsb'_append_eq_left
  done

theorem source_record (c : SpiSource.Config) (pc : Program.Buffered.PC)
    (within : pc.val < (BufferedSPI.program c).code.span) :
    ∃ instruction, (BufferedSPI.program c).fetch pc = some instruction ∧
      SpiSource.fullWords c ((coordinates c pc).row.setWidth 6) =
        GenericLayout.record (coordinates c)
          ((SpiSource.fullWords c ((coordinates c pc).row.setWidth 6)).extractLsb' 64 24)
          instruction := by
  have bound : pc.val ≤ SpiCoordinates.bitSpan c + 1 := by rw [span] at within; omega
  let leaf : Fin 4 := ⟨SpiCoordinates.physicalPC c pc.val, SpiEntry.physicalPC_lt_four c pc.val bound⟩
  refine ⟨SpiSource.leaf c leaf, SpiRefinement.source_fetch_physical c pc bound, ?_⟩
  rw [control_field, live_coordinates c pc within]
  simp only [BitVec.setWidth_ofNat_of_le (by decide : 6 ≤ 7)]
  change SpiSource.fullWords c (BitVec.ofNat 6 leaf.val) =
    GenericLayout.record (coordinates c) (SpiSource.control c (BitVec.ofNat 6 leaf.val)) (SpiSource.leaf c leaf)
  simp only [SpiSource.fullWords, GenericLayout.record, linear_finish, word_encoding, BitVec.append_assoc]
  rfl
  done

theorem row_leaf (c : SpiSource.Config) (pc : Program.Buffered.PC)
    (within : pc.val < (BufferedSPI.program c).code.span) :
    (coordinates c pc).row.setWidth 6 = BitVec.ofNat 6 (SpiCoordinates.physicalPC c pc.val) := by
  rw [live_coordinates c pc within]
  exact BitVec.setWidth_ofNat_of_le (by decide : 6 ≤ 7) _
  done

theorem row_bound (c : SpiSource.Config) (pc : Program.Buffered.PC)
    (within : pc.val < (BufferedSPI.program c).code.span) :
    (coordinates c pc).row.toNat < 4 := by
  have bound : pc.val ≤ SpiCoordinates.bitSpan c + 1 := by rw [span] at within; omega
  have physical := SpiEntry.physicalPC_lt_four c pc.val bound
  rw [live_coordinates c pc within]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) physical
  done

theorem canonical (c : SpiSource.Config) (pc : Program.Buffered.PC)
    (within : pc.val < (BufferedSPI.program c).code.span) :
    WordCanonical ((SpiSource.fullWords c ((coordinates c pc).row.setWidth 6)).extractLsb' 0 64) := by
  have bound : pc.val ≤ SpiCoordinates.bitSpan c + 1 := by rw [span] at within; omega
  let leaf : Fin 4 := ⟨SpiCoordinates.physicalPC c pc.val, SpiEntry.physicalPC_lt_four c pc.val bound⟩
  rw [word_field, row_leaf c pc within]
  change WordCanonical (SpiSource.word c (BitVec.ofNat 6 leaf.val))
  rw [word_encoding]
  exact GenericEncoding.canonical_instruction _
  done

theorem branchCanonical (c : SpiSource.Config) (pc : Program.Buffered.PC)
    (within : pc.val < (BufferedSPI.program c).code.span) :
    BranchCanonical ((SpiSource.fullWords c ((coordinates c pc).row.setWidth 6)).extractLsb' 0 64)
      ((SpiSource.fullWords c ((coordinates c pc).row.setWidth 6)).extractLsb' 88 56) := by
  have bound : pc.val ≤ SpiCoordinates.bitSpan c + 1 := by rw [span] at within; omega
  let leaf : Fin 4 := ⟨SpiCoordinates.physicalPC c pc.val, SpiEntry.physicalPC_lt_four c pc.val bound⟩
  rw [word_field, branch_field, row_leaf c pc within]
  unfold BranchCanonical
  exact (SpiWord.branches c leaf checkInput
    (checkState (SpiSource.word c (BitVec.ofNat 6 leaf.val)) 0)
    (GenericWord.check_word _ _) (GenericWord.check_branch _ _)).1
  done

theorem normalizes (c : SpiSource.Config) (pc : Program.Buffered.PC) :
    nextNormalizes pc ((SpiSource.fullWords c ((coordinates c pc).row.setWidth 6)).extractLsb' 0 64)
      ((SpiSource.fullWords c ((coordinates c pc).row.setWidth 6)).extractLsb' 88 56) = true := by
  simp only [branch_field, nextNormalizes]
  simp
  done

theorem controlCanonical (c : SpiSource.Config) (pc : Program.Buffered.PC)
    (within : pc.val < (BufferedSPI.program c).code.span) :
    controlValid ((SpiSource.fullWords c ((coordinates c pc).row.setWidth 6)).extractLsb' 64 24)
      (coordinates c pc) = true := by
  have bound : pc.val < SpiCoordinates.bitSpan c + 2 := by simpa only [span] using within
  have small : pc.val < 66 := by have := (SpiCoordinates.bitSpan_bounds c).2; omega
  rw [control_field]
  exact control_certificate c.bytesMinusOne ⟨pc.val, small⟩ bound
  done

theorem low_control_field (c : SpiSource.Config) (k : BitVec 6) :
    (SpiSource.fullWords c k).extractLsb' 64 22 = (SpiSource.control c k).extractLsb' 0 22 := by
  simp only [SpiSource.fullWords,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 64 + 22 ≤ 88),
    BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64), Nat.sub_self]
  done

theorem successor (c : SpiSource.Config) (pc : Program.Buffered.PC)
    (within : pc.val + 1 < (BufferedSPI.program c).code.span) :
    GenericLayout.sequential
      ((SpiSource.fullWords c ((coordinates c pc).row.setWidth 6)).extractLsb' 64 22)
      (coordinates c pc) = coordinates c ⟨pc.val + 1, by have := (BufferedSPI.program c).fits; omega⟩ := by
  have bound : pc.val + 1 < SpiCoordinates.bitSpan c + 2 := by simpa only [span] using within
  have small : pc.val < 65 := by have := (SpiCoordinates.bitSpan_bounds c).2; omega
  rw [low_control_field]
  exact successor_certificate c.bytesMinusOne ⟨pc.val, small⟩ bound
  done

theorem initial (c : SpiSource.Config) : coordinates c 0 = ⟨0, 0, 0⟩ := by
  have positive := (SpiCoordinates.bitSpan_bounds c).1
  simp [coordinates, SpiCoordinates.physicalPC, SpiCoordinates.outer, SpiCoordinates.inner,
    show 0 < SpiCoordinates.bitSpan c by omega]
  done

def layout (c : SpiSource.Config) : Layout (BufferedSPI.program c) where
  count := ⟨4, by decide⟩
  positive := by decide
  words := SpiSource.fullWords c
  map := coordinates c
  initial := initial c
  endpoints := endpoint_certificate c.bytesMinusOne
  rowBound := row_bound c
  sourceRecord := source_record c
  canonical := canonical c
  branchCanonical := branchCanonical c
  controlCanonical := controlCanonical c
  normalizes := fun pc _ => normalizes c pc
  successor := successor c

end Pinwheel.Hardware.Buffered.SpiCertificate
