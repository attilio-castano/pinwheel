import Pinwheel.Hardware.Buffered.I2cLayout
import Pinwheel.Hardware.Buffered.GenericCertificate

/-! An instruction-independent layout certificate for the existing fixed
reactive I²C image. Every discharged obligation is static: finite addresses,
word/control/branch fields, or successor-coordinate arithmetic. -/
namespace Pinwheel.Hardware.Buffered.I2cCertificate
open Pinwheel.Hardware Pinwheel.Program GenericCertificate

section
set_option maxRecDepth 10000
set_option maxHeartbeats 24000000

private theorem endpoints_bounded_chunk_0 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨0 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨0 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨0 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨0 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_1 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨64 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨64 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨64 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨64 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_2 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨128 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨128 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨128 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨128 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_3 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨192 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨192 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨192 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨192 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_4 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨256 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨256 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨256 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨256 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_5 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨320 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨320 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨320 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨320 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_6 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨384 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨384 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨384 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨384 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_7 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨448 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨448 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨448 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨448 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_8 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨512 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨512 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨512 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨512 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_9 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨576 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨576 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨576 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨576 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_10 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨640 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨640 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨640 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨640 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_11 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨704 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨704 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨704 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨704 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_12 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨768 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨768 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨768 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨768 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_13 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨832 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨832 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨832 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨832 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_14 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨896 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨896 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨896 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨896 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

private theorem endpoints_bounded_chunk_15 : ∀ offset : Fin 64, (I2cLayout.coordinates (⟨960 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row.toNat ≤ 64 ∧ ((I2cLayout.coordinates (⟨960 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).row = 64 → (I2cLayout.coordinates (⟨960 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).outer = 0 ∧ (I2cLayout.coordinates (⟨960 + offset.val, by have h := offset.isLt; omega⟩ : Fin 1024)).inner = 0) := by decide +kernel

theorem endpoints : ∀ p : Program.Buffered.PC,
    (I2cLayout.coordinates p).row.toNat ≤ 64 ∧
      ((I2cLayout.coordinates p).row = 64 →
        (I2cLayout.coordinates p).outer = 0 ∧ (I2cLayout.coordinates p).inner = 0) := by
  intro index
  have index_bound := index.isLt
  by_cases range_0 : index.val < 64
  ·
    have chunk_offset : index.val - 0 < 64 := by omega
    have witness := endpoints_bounded_chunk_0 ⟨index.val - 0, chunk_offset⟩
    have same : (⟨0 + (index.val - 0), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 0 + (index.val - 0) = index.val; omega
    simpa only [same] using witness
  by_cases range_1 : index.val < 128
  ·
    have chunk_offset : index.val - 64 < 64 := by omega
    have witness := endpoints_bounded_chunk_1 ⟨index.val - 64, chunk_offset⟩
    have same : (⟨64 + (index.val - 64), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 64 + (index.val - 64) = index.val; omega
    simpa only [same] using witness
  by_cases range_2 : index.val < 192
  ·
    have chunk_offset : index.val - 128 < 64 := by omega
    have witness := endpoints_bounded_chunk_2 ⟨index.val - 128, chunk_offset⟩
    have same : (⟨128 + (index.val - 128), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 128 + (index.val - 128) = index.val; omega
    simpa only [same] using witness
  by_cases range_3 : index.val < 256
  ·
    have chunk_offset : index.val - 192 < 64 := by omega
    have witness := endpoints_bounded_chunk_3 ⟨index.val - 192, chunk_offset⟩
    have same : (⟨192 + (index.val - 192), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 192 + (index.val - 192) = index.val; omega
    simpa only [same] using witness
  by_cases range_4 : index.val < 320
  ·
    have chunk_offset : index.val - 256 < 64 := by omega
    have witness := endpoints_bounded_chunk_4 ⟨index.val - 256, chunk_offset⟩
    have same : (⟨256 + (index.val - 256), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 256 + (index.val - 256) = index.val; omega
    simpa only [same] using witness
  by_cases range_5 : index.val < 384
  ·
    have chunk_offset : index.val - 320 < 64 := by omega
    have witness := endpoints_bounded_chunk_5 ⟨index.val - 320, chunk_offset⟩
    have same : (⟨320 + (index.val - 320), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 320 + (index.val - 320) = index.val; omega
    simpa only [same] using witness
  by_cases range_6 : index.val < 448
  ·
    have chunk_offset : index.val - 384 < 64 := by omega
    have witness := endpoints_bounded_chunk_6 ⟨index.val - 384, chunk_offset⟩
    have same : (⟨384 + (index.val - 384), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 384 + (index.val - 384) = index.val; omega
    simpa only [same] using witness
  by_cases range_7 : index.val < 512
  ·
    have chunk_offset : index.val - 448 < 64 := by omega
    have witness := endpoints_bounded_chunk_7 ⟨index.val - 448, chunk_offset⟩
    have same : (⟨448 + (index.val - 448), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 448 + (index.val - 448) = index.val; omega
    simpa only [same] using witness
  by_cases range_8 : index.val < 576
  ·
    have chunk_offset : index.val - 512 < 64 := by omega
    have witness := endpoints_bounded_chunk_8 ⟨index.val - 512, chunk_offset⟩
    have same : (⟨512 + (index.val - 512), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 512 + (index.val - 512) = index.val; omega
    simpa only [same] using witness
  by_cases range_9 : index.val < 640
  ·
    have chunk_offset : index.val - 576 < 64 := by omega
    have witness := endpoints_bounded_chunk_9 ⟨index.val - 576, chunk_offset⟩
    have same : (⟨576 + (index.val - 576), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 576 + (index.val - 576) = index.val; omega
    simpa only [same] using witness
  by_cases range_10 : index.val < 704
  ·
    have chunk_offset : index.val - 640 < 64 := by omega
    have witness := endpoints_bounded_chunk_10 ⟨index.val - 640, chunk_offset⟩
    have same : (⟨640 + (index.val - 640), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 640 + (index.val - 640) = index.val; omega
    simpa only [same] using witness
  by_cases range_11 : index.val < 768
  ·
    have chunk_offset : index.val - 704 < 64 := by omega
    have witness := endpoints_bounded_chunk_11 ⟨index.val - 704, chunk_offset⟩
    have same : (⟨704 + (index.val - 704), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 704 + (index.val - 704) = index.val; omega
    simpa only [same] using witness
  by_cases range_12 : index.val < 832
  ·
    have chunk_offset : index.val - 768 < 64 := by omega
    have witness := endpoints_bounded_chunk_12 ⟨index.val - 768, chunk_offset⟩
    have same : (⟨768 + (index.val - 768), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 768 + (index.val - 768) = index.val; omega
    simpa only [same] using witness
  by_cases range_13 : index.val < 896
  ·
    have chunk_offset : index.val - 832 < 64 := by omega
    have witness := endpoints_bounded_chunk_13 ⟨index.val - 832, chunk_offset⟩
    have same : (⟨832 + (index.val - 832), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 832 + (index.val - 832) = index.val; omega
    simpa only [same] using witness
  by_cases range_14 : index.val < 960
  ·
    have chunk_offset : index.val - 896 < 64 := by omega
    have witness := endpoints_bounded_chunk_14 ⟨index.val - 896, chunk_offset⟩
    have same : (⟨896 + (index.val - 896), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 896 + (index.val - 896) = index.val; omega
    simpa only [same] using witness
  have chunk_offset : index.val - 960 < 64 := by omega
  have witness := endpoints_bounded_chunk_15 ⟨index.val - 960, chunk_offset⟩
  have same : (⟨960 + (index.val - 960), by omega⟩ : Fin 1024) = index := by apply Fin.ext; change 960 + (index.val - 960) = index.val; omega
  simpa only [same] using witness
end

section
set_option maxRecDepth 10000
set_option maxHeartbeats 40000000

private theorem validators_bounded_chunk_0 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨0 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_1 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨16 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_2 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨32 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_3 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨48 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_4 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨64 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_5 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨80 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_6 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨96 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_7 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨112 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_8 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨128 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_9 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨144 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_10 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨160 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_11 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨176 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_12 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨192 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_13 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨208 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_14 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨224 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_15 : ∀ offset : Fin 16, let p := I2cLayout.pc (⟨240 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

private theorem validators_bounded_chunk_16 : ∀ offset : Fin 14, let p := I2cLayout.pc (⟨256 + offset.val, by have h := offset.isLt; omega⟩ : Fin 270); let q := I2cLayout.coordinates p; let record := I2cSource.fullWords (q.row.setWidth 6); WordCanonical (record.extractLsb' 0 64) ∧ BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧ controlValid (record.extractLsb' 64 24) q = true ∧ nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  unfold WordCanonical BranchCanonical
  decide +kernel

theorem validators : ∀ v : Fin 270,
    let p := I2cLayout.pc v
    let q := I2cLayout.coordinates p
    let record := I2cSource.fullWords (q.row.setWidth 6)
    WordCanonical (record.extractLsb' 0 64) ∧
      BranchCanonical (record.extractLsb' 0 64) (record.extractLsb' 88 56) ∧
      controlValid (record.extractLsb' 64 24) q = true ∧
      nextNormalizes p (record.extractLsb' 0 64) (record.extractLsb' 88 56) = true := by
  intro index
  have index_bound := index.isLt
  by_cases range_0 : index.val < 16
  ·
    have chunk_offset : index.val - 0 < 16 := by omega
    have witness := validators_bounded_chunk_0 ⟨index.val - 0, chunk_offset⟩
    have same : (⟨0 + (index.val - 0), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 0 + (index.val - 0) = index.val; omega
    simpa only [same] using witness
  by_cases range_1 : index.val < 32
  ·
    have chunk_offset : index.val - 16 < 16 := by omega
    have witness := validators_bounded_chunk_1 ⟨index.val - 16, chunk_offset⟩
    have same : (⟨16 + (index.val - 16), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 16 + (index.val - 16) = index.val; omega
    simpa only [same] using witness
  by_cases range_2 : index.val < 48
  ·
    have chunk_offset : index.val - 32 < 16 := by omega
    have witness := validators_bounded_chunk_2 ⟨index.val - 32, chunk_offset⟩
    have same : (⟨32 + (index.val - 32), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 32 + (index.val - 32) = index.val; omega
    simpa only [same] using witness
  by_cases range_3 : index.val < 64
  ·
    have chunk_offset : index.val - 48 < 16 := by omega
    have witness := validators_bounded_chunk_3 ⟨index.val - 48, chunk_offset⟩
    have same : (⟨48 + (index.val - 48), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 48 + (index.val - 48) = index.val; omega
    simpa only [same] using witness
  by_cases range_4 : index.val < 80
  ·
    have chunk_offset : index.val - 64 < 16 := by omega
    have witness := validators_bounded_chunk_4 ⟨index.val - 64, chunk_offset⟩
    have same : (⟨64 + (index.val - 64), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 64 + (index.val - 64) = index.val; omega
    simpa only [same] using witness
  by_cases range_5 : index.val < 96
  ·
    have chunk_offset : index.val - 80 < 16 := by omega
    have witness := validators_bounded_chunk_5 ⟨index.val - 80, chunk_offset⟩
    have same : (⟨80 + (index.val - 80), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 80 + (index.val - 80) = index.val; omega
    simpa only [same] using witness
  by_cases range_6 : index.val < 112
  ·
    have chunk_offset : index.val - 96 < 16 := by omega
    have witness := validators_bounded_chunk_6 ⟨index.val - 96, chunk_offset⟩
    have same : (⟨96 + (index.val - 96), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 96 + (index.val - 96) = index.val; omega
    simpa only [same] using witness
  by_cases range_7 : index.val < 128
  ·
    have chunk_offset : index.val - 112 < 16 := by omega
    have witness := validators_bounded_chunk_7 ⟨index.val - 112, chunk_offset⟩
    have same : (⟨112 + (index.val - 112), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 112 + (index.val - 112) = index.val; omega
    simpa only [same] using witness
  by_cases range_8 : index.val < 144
  ·
    have chunk_offset : index.val - 128 < 16 := by omega
    have witness := validators_bounded_chunk_8 ⟨index.val - 128, chunk_offset⟩
    have same : (⟨128 + (index.val - 128), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 128 + (index.val - 128) = index.val; omega
    simpa only [same] using witness
  by_cases range_9 : index.val < 160
  ·
    have chunk_offset : index.val - 144 < 16 := by omega
    have witness := validators_bounded_chunk_9 ⟨index.val - 144, chunk_offset⟩
    have same : (⟨144 + (index.val - 144), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 144 + (index.val - 144) = index.val; omega
    simpa only [same] using witness
  by_cases range_10 : index.val < 176
  ·
    have chunk_offset : index.val - 160 < 16 := by omega
    have witness := validators_bounded_chunk_10 ⟨index.val - 160, chunk_offset⟩
    have same : (⟨160 + (index.val - 160), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 160 + (index.val - 160) = index.val; omega
    simpa only [same] using witness
  by_cases range_11 : index.val < 192
  ·
    have chunk_offset : index.val - 176 < 16 := by omega
    have witness := validators_bounded_chunk_11 ⟨index.val - 176, chunk_offset⟩
    have same : (⟨176 + (index.val - 176), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 176 + (index.val - 176) = index.val; omega
    simpa only [same] using witness
  by_cases range_12 : index.val < 208
  ·
    have chunk_offset : index.val - 192 < 16 := by omega
    have witness := validators_bounded_chunk_12 ⟨index.val - 192, chunk_offset⟩
    have same : (⟨192 + (index.val - 192), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 192 + (index.val - 192) = index.val; omega
    simpa only [same] using witness
  by_cases range_13 : index.val < 224
  ·
    have chunk_offset : index.val - 208 < 16 := by omega
    have witness := validators_bounded_chunk_13 ⟨index.val - 208, chunk_offset⟩
    have same : (⟨208 + (index.val - 208), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 208 + (index.val - 208) = index.val; omega
    simpa only [same] using witness
  by_cases range_14 : index.val < 240
  ·
    have chunk_offset : index.val - 224 < 16 := by omega
    have witness := validators_bounded_chunk_14 ⟨index.val - 224, chunk_offset⟩
    have same : (⟨224 + (index.val - 224), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 224 + (index.val - 224) = index.val; omega
    simpa only [same] using witness
  by_cases range_15 : index.val < 256
  ·
    have chunk_offset : index.val - 240 < 16 := by omega
    have witness := validators_bounded_chunk_15 ⟨index.val - 240, chunk_offset⟩
    have same : (⟨240 + (index.val - 240), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 240 + (index.val - 240) = index.val; omega
    simpa only [same] using witness
  have chunk_offset : index.val - 256 < 14 := by omega
  have witness := validators_bounded_chunk_16 ⟨index.val - 256, chunk_offset⟩
  have same : (⟨256 + (index.val - 256), by omega⟩ : Fin 270) = index := by apply Fin.ext; change 256 + (index.val - 256) = index.val; omega
  simpa only [same] using witness
end

theorem control_field (k : BitVec 6) :
    (I2cSource.fullWords k).extractLsb' 64 24 = I2cSource.control k := by
  simp only [I2cSource.fullWords]
  bv_decide

theorem source_record (p : Program.Buffered.PC) (within : p.val < I2cSource.source.code.span) :
    ∃ i, I2cSource.source.fetch p = some i ∧
      I2cSource.fullWords ((I2cLayout.coordinates p).row.setWidth 6) =
        GenericLayout.record I2cLayout.coordinates
          ((I2cSource.fullWords ((I2cLayout.coordinates p).row.setWidth 6)).extractLsb' 64 24) i := by
  have within270 : p.val < 270 := within
  cases fetch : I2cSource.source.fetch p with
  | none =>
    have cert := I2cLayout.records ⟨p.val, within270⟩
    simp only [show I2cLayout.pc ⟨p.val, within270⟩ = p from rfl, fetch, Option.map_none] at cert
    cases cert
  | some i =>
    refine ⟨i, rfl, ?_⟩
    simpa only [I2cLayout.row, control_field,
      BitVec.setWidth_eq_extractLsb' (by decide : 6 ≤ 7)] using
      I2cLayout.source_record p within270 i fetch
  done

theorem low_control_field (k : BitVec 6) :
    (I2cSource.fullWords k).extractLsb' 64 22 = (I2cSource.control k).extractLsb' 0 22 := by
  simp only [I2cSource.fullWords]
  bv_decide

def layout : Layout I2cSource.source where
  count := ⟨50, by decide⟩
  positive := by decide
  words := I2cSource.fullWords
  map := I2cLayout.coordinates
  initial := I2cLayout.initial_coordinates
  endpoints := endpoints
  rowBound := fun p within => I2cLayout.coordinate_bound p within
  sourceRecord := source_record
  canonical := fun p within => (validators ⟨p.val, within⟩).1
  branchCanonical := fun p within => (validators ⟨p.val, within⟩).2.1
  controlCanonical := fun p within => (validators ⟨p.val, within⟩).2.2.1
  normalizes := fun p within => (validators ⟨p.val, within⟩).2.2.2
  successor := by
    intro p within
    have small : p.val < 269 := by
      have bound : p.val + 1 < 270 := within
      omega
    simpa only [I2cLayout.row, low_control_field,
      BitVec.setWidth_eq_extractLsb' (by decide : 6 ≤ 7)] using
      I2cLayout.sequential_coordinates p small

end Pinwheel.Hardware.Buffered.I2cCertificate
