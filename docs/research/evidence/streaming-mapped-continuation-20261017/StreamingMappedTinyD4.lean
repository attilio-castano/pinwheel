import Pinwheel.Hardware.StreamingMapped.TinyWiring
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Pinwheel.Artifact.StreamingMappedTinyD4
open Pinwheel.Hardware Pinwheel.Hardware.StreamingReady Pinwheel.Hardware.StreamingMapped
abbrev Pins := Pinwheel.Hardware.StreamingReady.TinyWiring.Pins
def netlistSHA256 : String := "b1ce35f0cfc3b47332f14edea002c8680fbedd1617ee31c41cff21be5a917eca"
def libertySHA256 : String := "34163f3e7de9f854afac57332ba06f1739b78e7ac35660a8a5ddd39c570124ad"
theorem one_bit (x : BitVec 1) : decide (x = 1) = x.getLsbD 0 := by decide +kernel +revert
theorem uo_out_bit0 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uo_out_bit1 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uo_out_bit2 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uo_out_bit3 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uo_out_bit4 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uo_out_bit5 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uo_out_bit6  : false = false := by decide +kernel +revert
theorem uo_out_bit7  : false = false := by decide +kernel +revert
def uo_out (pins : Pins) (engine : Values Package.Output) : BitVec 8 :=
  Word.pack (fun bit => match bit.val with
  | 0 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .miso).getLsbD 0))
  | 1 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .miso).getLsbD 1))
  | 2 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .miso).getLsbD 2))
  | 3 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .miso).getLsbD 3))
  | 4 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .ready).getLsbD 0))
  | 5 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .busy).getLsbD 0))
  | 6 => false
  | _ => false)
theorem uo_out_correct (pins : Pins) (engine : Values Package.Output) :
    uo_out pins engine = (if pins.ena &&& pins.rstN = 1 then (0 : BitVec 2) ++ (engine .busy ++ (engine .ready ++ engine .miso)) else 0) := by
  apply Word.from_bits
  intro i within
  rw [uo_out,Word.pack_bit _ i within]
  have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [uo_out_bit0 ((pins.ena).getLsbD 0) ((engine .miso).getLsbD 0) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uo_out_bit1 ((pins.ena).getLsbD 0) ((engine .miso).getLsbD 1) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uo_out_bit2 ((pins.ena).getLsbD 0) ((engine .miso).getLsbD 2) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uo_out_bit3 ((pins.ena).getLsbD 0) ((engine .miso).getLsbD 3) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uo_out_bit4 ((pins.ena).getLsbD 0) ((engine .ready).getLsbD 0) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uo_out_bit5 ((pins.ena).getLsbD 0) ((engine .busy).getLsbD 0) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uo_out_bit6 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uo_out_bit7 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
theorem uio_out_bit0 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uio_out_bit1 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uio_out_bit2 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uio_out_bit3  : false = false := by decide +kernel +revert
theorem uio_out_bit4  : false = false := by decide +kernel +revert
theorem uio_out_bit5  : false = false := by decide +kernel +revert
theorem uio_out_bit6  : false = false := by decide +kernel +revert
theorem uio_out_bit7  : false = false := by decide +kernel +revert
def uio_out (pins : Pins) (engine : Values Package.Output) : BitVec 8 :=
  Word.pack (fun bit => match bit.val with
  | 0 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .levels).getLsbD 0))
  | 1 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .levels).getLsbD 1))
  | 2 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .levels).getLsbD 2))
  | 3 => false
  | 4 => false
  | 5 => false
  | 6 => false
  | _ => false)
theorem uio_out_correct (pins : Pins) (engine : Values Package.Output) :
    uio_out pins engine = (if pins.ena &&& pins.rstN = 1 then (0 : BitVec 5) ++ engine .levels else 0) := by
  apply Word.from_bits
  intro i within
  rw [uio_out,Word.pack_bit _ i within]
  have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [uio_out_bit0 ((pins.ena).getLsbD 0) ((engine .levels).getLsbD 0) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_out_bit1 ((pins.ena).getLsbD 0) ((engine .levels).getLsbD 1) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_out_bit2 ((pins.ena).getLsbD 0) ((engine .levels).getLsbD 2) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_out_bit3 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_out_bit4 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_out_bit5 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_out_bit6 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_out_bit7 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
theorem uio_oe_bit0 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uio_oe_bit1 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uio_oe_bit2 (v0 : Bool) (v1 : Bool) (v2 : Bool) : (((v0) && (v2)) && (v1)) = (((v0) && (v2)) && (v1)) := by decide +kernel +revert
theorem uio_oe_bit3  : false = false := by decide +kernel +revert
theorem uio_oe_bit4  : false = false := by decide +kernel +revert
theorem uio_oe_bit5  : false = false := by decide +kernel +revert
theorem uio_oe_bit6  : false = false := by decide +kernel +revert
theorem uio_oe_bit7  : false = false := by decide +kernel +revert
def uio_oe (pins : Pins) (engine : Values Package.Output) : BitVec 8 :=
  Word.pack (fun bit => match bit.val with
  | 0 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .enabled).getLsbD 0))
  | 1 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .enabled).getLsbD 1))
  | 2 => ((((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0)) && ((engine .enabled).getLsbD 2))
  | 3 => false
  | 4 => false
  | 5 => false
  | 6 => false
  | _ => false)
theorem uio_oe_correct (pins : Pins) (engine : Values Package.Output) :
    uio_oe pins engine = (if pins.ena &&& pins.rstN = 1 then (0 : BitVec 5) ++ engine .enabled else 0) := by
  apply Word.from_bits
  intro i within
  rw [uio_oe,Word.pack_bit _ i within]
  have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [uio_oe_bit0 ((pins.ena).getLsbD 0) ((engine .enabled).getLsbD 0) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_oe_bit1 ((pins.ena).getLsbD 0) ((engine .enabled).getLsbD 1) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_oe_bit2 ((pins.ena).getLsbD 0) ((engine .enabled).getLsbD 2) ((pins.rstN).getLsbD 0)]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_oe_bit3 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_oe_bit4 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_oe_bit5 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_oe_bit6 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
  · rw [uio_oe_bit7 ]
    by_cases active : pins.ena &&& pins.rstN = 1
    · rw [if_pos active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = true :=
        activeBits.symm.trans (by simp only [active,decide_true])
      simp only [activeBool,Bool.true_and,BitVec.getLsbD_append]
      simp
    · rw [if_neg active]
      have activeBits := one_bit (pins.ena &&& pins.rstN)
      rw [BitVec.getLsbD_and] at activeBits
      have activeBool : (pins.ena.getLsbD 0 && pins.rstN.getLsbD 0) = false :=
        activeBits.symm.trans (by simp only [active,decide_false])
      simp only [activeBool,Bool.false_and,BitVec.getLsbD_zero]
      rfl
theorem engine_boundary_csn_bit0 (v0 : Bool) : (v0) = (v0) := by decide +kernel +revert
def engine_boundary_csn (pins : Pins) (engine : Values Package.Output) : BitVec 1 :=
  Word.pack (fun bit => match bit.val with

  | _ => ((pins.ui).getLsbD 0))
theorem engine_boundary_csn_correct (pins : Pins) (engine : Values Package.Output) :
    engine_boundary_csn pins engine = (pins.ui.extractLsb' 0 1) := by
  apply Word.from_bits
  intro i within
  rw [engine_boundary_csn,Word.pack_bit _ i within]
  have index : i = 0 := by omega
  subst i
  rw [engine_boundary_csn_bit0 ((pins.ui).getLsbD 0)]
  simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',BitVec.getLsbD_and,BitVec.getLsbD_not]
  simp
theorem engine_boundary_initialize_bit0 (v0 : Bool) (v1 : Bool) : (!((v0) && (v1))) = (!((v0) && (v1))) := by decide +kernel +revert
def engine_boundary_initialize (pins : Pins) (engine : Values Package.Output) : BitVec 1 :=
  Word.pack (fun bit => match bit.val with

  | _ => (!(((pins.ena).getLsbD 0) && ((pins.rstN).getLsbD 0))))
theorem engine_boundary_initialize_correct (pins : Pins) (engine : Values Package.Output) :
    engine_boundary_initialize pins engine = (~~~(pins.ena &&& pins.rstN)) := by
  apply Word.from_bits
  intro i within
  rw [engine_boundary_initialize,Word.pack_bit _ i within]
  have index : i = 0 := by omega
  subst i
  rw [engine_boundary_initialize_bit0 ((pins.ena).getLsbD 0) ((pins.rstN).getLsbD 0)]
  simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',BitVec.getLsbD_and,BitVec.getLsbD_not]
  simp
theorem engine_boundary_mosi_bit0 (v0 : Bool) : (v0) = (v0) := by decide +kernel +revert
theorem engine_boundary_mosi_bit1 (v0 : Bool) : (v0) = (v0) := by decide +kernel +revert
theorem engine_boundary_mosi_bit2 (v0 : Bool) : (v0) = (v0) := by decide +kernel +revert
theorem engine_boundary_mosi_bit3 (v0 : Bool) : (v0) = (v0) := by decide +kernel +revert
def engine_boundary_mosi (pins : Pins) (engine : Values Package.Output) : BitVec 4 :=
  Word.pack (fun bit => match bit.val with
  | 0 => ((pins.ui).getLsbD 2)
  | 1 => ((pins.ui).getLsbD 5)
  | 2 => ((pins.ui).getLsbD 6)
  | _ => ((pins.ui).getLsbD 7))
theorem engine_boundary_mosi_correct (pins : Pins) (engine : Values Package.Output) :
    engine_boundary_mosi pins engine = (pins.ui.extractLsb' 5 3 ++ pins.ui.extractLsb' 2 1) := by
  apply Word.from_bits
  intro i within
  rw [engine_boundary_mosi,Word.pack_bit _ i within]
  have indices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases indices with rfl | rfl | rfl | rfl
  · rw [engine_boundary_mosi_bit0 ((pins.ui).getLsbD 2)]
    simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',BitVec.getLsbD_and,BitVec.getLsbD_not]
    simp
  · rw [engine_boundary_mosi_bit1 ((pins.ui).getLsbD 5)]
    simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',BitVec.getLsbD_and,BitVec.getLsbD_not]
    simp
  · rw [engine_boundary_mosi_bit2 ((pins.ui).getLsbD 6)]
    simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',BitVec.getLsbD_and,BitVec.getLsbD_not]
    simp
  · rw [engine_boundary_mosi_bit3 ((pins.ui).getLsbD 7)]
    simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',BitVec.getLsbD_and,BitVec.getLsbD_not]
    simp
theorem engine_boundary_raw_inputs_bit0 (v0 : Bool) : (v0) = (v0) := by decide +kernel +revert
theorem engine_boundary_raw_inputs_bit1 (v0 : Bool) : (v0) = (v0) := by decide +kernel +revert
def engine_boundary_raw_inputs (pins : Pins) (engine : Values Package.Output) : BitVec 2 :=
  Word.pack (fun bit => match bit.val with
  | 0 => ((pins.ui).getLsbD 3)
  | _ => ((pins.ui).getLsbD 4))
theorem engine_boundary_raw_inputs_correct (pins : Pins) (engine : Values Package.Output) :
    engine_boundary_raw_inputs pins engine = (pins.ui.extractLsb' 3 2) := by
  apply Word.from_bits
  intro i within
  rw [engine_boundary_raw_inputs,Word.pack_bit _ i within]
  have indices : i = 0 ∨ i = 1 := by omega
  rcases indices with rfl | rfl
  · rw [engine_boundary_raw_inputs_bit0 ((pins.ui).getLsbD 3)]
    simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',BitVec.getLsbD_and,BitVec.getLsbD_not]
    simp
  · rw [engine_boundary_raw_inputs_bit1 ((pins.ui).getLsbD 4)]
    simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',BitVec.getLsbD_and,BitVec.getLsbD_not]
    simp
theorem engine_boundary_sck_bit0 (v0 : Bool) : (v0) = (v0) := by decide +kernel +revert
def engine_boundary_sck (pins : Pins) (engine : Values Package.Output) : BitVec 1 :=
  Word.pack (fun bit => match bit.val with

  | _ => ((pins.ui).getLsbD 1))
theorem engine_boundary_sck_correct (pins : Pins) (engine : Values Package.Output) :
    engine_boundary_sck pins engine = (pins.ui.extractLsb' 1 1) := by
  apply Word.from_bits
  intro i within
  rw [engine_boundary_sck,Word.pack_bit _ i within]
  have index : i = 0 := by omega
  subst i
  rw [engine_boundary_sck_bit0 ((pins.ui).getLsbD 1)]
  simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',BitVec.getLsbD_and,BitVec.getLsbD_not]
  simp
def actualEngine (pins : Pins) : Package.Pins :=
  ⟨engine_boundary_initialize pins (fun _ => 0),engine_boundary_csn pins (fun _ => 0),
   engine_boundary_sck pins (fun _ => 0),engine_boundary_mosi pins (fun _ => 0),
   engine_boundary_raw_inputs pins (fun _ => 0)⟩
def actualPads (pins : Pins) (engine : Values Package.Output) : Pinwheel.Hardware.StreamingReady.TinyWiring.Pad → BitVec 8
  | .uo => uo_out pins engine | .uio => uio_out pins engine | .oe => uio_oe pins engine
def actualTiny : Pinwheel.Hardware.StreamingMapped.TinyWiring.Backend := ⟨actualEngine,actualPads⟩
theorem tiny_correct : actualTiny.Correct 2 where
  enginePins := by
    intro pins
    simp only [actualTiny,actualEngine,engine_boundary_initialize_correct,engine_boundary_csn_correct,
      engine_boundary_sck_correct,engine_boundary_mosi_correct,engine_boundary_raw_inputs_correct]
    rfl
  pads := by
    intro pins engine pad
    cases pad <;> simp only [actualTiny,actualPads,uo_out_correct,uio_out_correct,uio_oe_correct] <;> rfl
end Pinwheel.Artifact.StreamingMappedTinyD4
