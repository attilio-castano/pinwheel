import Pinwheel.Hardware.Execution.Decode

namespace Pinwheel.Hardware.Execution

private theorem raw_parts (word : BitVec 64) : packRaw (unpack word) (word.extractLsb' 63 1) = word := by
  simp [packRaw, unpack]
  bv_normalize
  done

private theorem raw_unpack (f : Fields) (reserved : BitVec 1) : unpack (packRaw f reserved) = f := by
  cases f
  simp [unpack, packRaw]
  bv_normalize
  done

private theorem append_equal (a b : BitVec n) (c d : BitVec m) :
    a ++ c = b ++ d ↔ a = b ∧ c = d := by
  constructor
  · intro h
    exact ⟨by simpa only [BitVec.extractLsb'_append_eq_left] using congrArg (BitVec.extractLsb' m n) h,
      by simpa only [BitVec.extractLsb'_append_eq_right] using congrArg (BitVec.extractLsb' 0 m) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl
  done

private theorem append_zero (a : BitVec n) (b : BitVec m) :
    a ++ b = 0 ↔ a = 0 ∧ b = 0 := by
  have hz : (0 : BitVec n) ++ (0 : BitVec m) = (0 : BitVec (n + m)) := BitVec.zero_append_zero
  rw [← hz]
  exact append_equal a 0 b 0
  done

private theorem capture_canonical (bits : BitVec 6) :
    captureBits (getCapture bits) = if bits[0] then bits else 0 := by
  revert bits
  decide +kernel
  done

private theorem check_canonical (bits : BitVec 4) : checkBits (getCheck bits) = bits := by
  simp [checkBits, getCheck]
  bv_normalize
  done

private theorem wait_check (bits : BitVec 4) :
    ((0#2 ++ BitVec.ofBool bits[1] ++ bits.extractLsb' 0 1) = bits) ↔
      ((bits &&& 12#4) = 0#4) := by
  revert bits
  decide +kernel
  done

private theorem kinds (b : BitVec 3) : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by
  bv_omega
private theorem finishes (b : BitVec 2) : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by bv_omega
private theorem isSome_cond (b : Bool) (a : α) :
    (bif b then some a else none).isSome = b := by cases b <;> rfl

-- Decompose masks into record fields so Boolean reasoning needs no native bit-blaster.
private theorem clean_fields (f m : Fields) (r : BitVec 1) :
    clean (packRaw f r) (pack m) =
      (r == 0 && (f.no &&& ~~~m.no) == 0 && (f.yes &&& ~~~m.yes) == 0 &&
       (f.sample &&& ~~~m.sample) == 0 && (f.finish &&& ~~~m.finish) == 0 &&
       (f.terminal &&& ~~~m.terminal) == 0 && (f.entry &&& ~~~m.entry) == 0 &&
       (f.check &&& ~~~m.check) == 0 && (f.budget &&& ~~~m.budget) == 0 &&
       (f.duration &&& ~~~m.duration) == 0 && (f.enabled &&& ~~~m.enabled) == 0 &&
       (f.levels &&& ~~~m.levels) == 0 && (f.kind &&& ~~~m.kind) == 0) := by
  simp only [clean, pack, packRaw]
  repeat rw [BitVec.not_append]
  repeat rw [BitVec.and_append]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.and_eq_true]
  repeat rw [append_zero]
  bv_normalize
  done

private theorem masks :
    (0x7e001ffff#64) = pack ⟨7,7,7,255,0,0,63,0,0,0,0,0⟩ ∧
    (0x601ffff#64) = pack ⟨7,7,7,255,0,3,0,0,0,0,0,0⟩ ∧
    (0x7fffe01ffff#64) = pack ⟨7,7,7,255,0,15,63,63,3,0,0,0⟩ ∧
    (0x7f87fffe01ffff#64) = pack ⟨7,7,7,255,0,15,63,63,3,0,255,0⟩ ∧
    (0x7ffffffffe01ffff#64) = pack ⟨7,7,7,255,0,15,63,63,3,15,255,255⟩ ∧
    (0x1fffffff#64) = pack ⟨7,7,7,255,255,15,0,0,0,0,0,0⟩ := by
  decide +kernel
  done

set_option maxHeartbeats 2000000 in
private theorem valid_raw (f : Fields) (r : BitVec 1) :
    validValue (packRaw f r) = (decode (packRaw f r)).isSome := by
  rcases kinds f.kind with hk | hk | hk | hk | hk | hk | hk | hk
  all_goals rcases finishes f.finish with hf | hf | hf | hf
  all_goals simp_all [validValue, raw_unpack, decode, Fields.instruction,
    Fields.successor, encode, fields, finishFields, actionFields, Fields.action, Fields.pins,
    capture_canonical, check_canonical, isSome_cond, captureValid, -BitVec.toFin_extractLsb']
  all_goals try rw [masks.1]
  all_goals try rw [masks.2.1]
  all_goals try rw [masks.2.2.1]
  all_goals try rw [masks.2.2.2.1]
  all_goals try rw [masks.2.2.2.2.1]
  all_goals try rw [masks.2.2.2.2.2]
  all_goals try rw [clean_fields]
  all_goals try rw [show (4#64) = pack ⟨4,0,0,0,0,0,0,0,0,0,0,0⟩ from rfl]
  all_goals simp only [pack, packRaw]
  all_goals try apply Bool.eq_iff_iff.mpr
  all_goals try simp only [beq_iff_eq, Bool.and_eq_true]
  all_goals repeat rw [append_equal]
  all_goals try rw [wait_check]
  all_goals bv_normalize
  all_goals grind
  all_goals done

theorem valid_decode (word : BitVec 64) : validValue word = (decode word).isSome := by
  simpa only [raw_parts] using valid_raw (unpack word) (word.extractLsb' 63 1)
  done

private theorem capture_eval (bits : Expr I R 6) (inputs : Values I) (registers : Values R) :
    (captureLogic bits).eval inputs registers = BitVec.ofBool (captureValid (bits.eval inputs registers)) := by
  simp only [captureLogic, bor, Expr.eval, captureValid]
  generalize bits.eval inputs registers = b
  revert b
  decide +kernel
  done

/-- Every decoder output wire, including rejection, matches the functional record decoder. -/
theorem logic_correct (word : Expr I R 64) (inputs : Values I) (registers : Values R) (port : Port w) :
    (logic word port).eval inputs registers = value (word.eval inputs registers) port := by
  cases port <;> simp only [logic, value, fieldValue, unpack]
  all_goals try rfl
  simp only [validLogic, capture_eval, cleanLogic, Expr.eval]
  rcases kinds ((word.eval inputs registers).extractLsb' 0 3) with hk | hk | hk | hk | hk | hk | hk | hk
  all_goals rcases finishes ((word.eval inputs registers).extractLsb' 41 2) with hf | hf | hf | hf
  all_goals simp_all [validValue, unpack, clean]
  all_goals congr 1 <;> simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  done

end Pinwheel.Hardware.Execution
