import Pinwheel.Hardware.Execution.Record

namespace Pinwheel.Hardware.Execution
open Engine.Reactive

theorem unpack_pack (f : Fields) : unpack (pack f) = f := by
  cases f
  simp [unpack, pack, packRaw]
  bv_normalize
  done

private theorem capture_parts (d : BitVec 4) (i : BitVec 1) :
    (d ++ i ++ (1#1))[0] = true ∧ (d ++ i ++ (1#1)).extractLsb' 1 1 = i ∧
      (d ++ i ++ (1#1)).extractLsb' 2 4 = d := by
  bv_normalize
  done

theorem capture_roundtrip (c : Option (Capture 15)) : getCapture (captureBits c) = c := by
  cases c <;> simp only [captureBits, getCapture, capture_parts, BitVec.toFin_ofFin, ite_true]
  rfl
  done

theorem check_roundtrip (c : Check) : getCheck (checkBits c) = c := by
  cases c
  simp only [getCheck, checkBits, Check.mk.injEq]
  exact ⟨BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left⟩
  done

private theorem condition_parts (i : BitVec 1) (b : Bool) :
    ((0#2) ++ BitVec.ofBool b ++ i).extractLsb' 0 1 = i ∧
      ((0#2) ++ BitVec.ofBool b ++ i)[1] = b := by
  bv_normalize
  done

theorem fields_roundtrip (i : Operation) : (fields i).instruction = some i := by
  cases i with
  | checked a =>
    cases a with
    | mk action guard terminal finish =>
      cases finish <;> simp [fields, finishFields, Fields.instruction, Fields.successor, actionFields,
        Fields.action, Fields.pins, capture_roundtrip, check_roundtrip]
  | _ => simp [fields, Fields.instruction, actionFields, Fields.action, Fields.pins,
      capture_roundtrip, check_roundtrip, condition_parts]
  done

theorem decode_encode (i : Operation) : decode (encode i) = some i := by
  simp [decode, encode, unpack_pack, fields_roundtrip]
  done

theorem accepted_canonical (word : BitVec 64) (i : Operation) (h : decode word = some i) : encode i = word := by
  cases hc : (unpack word).instruction <;> simp_all [decode]
  grind
  done

end Pinwheel.Hardware.Execution
