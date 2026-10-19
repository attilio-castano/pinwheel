import Pinwheel.Hardware.Buffered.SerialUploadControl

namespace Pinwheel.Hardware.Buffered.SerialUpload
open Pinwheel.Hardware Serial.Frames
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def tableWord (sequence : BitVec 16) (k : BitVec 4) : BitVec 160 :=
  Serial.Encoding.encode .dictionary sequence (k ++ I2cSource.dictionary k)

def rowWord (sequence : BitVec 16) (k : BitVec 6) : BitVec 160 :=
  Serial.Encoding.encode .row sequence
    (((k ++ I2cSource.branchIndex k) ++ I2cSource.control k) ++ I2cSource.word k)

def commitWord (sequence : BitVec 16) : BitVec 160 :=
  Serial.Encoding.encode .commit sequence ((0#6 ++ 270#11) ++ 50#7)

theorem table_fields (sequence : BitVec 16) (k : BitVec 4) :
    (tableWord sequence k).extractLsb' 144 3 = 6#3 ∧
    (tableWord sequence k).extractLsb' 56 4 = k ∧
    (tableWord sequence k).extractLsb' 0 56 = I2cSource.dictionary k := by
  unfold tableWord Serial.Encoding.encode
  simp (disch := decide) only [Serial.Encoding.Operation.code,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self]
  simp
  done

theorem table_operands (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (sequence : BitVec 16) (k : BitVec 4) (closed : Closed (tableWord sequence k) s.record)
    (cold : pin.cold = false) : Table (s.coreInputs pin) k := by
  have opcode : Serial.requestOpcode s.record = 6 := by
    simpa [Serial.requestOpcode, closed.request, tableWord, Serial.Encoding.Operation.code] using
      Serial.Encoding.encode_opcode .dictionary sequence (k ++ I2cSource.dictionary k)
  have accepted : codeOf (tableWord sequence k) = 0 :=
    Serial.Encoding.encode_accepted .dictionary sequence (k ++ I2cSource.dictionary k)
  constructor
  all_goals rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput, Serial.deliver, SerialPackage.State.inputs,
    SerialPackage.Pins.inputs, cold, closed.dispatch, closed.code, accepted, opcode,
    Serial.requestField_eq, closed.request]
  case address =>
    apply BitVec.eq_of_toNat_eq
    have address := congrArg BitVec.toNat (table_fields sequence k).2.1
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at address
    simp only [BitVec.toNat_ofNat, address]
    change k.toNat % 64 = (0#2 ++ k).toNat
    rw [BitVec.toNat_append]
    have bound := k.isLt
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
    omega
    done
  case command => exact (table_fields sequence k).1
  case branch => exact (table_fields sequence k).2.2
  all_goals done

private theorem field_widen (word : BitVec n) (start narrow wide : Nat) :
    BitVec.ofNat wide (word.toNat / 2^start % 2^narrow) =
      (word.extractLsb' start narrow).setWidth wide := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  done

theorem row_fields (sequence : BitVec 16) (k : BitVec 6) :
    (rowWord sequence k).extractLsb' 144 3 = 1#3 ∧
    (rowWord sequence k).extractLsb' 92 6 = k ∧
    (rowWord sequence k).extractLsb' 0 64 = I2cSource.word k ∧
    (rowWord sequence k).extractLsb' 64 24 = I2cSource.control k ∧
    (rowWord sequence k).extractLsb' 88 4 = I2cSource.branchIndex k := by
  unfold rowWord Serial.Encoding.encode
  simp (disch := decide) only [Serial.Encoding.Operation.code,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self]
  simp
  done

theorem row_operands (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (sequence : BitVec 16) (k : BitVec 6) (closed : Closed (rowWord sequence k) s.record)
    (cold : pin.cold = false) : Row (s.coreInputs pin) k := by
  have opcode : Serial.requestOpcode s.record = 1 := by
    simpa [Serial.requestOpcode, closed.request, rowWord, Serial.Encoding.Operation.code] using
      Serial.Encoding.encode_opcode .row sequence
        (((k ++ I2cSource.branchIndex k) ++ I2cSource.control k) ++ I2cSource.word k)
  have accepted : codeOf (rowWord sequence k) = 0 :=
    Serial.Encoding.encode_accepted .row sequence
      (((k ++ I2cSource.branchIndex k) ++ I2cSource.control k) ++ I2cSource.word k)
  constructor
  all_goals rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput, Serial.deliver, SerialPackage.State.inputs,
    SerialPackage.Pins.inputs, cold, closed.dispatch, closed.code, accepted, opcode,
    Serial.requestField_eq, closed.request]
  case command => exact (row_fields sequence k).1
  case address => exact (row_fields sequence k).2.1
  case word => exact (row_fields sequence k).2.2.1
  case control => exact (row_fields sequence k).2.2.2.1
  case branch =>
    rw [show 309485009821345068724781056 = 2^88 from rfl, show 16 = 2^4 from rfl,
      field_widen, (row_fields sequence k).2.2.2.2,
      BitVec.setWidth_eq_append (by decide : 4 ≤ 56)]
    rfl
  all_goals done

theorem commit_fields (sequence : BitVec 16) :
    (commitWord sequence).extractLsb' 144 3 = 2#3 ∧
    (commitWord sequence).extractLsb' 0 7 = 50#7 ∧
    (commitWord sequence).extractLsb' 7 11 = 270#11 ∧
    (commitWord sequence).extractLsb' 18 3 = 0#3 ∧
    (commitWord sequence).extractLsb' 21 3 = 0#3 := by
  unfold commitWord Serial.Encoding.encode
  simp (disch := decide) only [Serial.Encoding.Operation.code,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self]
  decide +kernel
  done

theorem commit_operands (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (sequence : BitVec 16) (closed : Closed (commitWord sequence) s.record)
    (cold : pin.cold = false) : Commit (s.coreInputs pin) := by
  have opcode : Serial.requestOpcode s.record = 2 := by
    simpa [Serial.requestOpcode, closed.request, commitWord, Serial.Encoding.Operation.code] using
      Serial.Encoding.encode_opcode .commit sequence ((0#6 ++ 270#11) ++ 50#7)
  have accepted : codeOf (commitWord sequence) = 0 :=
    Serial.Encoding.encode_accepted .commit sequence ((0#6 ++ 270#11) ++ 50#7)
  constructor
  all_goals rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput, Serial.deliver, SerialPackage.State.inputs,
    SerialPackage.Pins.inputs, cold, closed.dispatch, closed.code, accepted, opcode,
    Serial.requestField_eq, closed.request]
  case command => exact (commit_fields sequence).1
  case count => exact (commit_fields sequence).2.1
  case span => exact (commit_fields sequence).2.2.1
  case levels => exact (commit_fields sequence).2.2.2.1
  case enabled => exact (commit_fields sequence).2.2.2.2
  all_goals done

end Pinwheel.Hardware.Buffered.SerialUpload
