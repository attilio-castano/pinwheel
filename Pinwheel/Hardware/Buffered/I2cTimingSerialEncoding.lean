import Pinwheel.Hardware.Buffered.I2cTimingSerialControl

namespace Pinwheel.Hardware.Buffered.I2cTiming.SerialUpload
open Pinwheel.Hardware Serial.Frames
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def rowWord (duration budget : Fin 256) (sequence : BitVec 16) (k : BitVec 6) : BitVec 160 :=
  Serial.Encoding.encode .row sequence
    (((k ++ I2cSource.branchIndex k) ++ I2cSource.control k) ++ I2cTiming.word duration budget k)

theorem row_fields (duration budget : Fin 256) (sequence : BitVec 16) (k : BitVec 6) :
    (rowWord duration budget sequence k).extractLsb' 144 3 = 1#3 ∧
    (rowWord duration budget sequence k).extractLsb' 92 6 = k ∧
    (rowWord duration budget sequence k).extractLsb' 0 64 = I2cTiming.word duration budget k ∧
    (rowWord duration budget sequence k).extractLsb' 64 24 = I2cSource.control k ∧
    (rowWord duration budget sequence k).extractLsb' 88 4 = I2cSource.branchIndex k := by
  unfold rowWord Serial.Encoding.encode
  simp (disch := decide) only [Serial.Encoding.Operation.code,
    BitVec.extractLsb'_append_eq_of_add_le,BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_setWidth_of_le,BitVec.extractLsb'_eq_self]
  simp

private theorem field_widen (word : BitVec n) (start narrow wide : Nat) :
    BitVec.ofNat wide (word.toNat / 2^start % 2^narrow) =
      (word.extractLsb' start narrow).setWidth wide := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat,BitVec.toNat_setWidth,BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]

theorem row_operands (duration budget : Fin 256) (s : SerialPackage.State)
    (pin : SerialPackage.Pins) (sequence : BitVec 16) (k : BitVec 6)
    (closed : Closed (rowWord duration budget sequence k) s.record) (cold : pin.cold = false) :
    Row duration budget (s.coreInputs pin) k := by
  have opcode : Serial.requestOpcode s.record = 1 := by
    simpa [Serial.requestOpcode,closed.request,rowWord,Serial.Encoding.Operation.code] using
      Serial.Encoding.encode_opcode .row sequence
        (((k ++ I2cSource.branchIndex k) ++ I2cSource.control k) ++ I2cTiming.word duration budget k)
  have accepted : codeOf (rowWord duration budget sequence k) = 0 :=
    Serial.Encoding.encode_accepted .row sequence
      (((k ++ I2cSource.branchIndex k) ++ I2cSource.control k) ++ I2cTiming.word duration budget k)
  constructor
  all_goals rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput,Serial.deliver,SerialPackage.State.inputs,
    SerialPackage.Pins.inputs,cold,closed.dispatch,closed.code,accepted,opcode,
    Serial.requestField_eq,closed.request]
  case command => exact (row_fields duration budget sequence k).1
  case address => exact (row_fields duration budget sequence k).2.1
  case word => exact (row_fields duration budget sequence k).2.2.1
  case control => exact (row_fields duration budget sequence k).2.2.2.1
  case branch =>
    rw [show 309485009821345068724781056 = 2^88 from rfl,show 16 = 2^4 from rfl,
      field_widen,(row_fields duration budget sequence k).2.2.2.2,
      BitVec.setWidth_eq_append (by decide : 4 ≤ 56)]
    rfl
  all_goals done

end Pinwheel.Hardware.Buffered.I2cTiming.SerialUpload
