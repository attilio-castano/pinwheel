import Pinwheel.Hardware.Buffered.GenericUploadSource

namespace Pinwheel.Hardware.Buffered.GenericUpload.Serial
open Pinwheel.Hardware Pinwheel.Program Serial.Frames
variable {p : Program.Buffered.Program} {layout : GenericCertificate.Layout p}
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def tableWord (image : Image p layout) (sequence : BitVec 16) (k : BitVec 4) : BitVec 160 :=
  Serial.Encoding.encode .dictionary sequence (k ++ image.dictionary k)

def rowWord (image : Image p layout) (sequence : BitVec 16) (k : BitVec 6) : BitVec 160 :=
  Serial.Encoding.encode .row sequence
    (((k ++ image.branchIndex k) ++ image.control k) ++ image.word k)

def commitWord (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p) (sequence : BitVec 16) : BitVec 160 :=
  Serial.Encoding.encode .commit sequence (((p.idle.enabled ++ p.idle.levels) ++ BitVec.ofNat 11 p.code.span) ++ BitVec.ofNat 7 layout.count.val)

theorem table_fields (image : Image p layout) (sequence : BitVec 16) (k : BitVec 4) :
    (tableWord image sequence k).extractLsb' 144 3 = 6#3 ∧
    (tableWord image sequence k).extractLsb' 56 4 = k ∧
    (tableWord image sequence k).extractLsb' 0 56 = image.dictionary k := by
  unfold tableWord Serial.Encoding.encode
  simp (disch := decide) only [Serial.Encoding.Operation.code,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self]
  simp
  done

theorem table_operands (image : Image p layout) (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (sequence : BitVec 16) (k : BitVec 4) (closed : Closed (tableWord image sequence k) s.record)
    (cold : pin.cold = false) : Table image (s.coreInputs pin) k := by
  have opcode : Serial.requestOpcode s.record = 6 := by
    simpa [Serial.requestOpcode, closed.request, tableWord, Serial.Encoding.Operation.code] using
      Serial.Encoding.encode_opcode .dictionary sequence (k ++ image.dictionary k)
  have accepted : codeOf (tableWord image sequence k) = 0 :=
    Serial.Encoding.encode_accepted .dictionary sequence (k ++ image.dictionary k)
  constructor
  all_goals rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput, Serial.deliver, SerialPackage.State.inputs,
    SerialPackage.Pins.inputs, cold, closed.dispatch, closed.code, accepted, opcode,
    Serial.requestField_eq, closed.request]
  case address =>
    apply BitVec.eq_of_toNat_eq
    have address := congrArg BitVec.toNat (table_fields image sequence k).2.1
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at address
    simp only [BitVec.toNat_ofNat, address]
    change k.toNat % 64 = (0#2 ++ k).toNat
    rw [BitVec.toNat_append]
    have bound := k.isLt
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
    omega
    done
  case command => exact (table_fields image sequence k).1
  case branch => exact (table_fields image sequence k).2.2
  all_goals done

private theorem field_widen (word : BitVec n) (start narrow wide : Nat) :
    BitVec.ofNat wide (word.toNat / 2^start % 2^narrow) =
      (word.extractLsb' start narrow).setWidth wide := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  done

theorem row_fields (image : Image p layout) (sequence : BitVec 16) (k : BitVec 6) :
    (rowWord image sequence k).extractLsb' 144 3 = 1#3 ∧
    (rowWord image sequence k).extractLsb' 92 6 = k ∧
    (rowWord image sequence k).extractLsb' 0 64 = image.word k ∧
    (rowWord image sequence k).extractLsb' 64 24 = image.control k ∧
    (rowWord image sequence k).extractLsb' 88 4 = image.branchIndex k := by
  unfold rowWord Serial.Encoding.encode
  simp (disch := decide) only [Serial.Encoding.Operation.code,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self]
  simp
  done

theorem row_operands (image : Image p layout) (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (sequence : BitVec 16) (k : BitVec 6) (closed : Closed (rowWord image sequence k) s.record)
    (cold : pin.cold = false) : Row image (s.coreInputs pin) k := by
  have opcode : Serial.requestOpcode s.record = 1 := by
    simpa [Serial.requestOpcode, closed.request, rowWord, Serial.Encoding.Operation.code] using
      Serial.Encoding.encode_opcode .row sequence
        (((k ++ image.branchIndex k) ++ image.control k) ++ image.word k)
  have accepted : codeOf (rowWord image sequence k) = 0 :=
    Serial.Encoding.encode_accepted .row sequence
      (((k ++ image.branchIndex k) ++ image.control k) ++ image.word k)
  constructor
  all_goals rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput, Serial.deliver, SerialPackage.State.inputs,
    SerialPackage.Pins.inputs, cold, closed.dispatch, closed.code, accepted, opcode,
    Serial.requestField_eq, closed.request]
  case command => exact (row_fields image sequence k).1
  case address => exact (row_fields image sequence k).2.1
  case word => exact (row_fields image sequence k).2.2.1
  case control => exact (row_fields image sequence k).2.2.2.1
  case branch =>
    rw [show 309485009821345068724781056 = 2^88 from rfl, show 16 = 2^4 from rfl,
      field_widen, (row_fields image sequence k).2.2.2.2,
      BitVec.setWidth_eq_append (by decide : 4 ≤ 56)]
    rfl
  all_goals done

theorem commit_fields (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p) (sequence : BitVec 16) :
    (commitWord p layout sequence).extractLsb' 144 3 = 2#3 ∧
    (commitWord p layout sequence).extractLsb' 0 7 = BitVec.ofNat 7 layout.count.val ∧
    (commitWord p layout sequence).extractLsb' 7 11 = BitVec.ofNat 11 p.code.span ∧
    (commitWord p layout sequence).extractLsb' 18 3 = p.idle.levels ∧
    (commitWord p layout sequence).extractLsb' 21 3 = p.idle.enabled := by
  unfold commitWord Serial.Encoding.encode
  simp (disch := decide) only [Serial.Encoding.Operation.code,
    BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_setWidth_of_le, BitVec.extractLsb'_eq_self]
  simp
  done

theorem commit_operands (p : Program.Buffered.Program) (layout : GenericCertificate.Layout p) (s : SerialPackage.State) (pin : SerialPackage.Pins)
    (sequence : BitVec 16) (closed : Closed (commitWord p layout sequence) s.record)
    (cold : pin.cold = false) : Commit p layout (s.coreInputs pin) := by
  have opcode : Serial.requestOpcode s.record = 2 := by
    simpa [Serial.requestOpcode, closed.request, commitWord, Serial.Encoding.Operation.code] using
      Serial.Encoding.encode_opcode .commit sequence (((p.idle.enabled ++ p.idle.levels) ++ BitVec.ofNat 11 p.code.span) ++ BitVec.ofNat 7 layout.count.val)
  have accepted : codeOf (commitWord p layout sequence) = 0 :=
    Serial.Encoding.encode_accepted .commit sequence (((p.idle.enabled ++ p.idle.levels) ++ BitVec.ofNat 11 p.code.span) ++ BitVec.ofNat 7 layout.count.val)
  constructor
  all_goals rw [s.record_coreInputs]
  all_goals simp [Serial.State.coreInput, Serial.deliver, SerialPackage.State.inputs,
    SerialPackage.Pins.inputs, cold, closed.dispatch, closed.code, accepted, opcode,
    Serial.requestField_eq, closed.request]
  case command => exact (commit_fields p layout sequence).1
  case count => exact (commit_fields p layout sequence).2.1
  case span => exact (commit_fields p layout sequence).2.2.1
  case levels => exact (commit_fields p layout sequence).2.2.2.1
  case enabled => exact (commit_fields p layout sequence).2.2.2.2
  all_goals done

end Pinwheel.Hardware.Buffered.GenericUpload.Serial
