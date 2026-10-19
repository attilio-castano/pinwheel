import Pinwheel.Hardware.Buffered.SerialCorrespondenceFrames

/-! Canonical request encodings for all eight supported serial operations.
The reserved payload bits are zero by construction, and parser acceptance is a
proved consequence of the encoded wire word, rather than an admission premise. -/
namespace Pinwheel.Hardware.Buffered.Serial.Encoding
open Pinwheel.Hardware

inductive Operation where
  | observe | row | commit | start | release | dictionary | warm | cold
  deriving DecidableEq, Repr

def Operation.code : Operation → BitVec 4
  | .observe => 0 | .row => 1 | .commit => 2 | .start => 3
  | .release => 4 | .dictionary => 6 | .warm => 7 | .cold => 8

def Operation.width : Operation → Nat
  | .observe => 5 | .row => 98 | .commit => 24 | .start => 60
  | .release => 32 | .dictionary => 60 | .warm | .cold => 0

def encode (operation : Operation) (sequence : BitVec 16)
    (payload : BitVec operation.width) : BitVec 160 :=
  ((0xA71 : BitVec 12) ++ operation.code) ++ (sequence ++ payload.setWidth 128)

private theorem append_toNat_add (a : BitVec m) (b : BitVec n) :
    (a ++ b).toNat = a.toNat * 2^n + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  done

theorem payload_bound (operation : Operation) (payload : BitVec operation.width) :
    payload.toNat < 2^128 := by
  cases operation <;> have h := payload.isLt <;> simp only [Operation.width] at * <;> omega
  done

theorem encode_toNat (operation : Operation) (sequence : BitVec 16)
    (payload : BitVec operation.width) :
    (encode operation sequence payload).toNat =
      (0xA710 + operation.code.toNat)*2^144 + sequence.toNat*2^128 + payload.toNat := by
  unfold encode
  repeat rw [append_toNat_add]
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (payload_bound operation payload)]
  change (2673*2^4 + operation.code.toNat)*2^144 +
    (sequence.toNat*2^128 + payload.toNat) = _
  omega
  done

theorem encode_header (operation : Operation) (sequence : BitVec 16)
    (payload : BitVec operation.width) :
    (encode operation sequence payload).toNat / 2^148 = 0xA71 := by
  rw [encode_toNat]
  have hc := operation.code.isLt
  have hs := sequence.isLt
  have hp := payload_bound operation payload
  omega
  done

theorem encode_opcode (operation : Operation) (sequence : BitVec 16)
    (payload : BitVec operation.width) :
    (encode operation sequence payload).toNat / 2^144 % 16 = operation.code.toNat := by
  rw [encode_toNat]
  have hc := operation.code.isLt
  have hs := sequence.isLt
  have hp := payload_bound operation payload
  omega
  done

theorem encode_payload (operation : Operation) (sequence : BitVec 16)
    (payload : BitVec operation.width) :
    (encode operation sequence payload).toNat % 2^128 = payload.toNat := by
  rw [encode_toNat]
  have hc := operation.code.isLt
  have hs := sequence.isLt
  have hp := payload_bound operation payload
  omega
  done

theorem encode_accepted (operation : Operation) (sequence : BitVec 16)
    (payload : BitVec operation.width) : Frames.codeOf (encode operation sequence payload) = 0 := by
  simp only [Frames.codeOf, requestCode, requestOpcode]
  rw [encode_header, encode_opcode, encode_payload]
  cases operation <;> have hp := payload.isLt <;> simp [Operation.code, Operation.width] at *
  all_goals exact hp
  done

theorem encode_fields (operation : Operation) (sequence : BitVec 16)
    (payload : BitVec operation.width) :
    (encode operation sequence payload).extractLsb' 148 12 = 0xA71 ∧
    (encode operation sequence payload).extractLsb' 144 4 = operation.code ∧
    (encode operation sequence payload).extractLsb' 128 16 = sequence ∧
    (encode operation sequence payload).extractLsb' 0 128 = payload.setWidth 128 := by
  unfold encode
  bv_decide
  done

end Pinwheel.Hardware.Buffered.Serial.Encoding
