import Pinwheel.Program.StreamingReadySegments
import Pinwheel.Program.StreamingI2CRead
import Pinwheel.I2C.RegisterReadPeer

namespace Pinwheel.Program.StreamingReadySegments

private def addressByte (request : I2C.RegisterRead.Request) (reading : Bool) : BitVec 8 :=
  BitVec.ofNat 8 (request.address.val * 2 + reading.toNat)

private def byteAndAck (byte : BitVec 8) (ack : Bool) : List Bool := StreamingI2CRead.byteBits byte ++ [ack]

private def splitAck (byte : BitVec 8) (samples : List Bool) : Option (Bool × List Bool) :=
  if samples.take 8 = StreamingI2CRead.byteBits byte then
    match samples.drop 8 with
    | bit :: tail => some (bit, tail)
    | [] => none
  else none

private theorem split_echo (byte : BitVec 8) (ack : Bool) (tail : List Bool) :
    splitAck byte (byteAndAck byte ack ++ tail) = some (ack, tail) := by
  have eight : (StreamingI2CRead.byteBits byte).length = 8 := StreamingI2CRead.byteBits_length _
  simp only [splitAck, byteAndAck, List.append_assoc, List.take_left' eight, List.drop_left' eight,
    if_true, List.singleton_append]
  done

private theorem split_last (byte : BitVec 8) (ack : Bool) :
    splitAck byte (byteAndAck byte ack) = some (ack, []) := by
  simpa using split_echo byte ack []
  done

private def endOnNack (tail : List Bool) (outcome : I2C.RegisterRead.Outcome) :
    Option I2C.RegisterRead.Outcome :=
  if tail.isEmpty then some outcome else none

/-- Recognize the exact successful or early-NACK receive prefix, including
    the echoed request and the controller's final released ACK slot. -/
def projectRegisterRead (request : I2C.RegisterRead.Request) (samples : List Bool) :
    Option I2C.RegisterRead.Outcome := do
  let (writeNack, rest) ← splitAck (addressByte request false) samples
  if writeNack then endOnNack rest .writeAddressNack else
    let (registerNack, rest) ← splitAck request.register rest
    if registerNack then endOnNack rest .registerNack else
      let (readNack, rest) ← splitAck (addressByte request true) rest
      if readNack then endOnNack rest .readAddressNack else
        if rest.length = 9 ∧ rest[8]? = some true then
          some (.success (StreamingI2CRead.decodeByte (rest.take 8)))
        else none

def expectedRegisterRead (request : I2C.RegisterRead.Request) (target : I2C.RegisterReadPeer.Target) :
    List Bool :=
  let writeNack := target.nack == some 0
  let registerNack := target.nack == some 1
  let readNack := target.nack == some 2
  byteAndAck (addressByte request false) writeNack ++
    if writeNack then [] else
      byteAndAck request.register registerNack ++
        if registerNack then [] else
          byteAndAck (addressByte request true) readNack ++
            if readNack then [] else byteAndAck target.payload true

private theorem byteAndAck_get (byte : BitVec 8) : (byteAndAck byte true)[8]? = some true := by
  unfold byteAndAck
  rw [List.getElem?_append_right (by simp), StreamingI2CRead.byteBits_length]
  rfl
  done

/-- The transport projection recognizes the same four outcomes as the
    independent I²C register-read specification. -/
theorem project_expected_registerRead (request : I2C.RegisterRead.Request)
    (target : I2C.RegisterReadPeer.Target) :
    projectRegisterRead request (expectedRegisterRead request target) = some target.outcome := by
  have takePayload : (byteAndAck target.payload true).take 8 = StreamingI2CRead.byteBits target.payload :=
    List.take_left' (StreamingI2CRead.byteBits_length _)
  have size : (byteAndAck target.payload true).length = 9 := by simp [byteAndAck]
  have getPayload : (byteAndAck target.payload true)[8]'(by omega) = true := by
    have value := byteAndAck_get target.payload
    rw [List.getElem?_eq_getElem (by omega)] at value
    exact Option.some.inj value
  rcases hn : target.nack with _ | stage
  · simp [projectRegisterRead, expectedRegisterRead, split_echo, hn, size, getPayload, takePayload,
      StreamingI2CRead.decode_byteBits, I2C.RegisterReadPeer.Target.outcome]
  · have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp [projectRegisterRead, expectedRegisterRead, split_echo, split_last, hn, endOnNack,
        I2C.RegisterReadPeer.Target.outcome]
  done

end Pinwheel.Program.StreamingReadySegments
