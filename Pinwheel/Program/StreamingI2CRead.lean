import Pinwheel.Engine.Reactive
import Pinwheel.I2C.Bus

/-! The external bit plan and open-drain peer for the standard 64-byte read.
The programmable core has no byte, address or acknowledgment operations. -/
namespace Pinwheel.Program.StreamingI2CRead

def addressBits : List Bool := [true, false, true, false, false, true, false, true]

/-- Within a byte, I²C sends the most significant bit first. -/
def byteBits (byte : BitVec 8) : List Bool :=
  List.ofFn fun i : Fin 8 => byte.getLsbD (7 - i.val)

def decodeByte (bits : List Bool) : BitVec 8 :=
  (BitVec.ofBoolListLE bits.reverse).setWidth 8

private def hostFrames : Nat → List Bool
  | 0 => []
  | n + 1 => List.replicate 8 true ++ [n == 0] ++ hostFrames n

/-- Address 0x52 with the read bit set, a released address ACK slot, then
64 released data bytes. The controller pulls low for all but the final ACK. -/
def hostBits : List Bool :=
  addressBits ++ [true] ++ hostFrames 64

private def peerFrames (payload : List (BitVec 8)) : List Bool :=
  payload.flatMap fun byte => byteBits byte ++ [true]

/-- The peer releases SDA during the address bits, acknowledges the address,
supplies the payload, and releases SDA during the controller's ACK slots. -/
def peerBits (payload : List (BitVec 8)) : List Bool :=
  List.replicate 8 true ++ [false] ++ peerFrames payload

def wireBits (payload : List (BitVec 8)) : List Bool :=
  List.zipWith (· && ·) hostBits (peerBits payload)

def hostBit (slot : Nat) : Bool := hostBits[slot]?.getD true

def peerBit (payload : List (BitVec 8)) (slot : Nat) : Bool :=
  (peerBits payload)[slot]?.getD true

def wireBit (payload : List (BitVec 8)) (slot : Nat) : Bool :=
  hostBit slot && peerBit payload slot

def drive (release : Bool) : I2C.Drive := if release then .release else .low

def controllerPins (pads : Engine.Reactive.Pins) : I2C.Pins :=
  ⟨drive (!pads.enabled.getLsbD 0),drive (!pads.enabled.getLsbD 1)⟩

def peerPins (payload : List (BitVec 8)) (slot : Nat) (stretchLow : Bool) : I2C.Pins :=
  ⟨drive (!stretchLow),drive (peerBit payload slot)⟩

def busRaw (bus : I2C.Bus) : BitVec 2 :=
  BitVec.ofBool bus.sda ++ BitVec.ofBool bus.scl

/-- In the digital board model raw input 0 is SCL and raw input 1 is SDA.
The controller must drive only LOW on enabled outputs. -/
def resolvedRaw (pads : Engine.Reactive.Pins) (peer : I2C.Pins) : BitVec 2 :=
  busRaw (I2C.resolve (controllerPins pads) peer)

private theorem resolve_drive (release : Bool) (peer : I2C.Drive) :
    I2C.resolveLine (drive release) peer = (release && peer == .release) := by
  cases release <;> cases peer <;> rfl

theorem resolvedRaw_scl (pads : Engine.Reactive.Pins) (peer : I2C.Pins) :
    (resolvedRaw pads peer).getLsbD 0 = (!pads.enabled.getLsbD 0 && peer.scl == .release) := by
  rw [resolvedRaw,busRaw,BitVec.getLsbD_append]
  simp [I2C.resolve,controllerPins,resolve_drive]

theorem resolvedRaw_sda (pads : Engine.Reactive.Pins) (peer : I2C.Pins) :
    (resolvedRaw pads peer).getLsbD 1 = (!pads.enabled.getLsbD 1 && peer.sda == .release) := by
  rw [resolvedRaw,busRaw,BitVec.getLsbD_append]
  simp [I2C.resolve,controllerPins,resolve_drive]

theorem resolvedRaw_peer_sda (pads : Engine.Reactive.Pins) (payload : List (BitVec 8))
    (slot : Nat) (stretchLow : Bool) (command : pads.enabled.getLsbD 1 = !hostBit slot) :
    (resolvedRaw pads (peerPins payload slot stretchLow)).getLsbD 1 = wireBit payload slot := by
  rw [resolvedRaw_sda,command]
  cases bit : peerBit payload slot <;> simp [peerPins,wireBit,bit,drive]

private def decodeFrames : Nat → List Bool → Option (List (BitVec 8))
  | 0, [] => some []
  | 0, _ => none
  | n + 1, bits =>
    if bits[8]? = some (n == 0) then
      (decodeFrames n (bits.drop 9)).map (decodeByte (bits.take 8) :: ·)
    else
      none

/-- Project the complete successful read, checking the address echo, the
target's ACK, the controller's ACK/NACK slots and the exact frame length. -/
def project (bits : List Bool) : Option (List (BitVec 8)) :=
  if bits.take 9 = addressBits ++ [false] then decodeFrames 64 (bits.drop 9) else none

@[simp] theorem byteBits_length (byte : BitVec 8) : (byteBits byte).length = 8 := by
  simp [byteBits]

theorem decode_byteBits (byte : BitVec 8) : decodeByte (byteBits byte) = byte := by
  decide +revert +kernel

private theorem hostFrames_length (n : Nat) : (hostFrames n).length = 9 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [hostFrames,ih,Nat.mul_succ]

theorem hostBits_length : hostBits.length = 585 := by
  simp [hostBits,hostFrames_length,addressBits]

private theorem peerFrames_length (payload : List (BitVec 8)) :
    (peerFrames payload).length = 9 * payload.length := by
  induction payload with
  | nil => rfl
  | cons byte rest ih =>
    change ((byteBits byte ++ [true]) ++ peerFrames rest).length = 9 * (rest.length+1)
    simp only [List.length_append,byteBits_length,List.length_singleton,ih,Nat.mul_succ]
    omega

theorem peerBits_length (payload : List (BitVec 8)) (size : payload.length = 64) :
    (peerBits payload).length = 585 := by
  simp [peerBits,peerFrames_length,size]

theorem wireBits_length (payload : List (BitVec 8)) (size : payload.length = 64) :
    (wireBits payload).length = 585 := by
  simp [wireBits,hostBits_length,peerBits_length payload size]

theorem wireBits_get (payload : List (BitVec 8)) (size : payload.length = 64)
    (slot : Nat) (within : slot < 585) : (wireBits payload)[slot]? = some (wireBit payload slot) := by
  have host := List.getElem?_eq_getElem (l := hostBits) (show slot < hostBits.length by
    rw [hostBits_length]
    exact within)
  have peer := List.getElem?_eq_getElem (l := peerBits payload) (show slot < (peerBits payload).length by
    rw [peerBits_length payload size]
    exact within)
  simp [wireBits,List.getElem?_zipWith,wireBit,hostBit,peerBit,host,peer]

private def wireFrames : List (BitVec 8) → List Bool
  | [] => []
  | byte :: rest => byteBits byte ++ [rest.isEmpty] ++ wireFrames rest

private theorem resolve_frames (payload : List (BitVec 8)) :
    List.zipWith (· && ·) (hostFrames payload.length) (peerFrames payload) = wireFrames payload := by
  induction payload with
  | nil => rfl
  | cons byte rest ih =>
    have zipByte : List.zipWith (· && ·) (List.replicate 8 true) (byteBits byte) = byteBits byte := by
      decide +revert +kernel
    have last : (rest.length == 0) = rest.isEmpty := by
      cases rest <;> rfl
    change List.zipWith (· && ·)
        ((List.replicate 8 true ++ [rest.length == 0]) ++ hostFrames rest.length)
        ((byteBits byte ++ [true]) ++ peerFrames rest) =
      (byteBits byte ++ [rest.isEmpty]) ++ wireFrames rest
    rw [List.zipWith_append (by simp),List.zipWith_append (by simp),zipByte,ih,last]
    simp

private theorem decode_frames (payload : List (BitVec 8)) :
    decodeFrames payload.length (wireFrames payload) = some payload := by
  induction payload with
  | nil => rfl
  | cons byte rest ih =>
    let frame := byteBits byte ++ [rest.isEmpty]
    let bits := frame ++ wireFrames rest
    have len : frame.length = 9 := by simp [frame]
    have ack : bits[8]? = some rest.isEmpty := by
      unfold bits frame
      rw [List.append_assoc,List.getElem?_append_right (by simp),byteBits_length]
      rfl
    have take : bits.take 8 = byteBits byte := by
      unfold bits frame
      rw [List.append_assoc,List.take_append_of_le_length (by simp)]
      exact List.take_of_length_le (by simp)
    have drop : bits.drop 9 = wireFrames rest := by
      rw [← len]
      exact List.drop_append_length
    have last : (rest.length == 0) = rest.isEmpty := by
      cases rest <;> rfl
    change decodeFrames (rest.length+1) bits = some (byte :: rest)
    simp [decodeFrames,ack,last,take,drop,decode_byteBits,ih]

theorem decode_wireBits (payload : List (BitVec 8)) (size : payload.length = 64) :
    project (wireBits payload) = some payload := by
  have wire : wireBits payload = (addressBits ++ [false]) ++ wireFrames payload := by
    have body := resolve_frames payload
    rw [size] at body
    change List.zipWith (· && ·) ((addressBits ++ [true]) ++ hostFrames 64)
      ((List.replicate 8 true ++ [false]) ++ peerFrames payload) = _
    rw [List.zipWith_append (by rfl),body]
    rfl
  rw [wire]
  change decodeFrames 64 (wireFrames payload) = some payload
  rw [← size]
  exact decode_frames payload

end Pinwheel.Program.StreamingI2CRead
