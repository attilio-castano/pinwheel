import Pinwheel.Binary.ImageProofs

namespace Pinwheel.Binary

def toBytes (bytes : List Byte) : ByteArray :=
  ⟨bytes.toArray.map (fun b => UInt8.ofBitVec (BitVec.ofFin b))⟩

def fromBytes (bytes : ByteArray) : List Byte :=
  bytes.data.toList.map (fun b => b.toBitVec.toFin)

def encodeBytes (image : Image) : ByteArray := toBytes (encode image)
def decodeBytes (bytes : ByteArray) : Option Image := decode (fromBytes bytes)

theorem from_to_bytes (bytes : List Byte) : fromBytes (toBytes bytes) = bytes := by
  simp [fromBytes, toBytes, List.map_map, Function.comp_def]
  done

theorem to_from_bytes (bytes : ByteArray) : toBytes (fromBytes bytes) = bytes := by
  cases bytes <;> simp [fromBytes, toBytes, List.map_map, Function.comp_def]
  done

theorem decode_encode_bytes (image : Image) : decodeBytes (encodeBytes image) = some image := by
  simp [decodeBytes, encodeBytes, from_to_bytes, decode_encode]
  done

end Pinwheel.Binary
