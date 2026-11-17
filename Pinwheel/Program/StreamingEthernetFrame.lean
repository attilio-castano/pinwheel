import Std

/-! A minimum Ethernet frame for the serial-interface transmit proof. The
host computes FCS and sends the preamble before the 64 MAC-frame octets. -/
namespace Pinwheel.Program.StreamingEthernetFrame

set_option maxRecDepth 12000

def serialBits (octets : List (BitVec 8)) : List Bool :=
  octets.flatMap fun octet => List.ofFn fun k : Fin 8 => octet.getLsbD k.val

/-- The reflected Ethernet CRC shift register. The host sends its complement
with the least significant octet first. -/
def crc32 (octets : List (BitVec 8)) : BitVec 32 :=
  ~~~((serialBits octets).foldl (fun crc bit =>
    let shifted := crc >>> 1
    if bit != crc.getLsbD 0 then shifted ^^^ 0xedb88320 else shifted) 0xffffffff)

def body : List (BitVec 8) :=
  [2,0,0,0,0,1, 2,0,0,0,0,2, 0x88,0xb5] ++ (List.range 46).map (BitVec.ofNat 8)

def fcs : List (BitVec 8) :=
  List.ofFn fun k : Fin 4 => (crc32 body).extractLsb' (8 * k.val) 8

def frameBytes : List (BitVec 8) := List.replicate 7 0x55 ++ [0xd5] ++ body ++ fcs

def frameBits : List Bool := serialBits frameBytes

/-- The quad host sends chronological TX bits starting at bit 63 of each word. -/
def frameWords : List (BitVec 64) :=
  (List.range 9).map fun k => ((frameBits.drop (64 * k)).take 64).foldl
    (fun word bit => (word <<< 1) ||| BitVec.ofNat 64 bit.toNat) 0

theorem frame_bits_count : frameBits.length = 576 := by decide +kernel

theorem fixture_fcs : fcs = [0xc6,0xe8,0x12,0x98] := by decide +kernel

/-- The exact TX words used in the serial PHY replay. -/
theorem fixture_words : frameWords =
    [0xaaaaaaaaaaaaaaab, 0x4000000000804000, 0x0000004011ad0080, 0x40c020a060e01090,
     0x50d030b070f00888, 0x48c828a868e81898, 0x58d838b878f80484, 0x44c424a464e41494,
     0x54d434b463174819] := by
  decide +kernel

end Pinwheel.Program.StreamingEthernetFrame
