import Pinwheel.Hardware.Processor.Examples.ByteProgram
import Pinwheel.Hardware.Processor.SystemModel

/-! RV32I firmware for the GPIO-wired Ready host. A cold-start request table
starts at ROM byte 256. Each byte encodes one request nibble, most significant
first. The RV32I reads each response and retains the low data word of the
collection receipt in x25. -/
namespace Pinwheel.Hardware.Processor.ReadySPI

open ProcessorSystemFirmware (iWord sWord)

def layout : AddressMap.Layout 8 2 :=
  ⟨⟨0x10000,0x40000000,0x40000100,0x40000200⟩, by decide +kernel⟩

private def branch (here target funct lhs rhs : Nat) : BitVec 32 :=
  let disp := ((4 * (target : Int) - 4 * here) % 8192).toNat
  BitVec.ofNat 32 (disp / 4096 * 2^31 + disp / 32 % 64 * 2^25 +
    rhs * 2^20 + lhs * 2^15 + funct * 2^12 + disp / 2 % 16 * 2^8 +
    disp / 2048 % 2 * 2^7 + 0x63)

private def addi (rd rs imm : Nat) := iWord imm rs 0 rd 0x13
private def send (rs : Nat) := sWord 4 1 rs 2

def program (frames collect : Nat) : Array (BitVec 32) := #[
  0x400000b7,           -- 0: x1 = GPIO base
  addi 2 0 256,         -- request nibble pointer
  addi 3 0 0,           -- completed frames
  addi 4 0 frames,
  addi 5 0 collect,
  addi 6 0 1,           -- selected, SCK low
  addi 7 0 3,           -- selected, SCK high
  addi 8 0 44,          -- 7: start request
  iWord 0 2 4 9 3,      -- 8: LBU request nibble
  iWord 2 9 1 9 0x13,   -- SLLI into GPIO bits 5:2
  addi 9 9 1, send 9,
  addi 9 9 2, send 9,
  addi 2 2 1, addi 8 8 4095,
  branch 16 8 1 8 0,
  send 0,
  iWord 0 1 2 9 3,      -- 18: poll READY
  iWord 16 9 7 9 0x13,
  branch 20 18 0 9 0,
  addi 8 0 52, addi 10 0 0, addi 11 0 28,
  send 6,               -- 24: select, low phase
  iWord 0 1 2 12 3,     -- 25: LW public MISO before SCK rises
  iWord 15 12 7 12 0x13,
  iWord 4 10 1 10 0x13, -- shift rolling response accumulator
  BitVec.ofNat 32 (12*2^20 + 10*2^15 + 6*2^12 + 10*2^7 + 0x33), -- OR
  send 7,
  addi 8 8 4095,
  branch 31 34 1 8 11,  -- after twenty-four nibbles, data[31:0] is complete
  branch 32 34 1 3 5,
  addi 25 10 0,
  branch 34 24 1 8 0,
  send 0, addi 3 3 1,
  branch 37 7 1 3 4,
  0x00100073]           -- intentional EBREAK

def rom (requests : Array (BitVec 8)) (frames collect : Nat) : SystemModel.Rom 8 :=
  fun address =>
    if address.toNat < 64 then (program frames collect)[address.toNat]?.getD 0
    else
      let start := 4 * (address.toNat - 64)
      let byte (k : Nat) := requests[start+k]?.getD 0
      byte 3 ++ byte 2 ++ byte 1 ++ byte 0

/-- Replacing the peripheral program and request data preserves the CPU's
instruction region when frame count and collection index stay fixed. -/
theorem same_code (requests other : Array (BitVec 8)) (frames collect : Nat)
    (addr : BitVec 8) (inCode : addr.toNat < 64) :
    rom requests frames collect addr = rom other frames collect addr := by simp [rom, inCode]

end Pinwheel.Hardware.Processor.ReadySPI
