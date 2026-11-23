import Pinwheel.Hardware.Processor.AddressMap

open Pinwheel.Hardware.Processor

namespace ProcessorSystemFirmware

def layout : AddressMap.Layout 5 2 :=
  ⟨⟨0x10000,0x40000000,0x40000100,0x40000200⟩,by decide +kernel⟩

def iWord (imm rs1 funct rd opcode : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((imm%4096)*2^20+rs1*2^15+funct*2^12+rd*2^7+opcode)
def sWord (imm rs1 rs2 funct : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((imm/32)*2^25+rs2*2^20+rs1*2^15+funct*2^12+(imm%32)*2^7+0x23)

def program : Array (BitVec 32) := #[
  0x000100b7, iWord 128 0 0 2 0x13, sWord 1 1 2 0,
  iWord 1 1 0 3 0x03, iWord 1 1 4 4 0x03, iWord 4 1 2 0 0x03,
  0x400002b7, sWord 4 5 3 2, iWord 4 5 2 6 0x03,
  iWord 256 5 0 7 0x13, iWord 0 7 2 8 0x03, 0x0000000f,0x00100073]
def rom (address : BitVec 5) : BitVec 32 := program[address.toNat]?.getD 0

end ProcessorSystemFirmware
