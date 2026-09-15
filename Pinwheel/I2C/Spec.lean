import Pinwheel.I2C.Bus

namespace Pinwheel.I2C

/-- One address byte (seven address bits then write=0), then one payload byte. -/
structure Request where
  address : Fin 128
  data : BitVec 8
  deriving DecidableEq, Repr

/-- Configured cycle minima, not a claim about an electrical I2C speed grade. -/
structure Config where
  phaseMinusOne : Fin 256
  waitMinusOne : Fin 256
  deriving DecidableEq, Repr

def Config.phaseCycles (cfg : Config) : Nat := cfg.phaseMinusOne.val + 1
def Config.waitCycles (cfg : Config) : Nat := cfg.waitMinusOne.val + 1

inductive Outcome where
  | success | addressNack | dataNack | timeout | busFault | resetAbort
  deriving DecidableEq, Repr

/-- Wire-order contract, expressed independently of controller bit selection. -/
def wireBits (r : Request) : Vector Bool 16 :=
  ⟨#[r.address.val.testBit 6, r.address.val.testBit 5, r.address.val.testBit 4,
    r.address.val.testBit 3, r.address.val.testBit 2, r.address.val.testBit 1,
    r.address.val.testBit 0, false,
    r.data[7], r.data[6], r.data[5], r.data[4], r.data[3], r.data[2], r.data[1], r.data[0]], rfl⟩

/-- Contract for a receiver: acknowledge each byte independently. -/
structure Reply where
  addressAck : Bool
  dataAck : Bool
  deriving DecidableEq, Repr

def Reply.outcome (reply : Reply) : Outcome :=
  if !reply.addressAck then .addressNack else if !reply.dataAck then .dataNack else .success

def Reply.clockCount (reply : Reply) : Nat := if reply.addressAck then 18 else 9

/-- ACK slots are the ninth clocks of address and payload. -/
def ackSlot (slot : Fin 18) : Bool := slot.val == 8 || slot.val == 17

end Pinwheel.I2C
