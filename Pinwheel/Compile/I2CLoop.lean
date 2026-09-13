import Pinwheel.Engine.Counted
import Pinwheel.Compile.I2CProofs

namespace Pinwheel.Compile.I2CLoop
open Engine.Reactive.Counted

def chain (head : Template) (tail : List Template) : Code :=
  match tail with
  | [] => .emit head
  | next :: rest => .seq (.emit head) (chain next rest)

/-- The same stored pin expression selects both address and payload bits, MSB first. -/
def serialPins (clockLow : Bool) : PinExpr :=
  .serial (.openDrain (if clockLow then 1 else 0)) 1 true ⟨.loop 1, .loop 0, true, true⟩

def bitBody (cfg : Pinwheel.I2C.Config) : Code :=
  chain (.action (serialPins true) cfg.phaseMinusOne) [
    .wait (serialPins false) ⟨0, true⟩ cfg.waitMinusOne,
    .checked (serialPins false) cfg.phaseMinusOne I2C.clockHigh,
    .checked (serialPins true) cfg.phaseMinusOne I2C.unguarded]

/-- Outside the bit loop, depth zero selects the byte's ACK sample slot. -/
def ackBody (cfg : Pinwheel.I2C.Config) : Code :=
  chain (.action (.literal (.openDrain 1)) cfg.phaseMinusOne) [
    .wait (.literal {}) ⟨0, true⟩ cfg.waitMinusOne,
    .checked (.literal {}) cfg.phaseMinusOne I2C.clockHigh none (some ⟨1, .loop 0⟩),
    .checked (.literal (.openDrain 1)) cfg.phaseMinusOne I2C.unguarded none none
      (.select (.loop 0) 0 (.branch (.loop 0) (.absolute 74) .next) .sequential)]

def code (cfg : Pinwheel.I2C.Config) : Code :=
  .seq
    (chain (.qualify (.literal {}) I2C.bothHigh cfg.phaseMinusOne cfg.waitMinusOne)
      [.checked (.literal (.openDrain 2)) cfg.phaseMinusOne I2C.clockHigh])
    (.seq
      (.repeat 1 (.seq (.repeat 7 (bitBody cfg)) (ackBody cfg)))
      (chain (.action (.literal (.openDrain 3)) cfg.phaseMinusOne) [
        .wait (.literal (.openDrain 2)) ⟨0, true⟩ cfg.waitMinusOne,
        .checked (.literal (.openDrain 2)) cfg.phaseMinusOne I2C.clockHigh,
        .checked (.literal {}) cfg.phaseMinusOne I2C.bothHigh,
        .halt]))

def program (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request) : Program :=
  ⟨code cfg, #v[BitVec.ofNat 8 (r.address.val * 2), r.data], {}, by exact (show 79 ≤ 128 from by decide),
    by exact (show 31 ≤ 64 from by decide), by exact (show 2 ≤ 2 from by decide)⟩

/-- Logical addresses still span the full transaction, but only 15 instruction templates are stored. -/
theorem size (cfg : Pinwheel.I2C.Config) :
    (code cfg).span = 79 ∧ (code cfg).words = 15 ∧ (code cfg).loops = 2 ∧
      (code cfg).nodes = 31 ∧ (code cfg).nesting = 2 := by
  repeat constructor

end Pinwheel.Compile.I2CLoop
