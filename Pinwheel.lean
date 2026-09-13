import Std
import Pinwheel.UART.Tx

/-!
Pinwheel library entry point, including the pure Lean UART specification and transmitter.
The small setup example below is retained as a toolchain check.
-/

namespace Pinwheel.Setup

/-- Complement each bit of a byte, for setup validation. -/
def invertByte (byte : BitVec 8) : BitVec 8 := ~~~byte

/-- Complementing a byte twice restores its original value. -/
theorem invertByte_involutive (byte : BitVec 8) : invertByte (invertByte byte) = byte := by
  simp [invertByte]

end Pinwheel.Setup
