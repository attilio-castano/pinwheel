import Std

/-!
Minimal package validation using bundled Lean libraries.
This example checks the toolchain; it does not model a protocol or circuit.
-/

namespace Pinwheel.Setup

/-- Complement each bit of a byte, for setup validation. -/
def invertByte (byte : BitVec 8) : BitVec 8 := ~~~byte

/-- Complementing a byte twice restores its original value. -/
theorem invertByte_involutive (byte : BitVec 8) : invertByte (invertByte byte) = byte := by
  simp [invertByte]

end Pinwheel.Setup
