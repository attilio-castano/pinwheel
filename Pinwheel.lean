import Pinwheel.Hardware.Loader.Contract
import Std
import Pinwheel.Binary.Execution
import Pinwheel.Binary.Bytes
import Pinwheel.Binary.Storage
import Pinwheel.I2C.Proofs
import Pinwheel.Engine.Compatibility
import Pinwheel.Engine.ControlProofs
import Pinwheel.Compile.StretchedPulse
import Pinwheel.Compile.I2CReadProofs
import Pinwheel.Compile.I2CProofs
import Pinwheel.Compile.I2CLoopCorrectness
import Pinwheel.UART.Tx
import Pinwheel.SPI.Controller
import Pinwheel.Compile.UART
import Pinwheel.Compile.SPI
import Pinwheel.Hardware.RawProgram
import Pinwheel.Hardware.Countdown
import Pinwheel.Hardware.Emit
import Pinwheel.Hardware.Execution.Emit
import Pinwheel.Hardware.Reactive.Emit
import Pinwheel.Hardware.Refinement
import Pinwheel.Hardware.Protocols
import Pinwheel.Hardware.Storage
import Pinwheel.Hardware.Reactive.FetchChoice
import Pinwheel.Hardware.UARTRx

/-!
Pinwheel library entry point: protocol models, shared engine, compilers, and proofs.
The small setup example below is retained as a toolchain check.
-/

namespace Pinwheel.Setup

/-- Complement each bit of a byte, for setup validation. -/
def invertByte (byte : BitVec 8) : BitVec 8 := ~~~byte

/-- Complementing a byte twice restores its original value. -/
theorem invertByte_involutive (byte : BitVec 8) : invertByte (invertByte byte) = byte := by
  simp [invertByte]

end Pinwheel.Setup
