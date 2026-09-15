import Pinwheel.Hardware.Refinement
import Pinwheel.Compile.UART
import Pinwheel.Compile.SPI

namespace Pinwheel.Hardware.Core

/-- A committed encoded image, one start edge (cycle zero), then n further edges. -/
def execute (p : Engine.Program) (incoming : Nat → Bool) (n : Nat) : Engine.State :=
  view (run (tick {start := true, sample := incoming 0}
    (embed (Raw.encodeProgram p) (Engine.reset p))) incoming n)

theorem execute_correct (p : Engine.Program) (incoming : Nat → Bool) (n : Nat) :
    execute p incoming n = Engine.run p (Engine.start p (incoming 0)) incoming n := by
  unfold execute
  rw [start_encoded, run_encoded]
  rfl
  done

theorem uart_waveform (cfg : UART.Config) (byte : BitVec 8) (incoming : Nat → Bool) (n : Nat) :
    (execute (Compile.UART.program cfg byte) incoming n).levels =
      Compile.UART.encodePin (UART.expected cfg byte n) := by
  simpa only [execute_correct, Compile.UART.execute] using Compile.UART.waveform_correct cfg byte incoming n

theorem spi_waveform (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Bool) (n : Nat) :
    (execute (Compile.SPI.program cfg byte) incoming n).levels =
      Compile.SPI.encodePins (SPI.expectedPins cfg byte n) := by
  simpa only [execute_correct, Compile.SPI.execute] using Compile.SPI.waveform_correct cfg byte incoming n

theorem spi_received (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Bool) (n : Nat)
    (h : cfg.transferCycles ≤ n) :
    Engine.samplesByte (execute (Compile.SPI.program cfg byte) incoming n).samples =
      SPI.expectedByte cfg incoming := by
  simpa only [execute_correct, Compile.SPI.execute] using Compile.SPI.received_correct cfg byte incoming n h

end Pinwheel.Hardware.Core
