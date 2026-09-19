import Pinwheel.Compile.SPI
import Pinwheel.SPI.Latency

/-! The compiled SPI program behind an input pipeline. The compile theorems hold
for every input history, so the pin-level contract transfers by substitution. -/
namespace Pinwheel.Compile.SPI

/-- The engine program receives the peripheral's reply behind `d` input registers
whenever the clock half-period covers the latency plus the peripheral's output
delay. Its pin waveform is `waveform_correct` for every history. -/
theorem received_behind_pipeline (cfg : SPI.Config) (byte reply : BitVec 8) (pins : Nat → Bool)
    (tco d : Nat) (idle : Bool) (peripheral : Pinwheel.SPI.Mode0 cfg pins reply tco)
    (rate : d + tco ≤ cfg.halfCycles) (cycle : Nat) (done : cfg.transferCycles ≤ cycle) :
    Engine.samplesByte (execute cfg byte (Latency.delayed d idle pins) cycle).samples = reply := by
  rw [received_correct cfg byte _ cycle done]
  exact Pinwheel.SPI.expectedByte_delayed cfg pins reply (cfg.halfCycles - tco) d idle
    (peripheral.presents (by omega)) (by omega) (Nat.sub_le _ _)

end Pinwheel.Compile.SPI
