import Std

/-! Independent 8N1 waveform specification, in clock-cycle units. -/

namespace Pinwheel.UART

/-- A fixed bit duration of 1 through 256 cycles, encoded as duration minus one. -/
structure Config where
  durationMinusOne : Fin 256
  deriving DecidableEq, Repr

/-- Number of clock intervals occupied by each UART symbol. -/
def Config.cycles (cfg : Config) : Nat := cfg.durationMinusOne.val + 1

/-- Number of clock intervals in one complete 8N1 frame. -/
def Config.frameCycles (cfg : Config) : Nat := 10 * cfg.cycles

/-- The UART contract: start, eight data bits in wire order, and stop. -/
def frame (byte : BitVec 8) : Array Bool :=
  #[false, byte.getLsbD 0, byte.getLsbD 1, byte.getLsbD 2, byte.getLsbD 3,
    byte.getLsbD 4, byte.getLsbD 5, byte.getLsbD 6, byte.getLsbD 7, true]

/-- Pin level at an elapsed cycle after acceptance; high after the frame. -/
def expected (cfg : Config) (byte : BitVec 8) (cycle : Nat) : Bool :=
  (frame byte).getD (cycle / cfg.cycles) true

/-- An 8N1 frame has ten symbols, independently of the transmitted byte. -/
theorem frame_size (byte : BitVec 8) : (frame byte).size = 10 := by
  rfl

end Pinwheel.UART
