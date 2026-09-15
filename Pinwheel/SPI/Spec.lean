import Std

/-! Independent mode-0, MSB-first, eight-bit SPI contract in system-clock cycles. -/

namespace Pinwheel.SPI

/-- Half-clock duration of 1 through 256 system cycles, encoded minus one. -/
structure Config where
  halfMinusOne : Fin 256
  deriving DecidableEq, Repr

def Config.halfCycles (cfg : Config) : Nat := cfg.halfMinusOne.val + 1

/-- Sixteen clock half-periods followed by one half-period of chip-select hold. -/
def Config.transferCycles (cfg : Config) : Nat := 17 * cfg.halfCycles

/-- Controller-driven pins; chip select is active-low. -/
structure Pins where
  csN : Bool
  sclk : Bool
  mosi : Bool
  deriving DecidableEq, Repr

/-- The specified output pattern, with each entry held for one half-period. -/
def wireFrame (byte : BitVec 8) : Array Pins :=
  #[⟨false, false, byte.getLsbD 7⟩, ⟨false, true, byte.getLsbD 7⟩,
    ⟨false, false, byte.getLsbD 6⟩, ⟨false, true, byte.getLsbD 6⟩,
    ⟨false, false, byte.getLsbD 5⟩, ⟨false, true, byte.getLsbD 5⟩,
    ⟨false, false, byte.getLsbD 4⟩, ⟨false, true, byte.getLsbD 4⟩,
    ⟨false, false, byte.getLsbD 3⟩, ⟨false, true, byte.getLsbD 3⟩,
    ⟨false, false, byte.getLsbD 2⟩, ⟨false, true, byte.getLsbD 2⟩,
    ⟨false, false, byte.getLsbD 1⟩, ⟨false, true, byte.getLsbD 1⟩,
    ⟨false, false, byte.getLsbD 0⟩, ⟨false, true, byte.getLsbD 0⟩,
    ⟨false, false, byte.getLsbD 0⟩]

/-- Cycle zero is the interval immediately following acceptance. -/
def expectedPins (cfg : Config) (byte : BitVec 8) (cycle : Nat) : Pins :=
  (wireFrame byte).getD (cycle / cfg.halfCycles) ⟨true, false, false⟩

/-- Wire-order sample index 0 receives the most-significant bit. -/
def sampleTime (cfg : Config) (bit : Fin 8) : Nat :=
  (2 * bit.val + 1) * cfg.halfCycles

/-- Expected receive slots after the specified sampling edges up to `cycle`. -/
def expectedSamples (cfg : Config) (incoming : Nat → Bool) (cycle : Nat) : Vector Bool 8 :=
  Vector.ofFn fun bit =>
    if sampleTime cfg bit ≤ cycle then incoming (sampleTime cfg bit) else false

/-- The complete received byte, defined directly from eight edge-indexed input values. -/
def expectedByte (cfg : Config) (incoming : Nat → Bool) : BitVec 8 :=
  BitVec.ofBoolListBE
    [incoming cfg.halfCycles, incoming (3 * cfg.halfCycles),
     incoming (5 * cfg.halfCycles), incoming (7 * cfg.halfCycles),
     incoming (9 * cfg.halfCycles), incoming (11 * cfg.halfCycles),
     incoming (13 * cfg.halfCycles), incoming (15 * cfg.halfCycles)]

theorem wireFrame_size (byte : BitVec 8) : (wireFrame byte).size = 17 := rfl

end Pinwheel.SPI
