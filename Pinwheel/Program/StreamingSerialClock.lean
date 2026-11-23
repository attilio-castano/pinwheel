import Pinwheel.Program.StreamingCellWaveform
import Pinwheel.Program.StreamingSPI

/-! # Clock contract for SPI and JTAG

Both protocols use one unguarded stream cell per bit, with the serial clock on
output 1 and data out on output 0. `cell_window` fixes the cell's pins per
core clock and `capture_sample` fixes which raw input the data-in capture
reads. For a cell with LOW duration `L` and HIGH duration `H` (the builders'
`half_cycles` is `L + 1 = H + 1`), and one core period `P` per observation:

* the clock sits at its idle level for at least `L + 2` periods (more if the
  host is late with data) and at its active level for exactly `H + 1`;
* data out changes on the first idle observation and holds through the
  active level: `L + 1` periods of setup and `H + 1` of hold around the
  leading edge;
* data in is the raw input from `L − 1` periods after the trailing edge, three
  periods before the leading edge. The peer's clock-to-output delay must fit
  in those `L − 1` periods.

`Fits` turns this into conditions on a peer's maximum clock rate and output
delay. Pad and board delays are outside the model. -/
namespace Pinwheel.Program.StreamingSerialClock
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingCellWaveform

/-- The serial clock: output 1's level. -/
def clockLevel (pins : Engine.Reactive.Pins) : Bool := pins.levels.getLsbD 1

/-- Data out (MOSI, TDI): output 0's level. -/
def dataOut (pins : Engine.Reactive.Pins) : Bool := pins.levels.getLsbD 0

/-- JTAG TMS: output 2's level. -/
def tms (pins : Engine.Reactive.Pins) : Bool := pins.levels.getLsbD 2

set_option linter.unusedSimpArgs false in
/-- SPI cells: SCK at `cpol` while idle and inverted while active; MOSI is the bit. -/
theorem spi_pins (mode : StreamingSPI.Mode) (d : Fin 256) (high last bit : Bool) :
    clockLevel ((StreamingSPI.cell mode d).dataPins high last bit) = (mode.cpol != high) ∧
      dataOut ((StreamingSPI.cell mode d).dataPins high last bit) = bit ∧
      clockLevel ((StreamingSPI.cell mode d).basePins false last) = mode.cpol := by
  cases mode <;> cases high <;> cases last <;> cases bit <;>
    simp [clockLevel, dataOut, StreamingSPI.cell, StreamingSPI.clockPins, StreamingSPI.Mode.cpol,
      Streaming.spiCell, Streaming.Cell.dataPins, Streaming.Cell.basePins] <;> decide +kernel

set_option linter.unusedSimpArgs false in
/-- JTAG cells: TCK low while idle and high while active; TDI is the bit; TMS
rises only on the last cell. -/
theorem jtag_pins (d : Fin 256) (high last bit : Bool) :
    clockLevel ((Streaming.jtagCell d).dataPins high last bit) = high ∧
      dataOut ((Streaming.jtagCell d).dataPins high last bit) = bit ∧
      tms ((Streaming.jtagCell d).dataPins high last bit) = last ∧
      clockLevel ((Streaming.jtagCell d).basePins false last) = false := by
  cases high <;> cases last <;> cases bit <;>
    simp [clockLevel, dataOut, tms, Streaming.jtagCell, Streaming.Cell.dataPins,
      Streaming.Cell.basePins] <;> decide +kernel

/-! ## Real time -/

/-- Periods the clock spends at its active level. -/
def activePeriods (half : Nat) : Nat := half

/-- Least periods at the idle level: the boundary clock plus `half`. -/
def idlePeriods (half : Nat) : Nat := half + 1

/-- Periods between the trailing edge and the data-in sample. -/
def inputWindow (half : Nat) : Nat := half - 2

/-- A peer accepts a serial clock up to `maxClockHz` and drives its data out
within `outputDelayNs` of the trailing edge. With builder setting `half`
(`half_cycles`, at least 3) and core clock `hz`, the fastest bit period
(`2 * half + 1` core periods) respects the peer's maximum rate and the
peer's delay fits before the sample. -/
def Fits (half hz maxClockHz outputDelayNs : Nat) : Prop :=
  3 ≤ half ∧ hz ≤ maxClockHz * (idlePeriods half + activePeriods half) ∧
    outputDelayNs * hz ≤ inputWindow half * 1000000000

instance (half hz maxClockHz outputDelayNs : Nat) : Decidable (Fits half hz maxClockHz outputDelayNs) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The window lengths follow from `cell_window` and `capture_sample` for a
cell whose durations are `half - 1`. -/
theorem windows (half : Nat) (atLeast : 3 ≤ half) (c : Cell) (low : c.lowDuration.val = half - 1)
    (high : c.highDuration.val = half - 1) :
    c.lowDuration.val + 2 = idlePeriods half ∧ c.highDuration.val + 1 = activePeriods half ∧
      c.lowDuration.val - 1 = inputWindow half := by
  simp only [idlePeriods, activePeriods, inputWindow, low, high]
  omega

/-- The bring-up settings (`half_cycles = 4`) at 4 MHz: a bit clock of up to
444.4 kHz, so the peer must accept at least 444,445 Hz, with a 500 ns window
for its output delay. -/
theorem at_4MHz : Fits 4 4000000 444445 500 ∧ ¬ Fits 4 4000000 444444 500 ∧ ¬ Fits 4 4000000 444445 501 := by
  decide

/-- The fastest setting (`half_cycles = 3`) at the 20 ns target: a bit clock
of up to 7.14 MHz, and the peer must drive data within 20 ns. -/
theorem at_50MHz : Fits 3 50000000 7142858 20 ∧ ¬ Fits 3 50000000 7142857 20 ∧ ¬ Fits 3 50000000 7142858 21 := by
  decide

end Pinwheel.Program.StreamingSerialClock
