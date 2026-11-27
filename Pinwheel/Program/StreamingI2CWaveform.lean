import Pinwheel.Program.StreamingI2CDeadline
import Pinwheel.Program.StreamingCellWaveform
import Pinwheel.Program.StreamingI2CTrace

/-! # SCL and SDA waveforms of one I²C data slot

The I²C proofs establish which bits are captured and when a stretch times out.
This module states the controller's pad waveform within a data slot as pin
observations (`pinTrace`), one per core clock:

* `low_window`: from the slot's boundary state, SCL is driven low for the
  boundary state and `L + 1` low states (`L = lowDuration`), then released. SDA
  takes its data value on the first low state and keeps it.
* `high_window`: once the SCL guard is ready, SCL stays released for that
  state and `H + 1` high states (`H = highDuration`). The next state drives SCL
  low again and releases SDA on the same clock.
* `ready_sample`: the guard is ready only when the sample it reads, taken two
  clocks earlier, shows SCL high.

Pad `0` is SCL and pad `1` is SDA; a set enable bit drives the open-drain pad
low. -/
namespace Pinwheel.Program.StreamingI2CWaveform
open Pinwheel.Program.StreamingReady Pinwheel.Program.StreamingI2CDeadline
open Pinwheel.Program.StreamingCellWaveform

/-- Whether a pin observation drives SCL low. -/
def sclLow (pins : Engine.Reactive.Pins) : Bool := pins.enabled.getLsbD 0

/-- Whether a pin observation drives SDA low. -/
def sdaLow (pins : Engine.Reactive.Pins) : Bool := pins.enabled.getLsbD 1

section
variable (profile : I2cProfile)

theorem cell_base (high last : Bool) :
    (i2cCell profile).basePins high last = ⟨0, if high then 0 else 1⟩ := by
  cases high <;> cases last <;> simp [Streaming.Cell.basePins, i2cCell] <;> decide +kernel

theorem cell_data (high last bit : Bool) :
    (i2cCell profile).dataPins high last bit =
      ⟨0, if high then (if bit then 0 else 2) else (if bit then 1 else 3)⟩ := by
  cases high <;> cases last <;> cases bit <;>
    simp [Streaming.Cell.dataPins, Streaming.Cell.basePins, i2cCell] <;> decide +kernel

/-- The last LOW clock of a guarded stream releases into WAIT with the HIGH pins. -/
theorem clock_low_exit (s : State a) (i : Input) (low : s.phase = .low) (zero : s.countdown = 0)
    (row : s.current = streamRowFor profile) :
    let t := clock (programFor profile) i s
    t.phase = .waiting ∧ t.pins = s.highPins ∧ t.current = s.current := by
  simp [clock, engine, low, zero, row, Instruction.hasHighGuard]

/-- A ready guarded wait enters HIGH with the full HIGH countdown and unchanged pins. -/
theorem clock_ready (s : State a) (i : Input) (waiting : s.phase = .waiting)
    (row : s.current = streamRowFor profile) (ready : s.waitReady = true) :
    let t := clock (programFor profile) i s
    t.phase = .high ∧ t.countdown.toNat = profile.highDuration.val ∧ t.pins = s.pins ∧
      t.current = s.current ∧ t.lastCell = s.lastCell := by
  simp only [clock, engine, waiting, ready, if_true, row, Instruction.isStream, State.enterHigh,
    State.captureData, Instruction.cell, State.lastCell]
  refine ⟨by trivial, ?_, by trivial, by trivial, by trivial⟩
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt profile.highDuration.isLt

end

section
variable (profile : I2cProfile)

end

section
variable (profile : I2cProfile)

/-- LOW window of a data slot: the boundary observation, `L + 1` LOW
observations with SDA at its data value, then SCL released with the same SDA. -/
theorem low_window (s : State a) (boundary : s.phase = .boundary) (row : s.current = streamRowFor profile)
    (reserve : s.canReserve = true) (inputs : List Input) (ordinary : ∀ i ∈ inputs, Ordinary i)
    (length : inputs.length = profile.lowDuration.val + 2) :
    ∃ bit, pinTrace (programFor profile) s inputs =
      s.pins :: (List.replicate (profile.lowDuration.val + 1) ((i2cCell profile).dataPins false s.lastCell bit) ++
        [(i2cCell profile).dataPins true s.lastCell bit]) := by
  obtain ⟨first, mid, last, rfl, midLength⟩ := split_last inputs _ length
  have ordinaryFirst := ordinary first List.mem_cons_self
  have ordinaryMid : ∀ i ∈ mid, Ordinary i := fun i mem =>
    ordinary i (List.mem_cons_of_mem _ (List.mem_append_left _ mem))
  have ordinaryLast := ordinary last (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have eq1 := step_clock (programFor profile) s first (by rw [boundary]; decide) ordinaryFirst
  obtain ⟨low1, count1, current1, pins1, lastCell1⟩ := clock_boundary (programFor profile) s first (i2cCell profile) (some (i2cGuard profile 1 1)) boundary row reserve
  rw [show (i2cCell profile).lowDuration = profile.lowDuration from rfl] at count1
  generalize ht1 : clock (programFor profile) first s = t1 at eq1 low1 count1 current1 pins1 lastCell1
  obtain ⟨trace, low2, count2, pins2, current2, bit2, remaining2⟩ :=
    low_hold (programFor profile) t1 low1 mid ordinaryMid (by rw [count1, midLength]; exact Nat.le_refl _)
  generalize ht2 : run (programFor profile) t1 mid = t2 at low2 count2 pins2 current2 bit2 remaining2
  have zero : t2.countdown = 0 := zero_of_toNat _ (by rw [count2, count1, midLength]; omega)
  have row2 : t2.current = streamRowFor profile := by rw [current2, current1, row]
  have eq2 := step_clock (programFor profile) t2 last (by rw [low2]; decide) ordinaryLast
  obtain ⟨_, exitPins, _⟩ := clock_low_exit profile t2 last low2 zero row2
  have lastCell2 : t2.lastCell = s.lastCell := by
    rw [← lastCell1]; simp only [State.lastCell, current2, remaining2]
  have high2 : t2.highPins = (i2cCell profile).dataPins true s.lastCell t1.cellBit := by
    simp only [State.highPins, row2, Instruction.isStream, Instruction.cell, if_true, lastCell2, bit2]
  refine ⟨t1.cellBit, ?_⟩
  simp only [pinTrace, eq1, pinTrace_append, trace, midLength, List.take_replicate, ht2]
  change s.pins :: (_ ++ [t2.pins, (step (programFor profile) last t2).pins]) = _
  rw [eq2, exitPins, high2, pins2, pins1, replicate_snoc, Nat.min_eq_left (Nat.le_succ _)]

/-- HIGH window of a data slot: once the guard is ready, the ready observation
and `H + 1` HIGH observations keep SCL released and SDA unchanged; the next
observation drives the cell's LOW base pins. -/
theorem high_window (s : State a) (waiting : s.phase = .waiting) (row : s.current = streamRowFor profile)
    (ready : s.waitReady = true) (inputs : List Input) (ordinary : ∀ i ∈ inputs, Ordinary i)
    (length : inputs.length = profile.highDuration.val + 2) :
    pinTrace (programFor profile) s inputs =
      List.replicate (profile.highDuration.val + 2) s.pins ++ [(i2cCell profile).basePins false s.lastCell] := by
  obtain ⟨first, mid, last, rfl, midLength⟩ := split_last inputs _ length
  have ordinaryFirst := ordinary first List.mem_cons_self
  have ordinaryMid : ∀ i ∈ mid, Ordinary i := fun i mem =>
    ordinary i (List.mem_cons_of_mem _ (List.mem_append_left _ mem))
  have ordinaryLast := ordinary last (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have eq1 := step_clock (programFor profile) s first (by rw [waiting]; decide) ordinaryFirst
  obtain ⟨high1, count1, pins1, current1, lastCell1⟩ := clock_ready profile s first waiting row ready
  generalize ht1 : clock (programFor profile) first s = t1 at eq1 high1 count1 pins1 current1 lastCell1
  obtain ⟨trace, high2, count2, pins2, current2, remaining2⟩ :=
    high_hold (programFor profile) t1 high1 mid ordinaryMid (by rw [count1, midLength]; exact Nat.le_refl _)
  generalize ht2 : run (programFor profile) t1 mid = t2 at high2 count2 pins2 current2 remaining2
  have zero : t2.countdown = 0 := zero_of_toNat _ (by rw [count2, count1, midLength]; omega)
  have row2 : t2.current = streamRowFor profile := by rw [current2, current1, row]
  have eq2 := step_clock (programFor profile) t2 last (by rw [high2]; decide) ordinaryLast
  have exitPins := clock_high_exit (programFor profile) t2 last (i2cCell profile) (some (i2cGuard profile 1 1)) high2 zero row2
  have lastCell2 : t2.lastCell = s.lastCell := by
    rw [← lastCell1]; simp only [State.lastCell, current2, remaining2]
  simp only [pinTrace, eq1, pinTrace_append, trace, midLength, List.take_replicate, ht2]
  change s.pins :: (_ ++ [t2.pins, (step (programFor profile) last t2).pins]) = _
  rw [eq2, exitPins, lastCell2, pins2, pins1, replicate_snoc, List.replicate_succ,
    Nat.min_eq_left (Nat.le_succ _)]
  rfl

/-- The guard is ready only when the sample it reads shows SCL high. With
`sampler_second`, that sample is the raw input two clocks earlier. -/
theorem ready_sample (s : State a) (row : s.current = streamRowFor profile) (ready : s.waitReady = true) :
    s.samplerSecond.getLsbD 0 = true := by
  have bit : ∀ raw : BitVec 2, ((raw &&& 1#2) == 1#2) = raw.getLsbD 0 := by decide
  rw [← bit]
  simpa [State.waitReady, row, Instruction.guard, i2cGuard, Guard.matches] using ready

/-- LOW observations drive SCL low and SDA low exactly for a zero data bit. -/
theorem low_pins (last bit : Bool) :
    sclLow ((i2cCell profile).dataPins false last bit) = true ∧
      sdaLow ((i2cCell profile).dataPins false last bit) = !bit := by
  rw [cell_data]; cases bit <;> decide

/-- HIGH observations release SCL and keep the same SDA. -/
theorem high_pins (last bit : Bool) :
    sclLow ((i2cCell profile).dataPins true last bit) = false ∧
      sdaLow ((i2cCell profile).dataPins true last bit) = !bit := by
  rw [cell_data]; cases bit <;> decide

/-- The next boundary drives SCL low and releases SDA on the same clock. After
a zero bit, SDA rises on the edge where SCL falls: the controller's data hold
time is zero core clocks. -/
theorem boundary_pins (last : Bool) :
    sclLow ((i2cCell profile).basePins false last) = true ∧
      sdaLow ((i2cCell profile).basePins false last) = false := by
  rw [cell_base]; decide

end

/-! ## Frame ends

The START hold row and the STOP hold row are pulses with SDA low and SCL
released for both phases (`holdCell`). -/

def holdCell (profile : I2cProfile) : Cell :=
  {lowDuration := profile.highDuration, highDuration := profile.highDuration,
   lowPins := ⟨0, 2⟩, highPins := ⟨0, 2⟩}

theorem hold_row (profile : I2cProfile) : i2cHold profile 2 = .pulse (holdCell profile) := rfl

theorem hold_base (profile : I2cProfile) : (holdCell profile).basePins false false = ⟨0, 2⟩ := by
  simp [holdCell, Streaming.Cell.basePins]

private theorem pc_toNat (pc : BitVec 7) (n : Nat) (h : pc.toNat = n) (small : n < 127) :
    (pc + 1).toNat = n + 1 := by
  have one : (1 : BitVec 7).toNat = 1 := rfl
  rw [BitVec.toNat_add, one, h]
  omega

private theorem hold_list (H : Nat) (x : Engine.Reactive.Pins) :
    List.replicate (H + 2) x ++ List.replicate (H + 1) x ++ [x] = List.replicate (2 * H + 4) x := by
  rw [List.replicate_append_replicate, ← List.replicate_succ']
  congr 1
  omega

/-- START: from the FETCH of row 1, SDA is held low with SCL released for
`2H + 4` observations; the next observation is the first data slot's
boundary, which drives SCL low and releases SDA. -/
theorem start_window (s : State a) (fetch : s.phase = .fetch) (pc : s.pc.toNat = 1) (live : s.remaining ≠ 0)
    (inputs : List Input) (ordinary : ∀ i ∈ inputs, Ordinary i)
    (length : inputs.length = 2 * profile.highDuration.val + 5) :
    pinTrace (programFor profile) s inputs =
      s.pins :: (List.replicate (2 * profile.highDuration.val + 4) ⟨0, 2⟩ ++ [⟨0, 1⟩]) := by
  have row1 : (programFor profile).fetch s.pc.toNat = some (.pulse (holdCell profile)) := by
    rw [pc]; exact StreamingI2CTrace.Profiled.fetch profile 1 (by decide)
  obtain ⟨pulse, last, rfl, pulseLength⟩ : ∃ pulse last, inputs = pulse ++ [last] ∧
      pulse.length = (holdCell profile).lowDuration.val + (holdCell profile).highDuration.val + 4 := by
    have nonempty : inputs ≠ [] := by intro nil; simp [nil] at length
    exact ⟨inputs.dropLast, inputs.getLast nonempty, (List.dropLast_concat_getLast nonempty).symm,
      by simp only [List.length_dropLast, holdCell]; omega⟩
  have ordinaryPulse : ∀ i ∈ pulse, Ordinary i := fun i mem => ordinary i (List.mem_append_left _ mem)
  obtain ⟨trace, phase, pc2, remaining, pins⟩ :=
    pulse_window (programFor profile) s (holdCell profile) fetch row1 pulse ordinaryPulse pulseLength
  generalize ht : run (programFor profile) s pulse = t at phase pc2 remaining pins
  have row2 : (programFor profile).fetch t.pc.toNat =
      some (.stream (i2cCell profile) (some (i2cGuard profile 1 1))) := by
    rw [pc2, pc_toNat s.pc 1 pc (by decide)]; exact StreamingI2CTrace.Profiled.fetch profile 2 (by decide)
  have eq := step_clock (programFor profile) t last (by rw [phase]; decide)
    (ordinary last (List.mem_append_right _ List.mem_cons_self))
  have first := clock_fetch_stream (programFor profile) t last _ _ phase row2 (by rw [remaining]; exact live)
  rw [pinTrace_snoc, trace, ht, eq, first, cell_base, hold_base]
  simp only [holdCell]
  rw [List.cons_append, hold_list]
  rfl

/-- STOP: from the ready wait of row 4 (SDA low, SCL released and seen high),
SDA stays low with SCL released for `2H + 6` observations; HALT then
releases SDA. -/
theorem stop_window (s : State a) (waiting : s.phase = .waiting) (pc : s.pc.toNat = 4)
    (row : s.current = .driveWait ⟨0, 2⟩ (i2cGuard profile 1 1)) (ready : s.waitReady = true)
    (held : s.pins = ⟨0, 2⟩) (inputs : List Input) (ordinary : ∀ i ∈ inputs, Ordinary i)
    (length : inputs.length = 2 * profile.highDuration.val + 6) :
    pinTrace (programFor profile) s inputs =
      List.replicate (2 * profile.highDuration.val + 6) ⟨0, 2⟩ ++ [⟨0, 0⟩] := by
  obtain ⟨first, rest, rfl⟩ : ∃ first rest, inputs = first :: rest := by
    cases inputs with
    | nil => simp at length
    | cons first rest => exact ⟨first, rest, rfl⟩
  obtain ⟨pulse, last, rfl, pulseLength⟩ : ∃ pulse last, rest = pulse ++ [last] ∧
      pulse.length = (holdCell profile).lowDuration.val + (holdCell profile).highDuration.val + 4 := by
    have nonempty : rest ≠ [] := by intro nil; simp [nil] at length
    exact ⟨rest.dropLast, rest.getLast nonempty, (List.dropLast_concat_getLast nonempty).symm,
      by simp only [List.length_dropLast, holdCell]; simp only [List.length_cons] at length; omega⟩
  have eq1 := step_clock (programFor profile) s first (by rw [waiting]; decide) (ordinary first List.mem_cons_self)
  obtain ⟨phase1, pc1, pins1, _⟩ := clock_wait_ready (programFor profile) s first _ _ waiting row ready
  generalize ht1 : clock (programFor profile) first s = t1 at eq1 phase1 pc1 pins1
  have row5 : (programFor profile).fetch t1.pc.toNat = some (.pulse (holdCell profile)) := by
    rw [pc1, pc_toNat s.pc 4 pc (by decide)]; exact StreamingI2CTrace.Profiled.fetch profile 5 (by decide)
  have ordinaryPulse : ∀ i ∈ pulse, Ordinary i := fun i mem =>
    ordinary i (List.mem_cons_of_mem _ (List.mem_append_left _ mem))
  obtain ⟨trace, phase, pc6, _, _⟩ :=
    pulse_window (programFor profile) t1 (holdCell profile) phase1 row5 pulse ordinaryPulse pulseLength
  generalize ht : run (programFor profile) t1 pulse = t at phase pc6
  have row6 : (programFor profile).fetch t.pc.toNat = some .halt := by
    rw [pc6, pc_toNat t1.pc 5 (by rw [pc1, pc_toNat s.pc 4 pc (by decide)]) (by decide)]
    exact StreamingI2CTrace.Profiled.fetch profile 6 (by decide)
  have eq := step_clock (programFor profile) t last (by rw [phase]; decide)
    (ordinary last (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)))
  have halt := clock_fetch_halt (programFor profile) t last phase row6
  simp only [pinTrace, eq1]
  rw [pinTrace_snoc, trace, ht, eq, halt, pins1, held, hold_base]
  simp only [holdCell]
  rw [List.cons_append, hold_list]
  rfl

/-- The STOP wait is ready only when its sample, two clocks old, shows SCL high. -/
theorem stop_ready_sample (s : State a) (row : s.current = .driveWait ⟨0, 2⟩ (i2cGuard profile 1 1))
    (ready : s.waitReady = true) : s.samplerSecond.getLsbD 0 = true := by
  have bit : ∀ raw : BitVec 2, ((raw &&& 1#2) == 1#2) = raw.getLsbD 0 := by decide
  rw [← bit]
  simpa [State.waitReady, row, Instruction.guard, i2cGuard, Guard.matches] using ready

/-! ## Real time

Reading each pin observation as one core period and the guard's sample as the
bus level at its clock, the windows give lower bounds on what the bus shows:

* SCL LOW lasts at least `L + 2` periods (`low_window`; a stretching target
  only lengthens it).
* SCL HIGH lasts at least `H + 4` periods: the bus was high at the sample read
  by the ready guard, two clocks before it (`ready_sample`, `sampler_second`),
  and stays released through `H + 2` more observations (`high_window`). This
  assumes the target does not pull SCL low again during HIGH.
* SDA is stable for at least `L + 1` periods before SCL is released.
* The controller's data hold after SCL falls is zero periods (`boundary_pins`).
* START hold (SDA low to SCL low) lasts `2H + 4` periods (`start_window`).
* STOP setup (SCL high to SDA released) lasts at least `2H + 8` periods: the
  SCL-high sample is two clocks older than the ready STOP wait
  (`stop_ready_sample`), which is followed by `2H + 6` observations before HALT
  releases SDA (`stop_window`).
* Bus-free time between transactions depends on when the host starts the next
  one, so it is not bounded here.

Pad delays, rise times and the sampler's analog behavior are outside this
model. `Meets` compares these bounds with an I²C mode's minimum times. -/

def lowPeriods (profile : I2cProfile) : Nat := profile.lowDuration.val + 2
def highPeriods (profile : I2cProfile) : Nat := profile.highDuration.val + 4
def setupPeriods (profile : I2cProfile) : Nat := profile.lowDuration.val + 1
def startHoldPeriods (profile : I2cProfile) : Nat := 2 * profile.highDuration.val + 4
def stopSetupPeriods (profile : I2cProfile) : Nat := 2 * profile.highDuration.val + 8

/-- Controller-side minimum times of an I²C bus mode, in nanoseconds: SCL LOW,
SCL HIGH, SDA setup, the shortest SCL period (1 / maximum frequency), START
hold and STOP setup. -/
structure Mode where
  name : String
  lowNs : Nat
  highNs : Nat
  setupNs : Nat
  periodNs : Nat
  startHoldNs : Nat
  stopSetupNs : Nat
  deriving Repr

def standardMode : Mode := ⟨"standard", 4700, 4000, 250, 10000, 4000, 4000⟩
def fastMode : Mode := ⟨"fast", 1300, 600, 100, 2500, 600, 600⟩
def fastPlusMode : Mode := ⟨"fast_plus", 500, 260, 50, 1000, 260, 260⟩

def modes : List Mode := [standardMode, fastMode, fastPlusMode]

/-- A profile meets a mode at core clock `hz` when every bound, converted at
`10⁹ / hz` ns per period, reaches the mode's minimum. -/
def Meets (profile : I2cProfile) (mode : Mode) (hz : Nat) : Prop :=
  mode.lowNs * hz ≤ lowPeriods profile * 1000000000 ∧
  mode.highNs * hz ≤ highPeriods profile * 1000000000 ∧
  mode.setupNs * hz ≤ setupPeriods profile * 1000000000 ∧
  mode.periodNs * hz ≤ (lowPeriods profile + highPeriods profile) * 1000000000 ∧
  mode.startHoldNs * hz ≤ startHoldPeriods profile * 1000000000 ∧
  mode.stopSetupNs * hz ≤ stopSetupPeriods profile * 1000000000

instance (profile : I2cProfile) (mode : Mode) (hz : Nat) : Decidable (Meets profile mode hz) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The standard profile meets standard mode only up to about 1.06 MHz: its
4-clock LOW must last 4.7 µs. -/
theorem standard_meets_standard_iff (hz : Nat) :
    Meets .standard standardMode hz ↔ hz ≤ 1063829 := by
  simp only [Meets, standardMode, lowPeriods, highPeriods, setupPeriods, startHoldPeriods, stopSetupPeriods]
  change 4700 * hz ≤ 5 * 1000000000 ∧ 4000 * hz ≤ 7 * 1000000000 ∧ 250 * hz ≤ 4 * 1000000000 ∧
    10000 * hz ≤ (5 + 7) * 1000000000 ∧ 4000 * hz ≤ 10 * 1000000000 ∧ 4000 * hz ≤ 14 * 1000000000 ↔ _
  omega

/-- At 4 MHz the standard profile meets Fast-mode Plus but not Fast mode:
its LOW lasts 1.25 µs against Fast mode's 1.3 µs. -/
theorem standard_at_4MHz :
    Meets .standard fastPlusMode 4000000 ∧ ¬ Meets .standard fastMode 4000000 := by
  decide

/-- Standard mode is reachable at the 20 ns target with long cell durations
(LOW 256 and HIGH 240 clocks in the Python builder). Like the other
mode-specific profiles it uses the largest poll budget (255), so a target may
stretch for 252 core clocks: longer SCL phases go with longer stretches. -/
def standardModeAt50MHz : I2cProfile := ⟨255, 239, 254, 1, 28, by decide, by decide, by decide, by decide⟩

theorem standardModeAt50MHz_meets : Meets standardModeAt50MHz standardMode 50000000 := by
  decide

/-- Standard mode at 4 MHz: LOW 18 and HIGH 18 clocks and a 255-poll budget in
the Python builder. -/
def standardModeAt4MHz : I2cProfile := ⟨17, 17, 254, 1, 28, by decide, by decide, by decide, by decide⟩

/-- Fast mode at 4 MHz: LOW 5 and HIGH 3 clocks and a 255-poll budget in the
Python builder. -/
def fastModeAt4MHz : I2cProfile := ⟨4, 2, 254, 1, 28, by decide, by decide, by decide, by decide⟩

theorem profiles_at_4MHz :
    Meets standardModeAt4MHz standardMode 4000000 ∧ Meets fastModeAt4MHz fastMode 4000000 := by
  decide

end Pinwheel.Program.StreamingI2CWaveform
