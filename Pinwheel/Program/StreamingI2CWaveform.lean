import Pinwheel.Program.StreamingI2CDeadline

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

/-- An ordinary runtime clock: no reset, START or RELEASE command. -/
def Ordinary (i : Input) : Prop := i.Runtime ∧ i.command ≠ 4#4

/-- Whether a pin observation drives SCL low. -/
def sclLow (pins : Engine.Reactive.Pins) : Bool := pins.enabled.getLsbD 0

/-- Whether a pin observation drives SDA low. -/
def sdaLow (pins : Engine.Reactive.Pins) : Bool := pins.enabled.getLsbD 1

section
variable (profile : I2cProfile)

theorem step_clock (s : State a) (i : Input) (busy : s.phase ≠ .free) (ordinary : Ordinary i) :
    step (programFor profile) i s = clock (programFor profile) i s := by
  rcases ordinary with ⟨⟨cold, warm⟩, release⟩
  simp [step, cold, (show i.command ≠ 15#4 from warm), release, State.canStart, busy]

theorem cell_base (high last : Bool) :
    (i2cCell profile).basePins high last = ⟨0, if high then 0 else 1⟩ := by
  cases high <;> cases last <;> simp [Streaming.Cell.basePins, i2cCell] <;> decide +kernel

theorem cell_data (high last bit : Bool) :
    (i2cCell profile).dataPins high last bit =
      ⟨0, if high then (if bit then 0 else 2) else (if bit then 1 else 3)⟩ := by
  cases high <;> cases last <;> cases bit <;>
    simp [Streaming.Cell.dataPins, Streaming.Cell.basePins, i2cCell] <;> decide +kernel

/-- A LOW-phase clock with time left only counts down. -/
theorem clock_low_tick (s : State a) (i : Input) (low : s.phase = .low) (left : s.countdown ≠ 0) :
    let t := clock (programFor profile) i s
    t.phase = .low ∧ t.countdown = s.countdown - 1 ∧ t.pins = s.pins ∧ t.current = s.current := by
  have left' : ¬ s.countdown = 0#8 := left
  simp [clock, engine, low, left']

/-- The last LOW clock of a guarded stream releases into WAIT with the HIGH pins. -/
theorem clock_low_exit (s : State a) (i : Input) (low : s.phase = .low) (zero : s.countdown = 0)
    (row : s.current = streamRowFor profile) :
    let t := clock (programFor profile) i s
    t.phase = .waiting ∧ t.pins = s.highPins ∧ t.current = s.current := by
  simp [clock, engine, low, zero, row, Instruction.hasHighGuard]

/-- A HIGH-phase clock with time left only counts down. -/
theorem clock_high_tick (s : State a) (i : Input) (high : s.phase = .high) (left : s.countdown ≠ 0) :
    let t := clock (programFor profile) i s
    t.phase = .high ∧ t.countdown = s.countdown - 1 ∧ t.pins = s.pins ∧ t.current = s.current := by
  have left' : ¬ s.countdown = 0#8 := left
  simp [clock, engine, high, left']

/-- The last HIGH clock of a stream cell drives the cell's LOW base pins. -/
theorem clock_high_exit (s : State a) (i : Input) (high : s.phase = .high) (zero : s.countdown = 0)
    (row : s.current = streamRowFor profile) :
    (clock (programFor profile) i s).pins = (i2cCell profile).basePins false s.lastCell := by
  simp [clock, engine, high, zero, row, Instruction.cell]

/-- A reserving boundary enters LOW with the full LOW countdown and the data pins. -/
theorem clock_boundary (s : State a) (i : Input) (boundary : s.phase = .boundary)
    (row : s.current = streamRowFor profile) (reserve : s.canReserve = true) :
    let t := clock (programFor profile) i s
    t.phase = .low ∧ t.countdown.toNat = profile.lowDuration.val ∧ t.current = s.current ∧
      t.pins = (i2cCell profile).dataPins false s.lastCell t.cellBit ∧ t.lastCell = s.lastCell := by
  simp only [clock, engine, boundary, reserve, if_true, row, Instruction.isStream, Instruction.cell,
    State.lastCell]
  refine ⟨by trivial, ?_, by trivial, by trivial, by trivial⟩
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt profile.lowDuration.isLt

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

theorem run_cons (p : Program) (s : State a) (i : Input) (rest : List Input) :
    run p s (i :: rest) = run p (step p i s) rest := rfl

theorem run_append (p : Program) (s : State a) (xs ys : List Input) :
    run p s (xs ++ ys) = run p (run p s xs) ys := by
  unfold run
  exact List.foldl_append

theorem pinTrace_append (p : Program) (s : State a) (xs ys : List Input) :
    pinTrace p s (xs ++ ys) = (pinTrace p s xs).take xs.length ++ pinTrace p (run p s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, pinTrace, List.length_cons, List.take_succ_cons, ih, run_cons,
      List.cons_append]

private theorem countdown_pred (c : BitVec 8) (positive : 0 < c.toNat) : (c - 1).toNat = c.toNat - 1 := by
  have := c.isLt
  have one : (1 : BitVec 8).toNat = 1 := rfl
  rw [BitVec.toNat_sub, one]
  omega

set_option linter.unusedSimpArgs false in
/-- Ordinary clocks shift the two-stage input sampler in every phase. -/
theorem step_samplers (p : Program) (s : State a) (i : Input) (ordinary : Ordinary i) :
    (step p i s).samplerFirst = i.rawInputs ∧ (step p i s).samplerSecond = s.samplerFirst := by
  rcases ordinary with ⟨⟨cold, warm⟩, release⟩
  have warm' : ¬ i.command = 15#4 := warm
  have release' : ¬ i.command = 4#4 := release
  by_cases start : i.command = 3#4 ∧ s.canStart i = true <;>
    simp [step, cold, warm', release', start, State.start, clock]

/-- After two more ordinary clocks, the second sampler holds the first of them. -/
theorem sampler_second (p : Program) (s : State a) (xs : List Input) (x y : Input)
    (ordinary : Ordinary x) (next : Ordinary y) :
    (run p s (xs ++ [x, y])).samplerSecond = x.rawInputs := by
  rw [run_append]
  change (step p y (step p x (run p s xs))).samplerSecond = _
  rw [(step_samplers p _ y next).2, (step_samplers p _ x ordinary).1]

section
variable (profile : I2cProfile)

/-- LOW keeps its pins while it counts down. -/
theorem low_hold (s : State a) (low : s.phase = .low) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Ordinary i) (within : inputs.length ≤ s.countdown.toNat) :
    pinTrace (programFor profile) s inputs = List.replicate (inputs.length + 1) s.pins ∧
      (run (programFor profile) s inputs).phase = .low ∧
      (run (programFor profile) s inputs).countdown.toNat = s.countdown.toNat - inputs.length ∧
      (run (programFor profile) s inputs).pins = s.pins ∧
      (run (programFor profile) s inputs).current = s.current ∧
      (run (programFor profile) s inputs).cellBit = s.cellBit ∧
      (run (programFor profile) s inputs).remaining = s.remaining := by
  induction inputs generalizing s with
  | nil => simp [pinTrace, run, low]
  | cons i rest ih =>
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have left : s.countdown ≠ 0 := by
      intro zero; rw [zero] at positive; simp at positive
    have busy : s.phase ≠ .free := by rw [low]; decide
    have eq := step_clock profile s i busy (ordinary i List.mem_cons_self)
    have tick := clock_low_tick profile s i low left
    have keep : (clock (programFor profile) i s).cellBit = s.cellBit ∧
        (clock (programFor profile) i s).remaining = s.remaining := by
      have left' : ¬ s.countdown = 0#8 := left
      simp [clock, engine, low, left']
    have count := countdown_pred s.countdown positive
    obtain ⟨trace, phase, countdown, pins, current, bit, remaining⟩ := ih (clock (programFor profile) i s)
      tick.1 (fun j mem => ordinary j (List.mem_cons_of_mem _ mem))
      (by rw [tick.2.1, count]; simp only [List.length_cons] at within; omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [pinTrace, eq, trace, tick.2.2.1, List.length_cons, List.replicate_succ]
    · rw [run_cons, eq]; exact phase
    · rw [run_cons, eq, countdown, tick.2.1, count]; simp only [List.length_cons]; omega
    · rw [run_cons, eq, pins, tick.2.2.1]
    · rw [run_cons, eq, current, tick.2.2.2]
    · rw [run_cons, eq, bit, keep.1]
    · rw [run_cons, eq, remaining, keep.2]

/-- HIGH keeps its pins while it counts down. -/
theorem high_hold (s : State a) (high : s.phase = .high) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Ordinary i) (within : inputs.length ≤ s.countdown.toNat) :
    pinTrace (programFor profile) s inputs = List.replicate (inputs.length + 1) s.pins ∧
      (run (programFor profile) s inputs).phase = .high ∧
      (run (programFor profile) s inputs).countdown.toNat = s.countdown.toNat - inputs.length ∧
      (run (programFor profile) s inputs).pins = s.pins ∧
      (run (programFor profile) s inputs).current = s.current ∧
      (run (programFor profile) s inputs).remaining = s.remaining := by
  induction inputs generalizing s with
  | nil => simp [pinTrace, run, high]
  | cons i rest ih =>
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have left : s.countdown ≠ 0 := by
      intro zero; rw [zero] at positive; simp at positive
    have busy : s.phase ≠ .free := by rw [high]; decide
    have eq := step_clock profile s i busy (ordinary i List.mem_cons_self)
    have tick := clock_high_tick profile s i high left
    have keep : (clock (programFor profile) i s).remaining = s.remaining := by
      have left' : ¬ s.countdown = 0#8 := left
      simp [clock, engine, high, left']
    have count := countdown_pred s.countdown positive
    obtain ⟨trace, phase, countdown, pins, current, remaining⟩ := ih (clock (programFor profile) i s)
      tick.1 (fun j mem => ordinary j (List.mem_cons_of_mem _ mem))
      (by rw [tick.2.1, count]; simp only [List.length_cons] at within; omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [pinTrace, eq, trace, tick.2.2.1, List.length_cons, List.replicate_succ]
    · rw [run_cons, eq]; exact phase
    · rw [run_cons, eq, countdown, tick.2.1, count]; simp only [List.length_cons]; omega
    · rw [run_cons, eq, pins, tick.2.2.1]
    · rw [run_cons, eq, current, tick.2.2.2]
    · rw [run_cons, eq, remaining, keep]

end

section
variable (profile : I2cProfile)

private theorem split_last (inputs : List Input) (n : Nat) (length : inputs.length = n + 2) :
    ∃ first mid last, inputs = first :: (mid ++ [last]) ∧ mid.length = n := by
  match inputs, length with
  | first :: rest, length =>
    have nonempty : rest ≠ [] := by intro nil; simp [nil] at length
    refine ⟨first, rest.dropLast, rest.getLast nonempty, ?_, ?_⟩
    · rw [List.dropLast_concat_getLast nonempty]
    · simp only [List.length_dropLast]; simp only [List.length_cons] at length; omega

private theorem zero_of_toNat (c : BitVec 8) (zero : c.toNat = 0) : c = 0 :=
  BitVec.eq_of_toNat_eq (by simpa using zero)

private theorem replicate_snoc {α : Type} (n : Nat) (x y : α) :
    List.replicate n x ++ [x, y] = List.replicate (n + 1) x ++ [y] := by
  rw [List.replicate_succ', List.append_assoc]; rfl

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
  have eq1 := step_clock profile s first (by rw [boundary]; decide) ordinaryFirst
  obtain ⟨low1, count1, current1, pins1, lastCell1⟩ := clock_boundary profile s first boundary row reserve
  generalize ht1 : clock (programFor profile) first s = t1 at eq1 low1 count1 current1 pins1 lastCell1
  obtain ⟨trace, low2, count2, pins2, current2, bit2, remaining2⟩ :=
    low_hold profile t1 low1 mid ordinaryMid (by rw [count1, midLength]; exact Nat.le_refl _)
  generalize ht2 : run (programFor profile) t1 mid = t2 at low2 count2 pins2 current2 bit2 remaining2
  have zero : t2.countdown = 0 := zero_of_toNat _ (by rw [count2, count1, midLength]; omega)
  have row2 : t2.current = streamRowFor profile := by rw [current2, current1, row]
  have eq2 := step_clock profile t2 last (by rw [low2]; decide) ordinaryLast
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
  have eq1 := step_clock profile s first (by rw [waiting]; decide) ordinaryFirst
  obtain ⟨high1, count1, pins1, current1, lastCell1⟩ := clock_ready profile s first waiting row ready
  generalize ht1 : clock (programFor profile) first s = t1 at eq1 high1 count1 pins1 current1 lastCell1
  obtain ⟨trace, high2, count2, pins2, current2, remaining2⟩ :=
    high_hold profile t1 high1 mid ordinaryMid (by rw [count1, midLength]; exact Nat.le_refl _)
  generalize ht2 : run (programFor profile) t1 mid = t2 at high2 count2 pins2 current2 remaining2
  have zero : t2.countdown = 0 := zero_of_toNat _ (by rw [count2, count1, midLength]; omega)
  have row2 : t2.current = streamRowFor profile := by rw [current2, current1, row]
  have eq2 := step_clock profile t2 last (by rw [high2]; decide) ordinaryLast
  have exitPins := clock_high_exit profile t2 last high2 zero row2
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

Pad delays, rise times and the sampler's analog behavior are outside this
model. `Meets` compares these bounds with an I²C mode's minimum times. -/

def lowPeriods (profile : I2cProfile) : Nat := profile.lowDuration.val + 2
def highPeriods (profile : I2cProfile) : Nat := profile.highDuration.val + 4
def setupPeriods (profile : I2cProfile) : Nat := profile.lowDuration.val + 1

/-- Controller-side minimum times of an I²C bus mode, in nanoseconds: SCL LOW,
SCL HIGH, SDA setup, and the shortest SCL period (1 / maximum frequency). -/
structure Mode where
  name : String
  lowNs : Nat
  highNs : Nat
  setupNs : Nat
  periodNs : Nat
  deriving Repr

def standardMode : Mode := ⟨"standard", 4700, 4000, 250, 10000⟩
def fastMode : Mode := ⟨"fast", 1300, 600, 100, 2500⟩
def fastPlusMode : Mode := ⟨"fast_plus", 500, 260, 50, 1000⟩

def modes : List Mode := [standardMode, fastMode, fastPlusMode]

/-- A profile meets a mode at core clock `hz` when every bound, converted at
`10⁹ / hz` ns per period, reaches the mode's minimum. -/
def Meets (profile : I2cProfile) (mode : Mode) (hz : Nat) : Prop :=
  mode.lowNs * hz ≤ lowPeriods profile * 1000000000 ∧
  mode.highNs * hz ≤ highPeriods profile * 1000000000 ∧
  mode.setupNs * hz ≤ setupPeriods profile * 1000000000 ∧
  mode.periodNs * hz ≤ (lowPeriods profile + highPeriods profile) * 1000000000

instance (profile : I2cProfile) (mode : Mode) (hz : Nat) : Decidable (Meets profile mode hz) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The standard profile meets standard mode only up to about 1.06 MHz: its
4-clock LOW must last 4.7 µs. -/
theorem standard_meets_standard_iff (hz : Nat) :
    Meets .standard standardMode hz ↔ hz ≤ 1063829 := by
  simp only [Meets, standardMode, lowPeriods, highPeriods, setupPeriods]
  change 4700 * hz ≤ 5 * 1000000000 ∧ 4000 * hz ≤ 7 * 1000000000 ∧ 250 * hz ≤ 4 * 1000000000 ∧
    10000 * hz ≤ (5 + 7) * 1000000000 ↔ _
  omega

/-- At 4 MHz the standard profile meets Fast-mode Plus but not Fast mode:
its LOW lasts 1.25 µs against Fast mode's 1.3 µs. -/
theorem standard_at_4MHz :
    Meets .standard fastPlusMode 4000000 ∧ ¬ Meets .standard fastMode 4000000 := by
  decide

/-- Standard mode is reachable at the 20 ns target with long cell durations
(LOW 256 and HIGH 240 clocks in the Python builder). -/
def standardModeAt50MHz : I2cProfile := ⟨255, 239, 30, 1, 28, by decide, by decide, by decide, by decide⟩

theorem standardModeAt50MHz_meets : Meets standardModeAt50MHz standardMode 50000000 := by
  decide

end Pinwheel.Program.StreamingI2CWaveform
