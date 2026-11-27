import Pinwheel.Program.StreamingReadyExecution

/-! # Pad waveform of one stream cell

Engine facts shared by every stream program, stated as pin observations
(`pinTrace`), one per core clock. They hold for any program, because only
FETCH consults the program.

* `low_hold`, `high_hold`: LOW and HIGH keep their pins while counting down.
* `step_samplers`, `sampler_second`: every ordinary clock shifts the two-stage
  input sampler, so the second stage holds the raw input from two clocks ago.
* `cell_window`: an unguarded stream cell (SPI, JTAG) shows its boundary
  observation, `L + 1` LOW observations, `H + 1` HIGH observations, then the
  next boundary's LOW base pins. The LOW and HIGH observations carry the same
  transmitted bit. Guarded cells (I²C) wait between LOW and HIGH; see
  `StreamingI2CWaveform`. -/
namespace Pinwheel.Program.StreamingCellWaveform
open Pinwheel.Program.StreamingReady

/-- An ordinary runtime clock: no reset, START or RELEASE command. -/
def Ordinary (i : Input) : Prop := i.Runtime ∧ i.command ≠ 4#4

theorem step_clock (p : Program) (s : State a) (i : Input) (busy : s.phase ≠ .free) (ordinary : Ordinary i) :
    step p i s = clock p i s := by
  rcases ordinary with ⟨⟨cold, warm⟩, release⟩
  simp [step, cold, (show i.command ≠ 15#4 from warm), release, State.canStart, busy]

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

theorem pinTrace_snoc (p : Program) (s : State a) (xs : List Input) (x : Input) :
    pinTrace p s (xs ++ [x]) = pinTrace p s xs ++ [(step p x (run p s xs)).pins] := by
  induction xs generalizing s with
  | nil => rfl
  | cons y ys ih => simp only [List.cons_append, pinTrace, ih, run_cons]

theorem countdown_pred (c : BitVec 8) (positive : 0 < c.toNat) : (c - 1).toNat = c.toNat - 1 := by
  have := c.isLt
  have one : (1 : BitVec 8).toNat = 1 := rfl
  rw [BitVec.toNat_sub, one]
  omega

theorem zero_of_toNat (c : BitVec 8) (zero : c.toNat = 0) : c = 0 :=
  BitVec.eq_of_toNat_eq (by simpa using zero)

theorem replicate_snoc {α : Type} (n : Nat) (x y : α) :
    List.replicate n x ++ [x, y] = List.replicate (n + 1) x ++ [y] := by
  rw [List.replicate_succ', List.append_assoc]; rfl

theorem split_last (inputs : List Input) (n : Nat) (length : inputs.length = n + 2) :
    ∃ first mid last, inputs = first :: (mid ++ [last]) ∧ mid.length = n := by
  match inputs, length with
  | first :: rest, length =>
    have nonempty : rest ≠ [] := by intro nil; simp [nil] at length
    refine ⟨first, rest.dropLast, rest.getLast nonempty, ?_, ?_⟩
    · rw [List.dropLast_concat_getLast nonempty]
    · simp only [List.length_dropLast]; simp only [List.length_cons] at length; omega

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

/-- A LOW-phase clock with time left only counts down. -/
theorem clock_low_tick (p : Program) (s : State a) (i : Input) (low : s.phase = .low) (left : s.countdown ≠ 0) :
    let t := clock p i s
    t.phase = .low ∧ t.countdown = s.countdown - 1 ∧ t.pins = s.pins ∧ t.current = s.current ∧
      t.cellBit = s.cellBit ∧ t.remaining = s.remaining := by
  have left' : ¬ s.countdown = 0#8 := left
  simp [clock, engine, low, left']

/-- A HIGH-phase clock with time left only counts down. -/
theorem clock_high_tick (p : Program) (s : State a) (i : Input) (high : s.phase = .high) (left : s.countdown ≠ 0) :
    let t := clock p i s
    t.phase = .high ∧ t.countdown = s.countdown - 1 ∧ t.pins = s.pins ∧ t.current = s.current ∧
      t.remaining = s.remaining := by
  have left' : ¬ s.countdown = 0#8 := left
  simp [clock, engine, high, left']

/-- A reserving boundary of a stream cell enters LOW with the full LOW
countdown and the cell's LOW data pins. -/
theorem clock_boundary (p : Program) (s : State a) (i : Input) (c : Cell) (g : Option Guard)
    (boundary : s.phase = .boundary) (row : s.current = .stream c g) (reserve : s.canReserve = true) :
    let t := clock p i s
    t.phase = .low ∧ t.countdown.toNat = c.lowDuration.val ∧ t.current = s.current ∧
      t.pins = c.dataPins false s.lastCell t.cellBit ∧ t.lastCell = s.lastCell := by
  simp only [clock, engine, boundary, reserve, if_true, row, Instruction.isStream, Instruction.cell,
    State.lastCell]
  refine ⟨by trivial, ?_, by trivial, by trivial, by trivial⟩
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt c.lowDuration.isLt

/-- The last LOW clock of an unguarded stream cell enters HIGH with the full
HIGH countdown and the HIGH data pins of the same bit. -/
theorem clock_low_exit (p : Program) (s : State a) (i : Input) (c : Cell) (low : s.phase = .low)
    (zero : s.countdown = 0) (row : s.current = .stream c none) :
    let t := clock p i s
    t.phase = .high ∧ t.countdown.toNat = c.highDuration.val ∧
      t.pins = c.dataPins true s.lastCell s.cellBit ∧ t.current = s.current ∧ t.remaining = s.remaining := by
  simp only [clock, engine, low, zero, row, Instruction.hasHighGuard, State.enterHigh, State.captureData,
    State.highPins, Instruction.isStream, Instruction.cell, State.lastCell]
  refine ⟨by trivial, ?_, by trivial, by trivial, by trivial⟩
  first
    | (simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt c.highDuration.isLt)
    | exact Nat.mod_eq_of_lt c.highDuration.isLt

/-- The last HIGH clock of a stream cell drives the cell's LOW base pins. -/
theorem clock_high_exit (p : Program) (s : State a) (i : Input) (c : Cell) (g : Option Guard)
    (high : s.phase = .high) (zero : s.countdown = 0) (row : s.current = .stream c g) :
    (clock p i s).pins = c.basePins false s.lastCell := by
  simp [clock, engine, high, zero, row, Instruction.cell]

/-- LOW keeps its pins while it counts down. -/
theorem low_hold (p : Program) (s : State a) (low : s.phase = .low) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Ordinary i) (within : inputs.length ≤ s.countdown.toNat) :
    pinTrace p s inputs = List.replicate (inputs.length + 1) s.pins ∧
      (run p s inputs).phase = .low ∧
      (run p s inputs).countdown.toNat = s.countdown.toNat - inputs.length ∧
      (run p s inputs).pins = s.pins ∧ (run p s inputs).current = s.current ∧
      (run p s inputs).cellBit = s.cellBit ∧ (run p s inputs).remaining = s.remaining := by
  induction inputs generalizing s with
  | nil => simp [pinTrace, run, low]
  | cons i rest ih =>
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have left : s.countdown ≠ 0 := by
      intro zero; rw [zero] at positive; simp at positive
    have eq := step_clock p s i (by rw [low]; decide) (ordinary i List.mem_cons_self)
    obtain ⟨phase1, count1, pins1, current1, bit1, remaining1⟩ := clock_low_tick p s i low left
    have count := countdown_pred s.countdown positive
    obtain ⟨trace, phase, countdown, pins, current, bit, remaining⟩ := ih (clock p i s)
      phase1 (fun j mem => ordinary j (List.mem_cons_of_mem _ mem))
      (by rw [count1, count]; simp only [List.length_cons] at within; omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [pinTrace, eq, trace, pins1, List.length_cons, List.replicate_succ]
    · rw [run_cons, eq]; exact phase
    · rw [run_cons, eq, countdown, count1, count]; simp only [List.length_cons]; omega
    · rw [run_cons, eq, pins, pins1]
    · rw [run_cons, eq, current, current1]
    · rw [run_cons, eq, bit, bit1]
    · rw [run_cons, eq, remaining, remaining1]

/-- HIGH keeps its pins while it counts down. -/
theorem high_hold (p : Program) (s : State a) (high : s.phase = .high) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Ordinary i) (within : inputs.length ≤ s.countdown.toNat) :
    pinTrace p s inputs = List.replicate (inputs.length + 1) s.pins ∧
      (run p s inputs).phase = .high ∧
      (run p s inputs).countdown.toNat = s.countdown.toNat - inputs.length ∧
      (run p s inputs).pins = s.pins ∧ (run p s inputs).current = s.current ∧
      (run p s inputs).remaining = s.remaining := by
  induction inputs generalizing s with
  | nil => simp [pinTrace, run, high]
  | cons i rest ih =>
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have left : s.countdown ≠ 0 := by
      intro zero; rw [zero] at positive; simp at positive
    have eq := step_clock p s i (by rw [high]; decide) (ordinary i List.mem_cons_self)
    obtain ⟨phase1, count1, pins1, current1, remaining1⟩ := clock_high_tick p s i high left
    have count := countdown_pred s.countdown positive
    obtain ⟨trace, phase, countdown, pins, current, remaining⟩ := ih (clock p i s)
      phase1 (fun j mem => ordinary j (List.mem_cons_of_mem _ mem))
      (by rw [count1, count]; simp only [List.length_cons] at within; omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [pinTrace, eq, trace, pins1, List.length_cons, List.replicate_succ]
    · rw [run_cons, eq]; exact phase
    · rw [run_cons, eq, countdown, count1, count]; simp only [List.length_cons]; omega
    · rw [run_cons, eq, pins, pins1]
    · rw [run_cons, eq, current, current1]
    · rw [run_cons, eq, remaining, remaining1]

/-- One unguarded stream cell from its reserving boundary: the boundary
observation, `L + 1` LOW and `H + 1` HIGH observations of the same bit, then
the next boundary's LOW base pins. -/
theorem cell_window (p : Program) (s : State a) (c : Cell) (boundary : s.phase = .boundary)
    (row : s.current = .stream c none) (reserve : s.canReserve = true) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Ordinary i)
    (length : inputs.length = c.lowDuration.val + c.highDuration.val + 3) :
    ∃ bit, pinTrace p s inputs =
      s.pins :: (List.replicate (c.lowDuration.val + 1) (c.dataPins false s.lastCell bit) ++
        List.replicate (c.highDuration.val + 1) (c.dataPins true s.lastCell bit) ++
        [c.basePins false s.lastCell]) := by
  obtain ⟨first, rest, rfl⟩ : ∃ first rest, inputs = first :: rest := by
    cases inputs with
    | nil => simp at length
    | cons first rest => exact ⟨first, rest, rfl⟩
  have ordinaryFirst := ordinary first List.mem_cons_self
  have ordinaryRest : ∀ i ∈ rest, Ordinary i := fun i mem => ordinary i (List.mem_cons_of_mem _ mem)
  have restLength : rest.length = c.lowDuration.val + c.highDuration.val + 2 := by
    simp only [List.length_cons] at length; omega
  -- LOW: the boundary step, then `L` countdown clocks, then the exit clock.
  have eq1 := step_clock p s first (by rw [boundary]; decide) ordinaryFirst
  obtain ⟨low1, count1, current1, pins1, lastCell1⟩ := clock_boundary p s first c none boundary row reserve
  generalize ht1 : clock p first s = t1 at eq1 low1 count1 current1 pins1 lastCell1
  let lowClocks := rest.take c.lowDuration.val
  let tail := rest.drop c.lowDuration.val
  have splitRest : rest = lowClocks ++ tail := (List.take_append_drop _ _).symm
  have lowLength : lowClocks.length = c.lowDuration.val := by
    simp only [lowClocks, List.length_take, restLength]; omega
  have tailLength : tail.length = c.highDuration.val + 2 := by simp [tail, restLength]; omega
  have ordinaryLow : ∀ i ∈ lowClocks, Ordinary i := fun i mem =>
    ordinaryRest i (List.mem_of_mem_take mem)
  have ordinaryTail : ∀ i ∈ tail, Ordinary i := fun i mem => ordinaryRest i (List.mem_of_mem_drop mem)
  obtain ⟨lowTrace, low2, count2, pins2, current2, bit2, remaining2⟩ :=
    low_hold p t1 low1 lowClocks ordinaryLow (by rw [count1, lowLength]; exact Nat.le_refl _)
  generalize ht2 : run p t1 lowClocks = t2 at low2 count2 pins2 current2 bit2 remaining2
  have zero2 : t2.countdown = 0 := zero_of_toNat _ (by rw [count2, count1, lowLength]; omega)
  have row2 : t2.current = .stream c none := by rw [current2, current1, row]
  obtain ⟨enter, highTail, tailEq, highTailLength⟩ : ∃ enter highTail, tail = enter :: highTail ∧
      highTail.length = c.highDuration.val + 1 := by
    match tail, tailLength with
    | enter :: highTail, h => exact ⟨enter, highTail, rfl, by simp only [List.length_cons] at h; omega⟩
  have ordinaryEnter := ordinaryTail enter (by rw [tailEq]; exact List.mem_cons_self)
  have eq3 := step_clock p t2 enter (by rw [low2]; decide) ordinaryEnter
  obtain ⟨high3, count3, pins3, current3, remaining3⟩ := clock_low_exit p t2 enter c low2 zero2 row2
  generalize ht3 : clock p enter t2 = t3 at eq3 high3 count3 pins3 current3 remaining3
  -- HIGH: `H` countdown clocks, then the exit clock.
  obtain ⟨highClocks, exit, rfl, highLength⟩ : ∃ highClocks exit, highTail = highClocks ++ [exit] ∧
      highClocks.length = c.highDuration.val := by
    have nonempty : highTail ≠ [] := by intro nil; simp [nil] at highTailLength
    exact ⟨highTail.dropLast, highTail.getLast nonempty, (List.dropLast_concat_getLast nonempty).symm,
      by simp only [List.length_dropLast]; omega⟩
  have ordinaryHigh : ∀ i ∈ highClocks, Ordinary i := fun i mem =>
    ordinaryTail i (by rw [tailEq]; exact List.mem_cons_of_mem _ (List.mem_append_left _ mem))
  have ordinaryExit : Ordinary exit :=
    ordinaryTail exit (by rw [tailEq]; exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  obtain ⟨highTrace, high4, count4, pins4, current4, remaining4⟩ :=
    high_hold p t3 high3 highClocks ordinaryHigh (by rw [count3, highLength]; exact Nat.le_refl _)
  generalize ht4 : run p t3 highClocks = t4 at high4 count4 pins4 current4 remaining4
  have zero4 : t4.countdown = 0 := zero_of_toNat _ (by rw [count4, count3, highLength]; omega)
  have row4 : t4.current = .stream c none := by rw [current4, current3, row2]
  have eq5 := step_clock p t4 exit (by rw [high4]; decide) ordinaryExit
  have exitPins := clock_high_exit p t4 exit c none high4 zero4 row4
  have last2 : t2.lastCell = s.lastCell := by
    rw [← lastCell1]; simp only [State.lastCell, current2, remaining2]
  have last4 : t4.lastCell = s.lastCell := by
    rw [← last2]; simp only [State.lastCell, current4, current3, remaining4, remaining3]
  refine ⟨t1.cellBit, ?_⟩
  rw [splitRest, tailEq]
  simp only [pinTrace, eq1, pinTrace_append, lowTrace, lowLength, List.take_replicate, ht2]
  rw [eq3, highTrace, highLength, List.take_replicate, ht4, eq5, exitPins, last4, pins4, pins3, last2, bit2,
    pins2, pins1, Nat.min_eq_left (Nat.le_succ _), Nat.min_eq_left (Nat.le_succ _)]
  simp only [List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append]

/-- The data-in capture of an unguarded cell happens on the clock that ends
LOW (`L + 1` clocks into the window) and reads the second sampler, which holds
the raw input from window clock `L - 1`. The next observation is the cell's
leading clock edge (`cell_window`), so the sample precedes it by three clocks. -/
theorem capture_sample (p : Program) (s : State a) (c : Cell) (boundary : s.phase = .boundary)
    (row : s.current = .stream c none) (reserve : s.canReserve = true) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Ordinary i)
    (length : inputs.length = c.lowDuration.val + c.highDuration.val + 3) (one : 1 ≤ c.lowDuration.val) :
    let t := run p s (inputs.take (c.lowDuration.val + 1))
    t.phase = .low ∧ t.countdown = 0 ∧ t.current = .stream c none ∧ t.captures = c.receive ∧
      t.samplerSecond = (inputs[c.lowDuration.val - 1]'(by omega)).rawInputs := by
  intro t
  obtain ⟨first, rest, rfl⟩ : ∃ first rest, inputs = first :: rest := by
    cases inputs with
    | nil => simp at length
    | cons first rest => exact ⟨first, rest, rfl⟩
  have ordinaryRest : ∀ i ∈ rest, Ordinary i := fun i mem => ordinary i (List.mem_cons_of_mem _ mem)
  have restLength : rest.length = c.lowDuration.val + c.highDuration.val + 2 := by
    simp only [List.length_cons] at length; omega
  have eq1 := step_clock p s first (by rw [boundary]; decide) (ordinary first List.mem_cons_self)
  obtain ⟨low1, count1, current1, _, _⟩ := clock_boundary p s first c none boundary row reserve
  generalize ht1 : clock p first s = t1 at eq1 low1 count1 current1
  have lowLength : (rest.take c.lowDuration.val).length = c.lowDuration.val := by
    simp only [List.length_take, restLength]; omega
  obtain ⟨_, low2, count2, _, current2, _, _⟩ := low_hold p t1 low1 (rest.take c.lowDuration.val)
    (fun i mem => ordinaryRest i (List.mem_of_mem_take mem)) (by rw [count1, lowLength]; exact Nat.le_refl _)
  have unfold : t = run p t1 (rest.take c.lowDuration.val) := by
    simp only [t, List.take_succ_cons, run_cons, eq1]
  have current : t.current = .stream c none := by rw [unfold, current2, current1, row]
  have zero : t.countdown = 0 := zero_of_toNat _ (by rw [unfold, count2, count1, lowLength]; omega)
  have low : t.phase = .low := by rw [unfold]; exact low2
  refine ⟨low, zero, current, ?_, ?_⟩
  · simp [State.captures, low, zero, current, Instruction.isStream, Instruction.cell, Instruction.hasHighGuard]
  · let L := c.lowDuration.val
    have inside : L < (first :: rest).length := by simp only [List.length_cons]; omega
    have before : L - 1 < (first :: rest).length := by omega
    have split : (first :: rest).take (L + 1) =
        (first :: rest).take (L - 1) ++ [(first :: rest)[L - 1], (first :: rest)[L]] := by
      have previous := List.take_succ_eq_append_getElem (l := first :: rest) (i := L - 1) before
      rw [show L - 1 + 1 = L by omega] at previous
      rw [List.take_succ_eq_append_getElem inside, previous, List.append_assoc]
      rfl
    change (run p s ((first :: rest).take (L + 1))).samplerSecond = _
    rw [split]
    exact sampler_second p s _ _ _ (ordinary _ (List.getElem_mem before)) (ordinary _ (List.getElem_mem inside))

/-! ## Pulses, waits, fetch and halt -/

theorem low_hold_frame (p : Program) (s : State a) (low : s.phase = .low) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Ordinary i) (within : inputs.length ≤ s.countdown.toNat) :
    (run p s inputs).pc = s.pc := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have left : ¬ s.countdown = 0#8 := by
      intro zero; rw [zero] at positive; simp at positive
    have eq := step_clock p s i (by rw [low]; decide) (ordinary i List.mem_cons_self)
    have tick := clock_low_tick p s i low left
    have count := countdown_pred s.countdown positive
    have pc : (clock p i s).pc = s.pc := by simp [clock, engine, low, left]
    rw [run_cons, eq, ih _ tick.1 (fun j mem => ordinary j (List.mem_cons_of_mem _ mem))
      (by rw [tick.2.1, count]; simp only [List.length_cons] at within; omega), pc]

theorem high_hold_frame (p : Program) (s : State a) (high : s.phase = .high) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Ordinary i) (within : inputs.length ≤ s.countdown.toNat) :
    (run p s inputs).pc = s.pc := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have left : ¬ s.countdown = 0#8 := by
      intro zero; rw [zero] at positive; simp at positive
    have eq := step_clock p s i (by rw [high]; decide) (ordinary i List.mem_cons_self)
    have tick := clock_high_tick p s i high left
    have count := countdown_pred s.countdown positive
    have pc : (clock p i s).pc = s.pc := by simp [clock, engine, high, left]
    rw [run_cons, eq, ih _ tick.1 (fun j mem => ordinary j (List.mem_cons_of_mem _ mem))
      (by rw [tick.2.1, count]; simp only [List.length_cons] at within; omega), pc]

/-- FETCH of a pulse enters its boundary with the LOW pins. -/
theorem clock_fetch_pulse (p : Program) (s : State a) (i : Input) (c : Cell) (fetch : s.phase = .fetch)
    (row : p.fetch s.pc.toNat = some (.pulse c)) :
    let t := clock p i s
    t.phase = .boundary ∧ t.current = .pulse c ∧ t.pins = c.lowPins ∧ t.pc = s.pc ∧ t.remaining = s.remaining := by
  simp [clock, engine, fetch, row]

/-- A pulse boundary needs no credit and enters LOW with the LOW pins. -/
theorem clock_pulse_boundary (p : Program) (s : State a) (i : Input) (c : Cell) (boundary : s.phase = .boundary)
    (row : s.current = .pulse c) :
    let t := clock p i s
    t.phase = .low ∧ t.countdown.toNat = c.lowDuration.val ∧ t.pins = c.lowPins ∧ t.current = s.current ∧
      t.pc = s.pc ∧ t.remaining = s.remaining := by
  have reserve : s.canReserve = true := by simp [State.canReserve, row, Instruction.isStream]
  simp only [clock, engine, boundary, reserve, if_true, row, Instruction.isStream, Instruction.cell]
  refine ⟨by trivial, ?_, by simp, by trivial, by trivial, by trivial⟩
  first
    | (simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt c.lowDuration.isLt)
    | exact Nat.mod_eq_of_lt c.lowDuration.isLt

/-- The last LOW clock of a pulse enters HIGH with the HIGH pins. -/
theorem clock_pulse_low_exit (p : Program) (s : State a) (i : Input) (c : Cell) (low : s.phase = .low)
    (zero : s.countdown = 0) (row : s.current = .pulse c) :
    let t := clock p i s
    t.phase = .high ∧ t.countdown.toNat = c.highDuration.val ∧ t.pins = c.highPins ∧ t.current = s.current ∧
      t.pc = s.pc ∧ t.remaining = s.remaining := by
  simp only [clock, engine, low, zero, row, Instruction.hasHighGuard, State.enterHigh, State.captureData,
    State.highPins, Instruction.isStream, Instruction.cell]
  refine ⟨by trivial, ?_, by simp, by trivial, by trivial, by trivial⟩
  first
    | (simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt c.highDuration.isLt)
    | exact Nat.mod_eq_of_lt c.highDuration.isLt

/-- The last HIGH clock of a pulse fetches the next row with the LOW base pins. -/
theorem clock_pulse_high_exit (p : Program) (s : State a) (i : Input) (c : Cell) (high : s.phase = .high)
    (zero : s.countdown = 0) (row : s.current = .pulse c) :
    let t := clock p i s
    t.phase = .fetch ∧ t.pc = s.pc + 1 ∧ t.pins = c.basePins false false ∧ t.remaining = s.remaining := by
  simp [clock, engine, high, zero, row, Instruction.isStream, Instruction.cell, State.lastCell]

/-- A ready drive-and-wait row fetches the next row and keeps its pins. -/
theorem clock_wait_ready (p : Program) (s : State a) (i : Input) (pins : Pins) (g : Guard)
    (waiting : s.phase = .waiting) (row : s.current = .driveWait pins g) (ready : s.waitReady = true) :
    let t := clock p i s
    t.phase = .fetch ∧ t.pc = s.pc + 1 ∧ t.pins = s.pins ∧ t.remaining = s.remaining := by
  simp [clock, engine, waiting, ready, row, Instruction.isStream]

/-- FETCH of a stream row with cells left enters the boundary with its LOW base pins. -/
theorem clock_fetch_stream (p : Program) (s : State a) (i : Input) (c : Cell) (g : Option Guard)
    (fetch : s.phase = .fetch) (row : p.fetch s.pc.toNat = some (.stream c g)) (live : s.remaining ≠ 0) :
    (clock p i s).pins = c.basePins false (s.remaining == 1) := by
  have live' : ¬ s.remaining = 0#16 := live
  simp [clock, engine, fetch, row, live']

/-- FETCH of HALT drives the program's idle pins. -/
theorem clock_fetch_halt (p : Program) (s : State a) (i : Input) (fetch : s.phase = .fetch)
    (row : p.fetch s.pc.toNat = some .halt) :
    (clock p i s).pins = p.idle := by
  simp [clock, engine, fetch, row, State.stop]

private theorem pulse_list {α : Type} (L H : Nat) (x y b : α) :
    x :: (List.replicate L x ++ x :: (List.replicate H y ++ [y, b])) =
      List.replicate (L + 2) x ++ List.replicate (H + 1) y ++ [b] := by
  rw [List.replicate_succ, List.replicate_succ', List.replicate_succ']
  simp

/-- A whole pulse from its FETCH: the fetch observation, `L + 2` LOW-pin
observations (boundary and LOW), `H + 1` HIGH-pin observations, then the next
FETCH with the LOW base pins. -/
theorem pulse_window (p : Program) (s : State a) (c : Cell) (fetch : s.phase = .fetch)
    (row : p.fetch s.pc.toNat = some (.pulse c)) (inputs : List Input) (ordinary : ∀ i ∈ inputs, Ordinary i)
    (length : inputs.length = c.lowDuration.val + c.highDuration.val + 4) :
    pinTrace p s inputs =
      s.pins :: (List.replicate (c.lowDuration.val + 2) c.lowPins ++
        List.replicate (c.highDuration.val + 1) c.highPins ++ [c.basePins false false]) ∧
      (run p s inputs).phase = .fetch ∧ (run p s inputs).pc = s.pc + 1 ∧
      (run p s inputs).remaining = s.remaining ∧ (run p s inputs).pins = c.basePins false false := by
  obtain ⟨first, second, rest, rfl⟩ : ∃ first second rest, inputs = first :: second :: rest := by
    match inputs, length with
    | first :: second :: rest, _ => exact ⟨first, second, rest, rfl⟩
  have restLength : rest.length = c.lowDuration.val + c.highDuration.val + 2 := by
    simp only [List.length_cons] at length; omega
  have ordinaryRest : ∀ i ∈ rest, Ordinary i := fun i mem =>
    ordinary i (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem))
  have eq1 := step_clock p s first (by rw [fetch]; decide) (ordinary first List.mem_cons_self)
  obtain ⟨phase1, current1, pins1, pc1, remaining1⟩ := clock_fetch_pulse p s first c fetch row
  generalize ht1 : clock p first s = t1 at eq1 phase1 current1 pins1 pc1 remaining1
  have eq2 := step_clock p t1 second (by rw [phase1]; decide)
    (ordinary second (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨low2, count2, pins2, current2, pc2, remaining2⟩ := clock_pulse_boundary p t1 second c phase1 current1
  generalize ht2 : clock p second t1 = t2 at eq2 low2 count2 pins2 current2 pc2 remaining2
  let lowClocks := rest.take c.lowDuration.val
  let tail := rest.drop c.lowDuration.val
  have splitRest : rest = lowClocks ++ tail := (List.take_append_drop _ _).symm
  have lowLength : lowClocks.length = c.lowDuration.val := by
    simp only [lowClocks, List.length_take, restLength]; omega
  have tailLength : tail.length = c.highDuration.val + 2 := by simp [tail, restLength]; omega
  have ordinaryLow : ∀ i ∈ lowClocks, Ordinary i := fun i mem => ordinaryRest i (List.mem_of_mem_take mem)
  have ordinaryTail : ∀ i ∈ tail, Ordinary i := fun i mem => ordinaryRest i (List.mem_of_mem_drop mem)
  have lowPc := low_hold_frame p t2 low2 lowClocks ordinaryLow (by rw [count2, lowLength]; exact Nat.le_refl _)
  obtain ⟨lowTrace, low3, count3, pins3, current3, _, remaining3⟩ :=
    low_hold p t2 low2 lowClocks ordinaryLow (by rw [count2, lowLength]; exact Nat.le_refl _)
  generalize ht3 : run p t2 lowClocks = t3 at lowPc low3 count3 pins3 current3 remaining3
  have zero3 : t3.countdown = 0 := zero_of_toNat _ (by rw [count3, count2, lowLength]; omega)
  have row3 : t3.current = .pulse c := by rw [current3, current2, current1]
  obtain ⟨enter, highTail, tailEq, highTailLength⟩ : ∃ enter highTail, tail = enter :: highTail ∧
      highTail.length = c.highDuration.val + 1 := by
    match tail, tailLength with
    | enter :: highTail, h => exact ⟨enter, highTail, rfl, by simp only [List.length_cons] at h; omega⟩
  have eq4 := step_clock p t3 enter (by rw [low3]; decide) (ordinaryTail enter (by rw [tailEq]; exact List.mem_cons_self))
  obtain ⟨high4, count4, pins4, current4, pc4, remaining4⟩ := clock_pulse_low_exit p t3 enter c low3 zero3 row3
  generalize ht4 : clock p enter t3 = t4 at eq4 high4 count4 pins4 current4 pc4 remaining4
  obtain ⟨highClocks, exit, rfl, highLength⟩ : ∃ highClocks exit, highTail = highClocks ++ [exit] ∧
      highClocks.length = c.highDuration.val := by
    have nonempty : highTail ≠ [] := by intro nil; simp [nil] at highTailLength
    exact ⟨highTail.dropLast, highTail.getLast nonempty, (List.dropLast_concat_getLast nonempty).symm,
      by simp only [List.length_dropLast]; omega⟩
  have ordinaryHigh : ∀ i ∈ highClocks, Ordinary i := fun i mem =>
    ordinaryTail i (by rw [tailEq]; exact List.mem_cons_of_mem _ (List.mem_append_left _ mem))
  have ordinaryExit : Ordinary exit :=
    ordinaryTail exit (by rw [tailEq]; exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have highPc := high_hold_frame p t4 high4 highClocks ordinaryHigh (by rw [count4, highLength]; exact Nat.le_refl _)
  obtain ⟨highTrace, high5, count5, pins5, current5, remaining5⟩ :=
    high_hold p t4 high4 highClocks ordinaryHigh (by rw [count4, highLength]; exact Nat.le_refl _)
  generalize ht5 : run p t4 highClocks = t5 at highPc high5 count5 pins5 current5 remaining5
  have zero5 : t5.countdown = 0 := zero_of_toNat _ (by rw [count5, count4, highLength]; omega)
  have row5 : t5.current = .pulse c := by rw [current5, current4, row3]
  have eq6 := step_clock p t5 exit (by rw [high5]; decide) ordinaryExit
  obtain ⟨phase6, pc6, pins6, remaining6⟩ := clock_pulse_high_exit p t5 exit c high5 zero5 row5
  generalize ht6 : clock p exit t5 = t6 at eq6 phase6 pc6 pins6 remaining6
  have runAll : run p s (first :: second :: rest) = t6 := by
    rw [splitRest, tailEq, run_cons, eq1, run_cons, eq2, run_append, ht3, run_cons, eq4, run_append, ht5]
    change step p exit t5 = t6
    rw [eq6]
  refine ⟨?_, by rw [runAll]; exact phase6, by rw [runAll, pc6, highPc, pc4, lowPc, pc2, pc1],
    by rw [runAll, remaining6, remaining5, remaining4, remaining3, remaining2, remaining1],
    by rw [runAll, pins6]⟩
  rw [splitRest, tailEq]
  simp only [pinTrace, eq1, eq2, pinTrace_append, lowTrace, lowLength, List.take_replicate, ht3]
  rw [eq4, highTrace, highLength, List.take_replicate, ht5]
  change s.pins :: t1.pins :: (_ ++ (t3.pins :: (_ ++ [t5.pins, (step p exit t5).pins]))) = _
  rw [eq6, pins6, pins5, pins4, pins3, pins2, pins1, Nat.min_eq_left (Nat.le_succ _),
    Nat.min_eq_left (Nat.le_succ _)]
  rw [pulse_list]

end Pinwheel.Program.StreamingCellWaveform
