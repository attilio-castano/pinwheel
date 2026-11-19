import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingReadyTiming
import Pinwheel.Program.StreamingReadyBitTrace

/-! A transmit-only Ethernet serial interface. All timing is expressed in
project clock samples. An external PHY supplies the bit clock and performs
the line coding. -/
namespace Pinwheel.Program.StreamingEthernetCore
open StreamingReady

set_option linter.unusedSimpArgs false

def idlePins : Pins := ⟨0, 3⟩
def txPins (bit : Bool) : Pins := ⟨if bit then 3 else 2, 3⟩

def goGuard : Guard := {mask := 2, expected := 2}
def highGuard : Guard := {mask := 1, expected := 1}
def lowGuard : Guard := {mask := 1, expected := 0}

def txCell : Cell := {lowPins := txPins false, highPins := txPins false, transmit := true}
def streamRow : Instruction := .stream txCell (some highGuard)

def source : List Instruction :=
  [.driveWait idlePins goGuard, .driveWait idlePins highGuard, .driveWait idlePins lowGuard,
    .driveWait idlePins highGuard, streamRow, .halt]

theorem supported : Supported source := by decide +kernel

def image : Compiled source idlePins := ⟨source.map encode, supported, rfl⟩
abbrev program : Program := image.program

private theorem base_pins (high last : Bool) : txCell.basePins high last = txPins false := by
  cases high <;> cases last <;> rfl

private theorem data_pins (high last bit : Bool) : txCell.dataPins high last bit = txPins bit := by
  cases high <;> cases last <;> cases bit <;> rfl

private theorem ready_high (s : State a) (row : s.current = streamRow) :
    s.waitReady = s.samplerSecond[0] := by
  rw [State.waitReady, row]
  change highGuard.matches s.samplerSecond = s.samplerSecond[0]
  generalize s.samplerSecond = raw
  decide +revert +kernel

/-- The boundary immediately before a scheduled transmit reservation. -/
structure Boundary (s : State a) (n : Nat) : Prop where
  phase : s.phase = .boundary
  row : s.current = streamRow
  pc : s.pc = 4
  remaining : s.remaining.toNat = n
  positive : 0 < n
  pins : s.pins = txPins false

structure HaltReady (s : State a) : Prop where
  phase : s.phase = .fetch
  pc : s.pc = 5
  remaining : s.remaining = 0
  pins : s.pins = txPins false

private structure Held (s : State a) (phase : Phase) (n : Nat) (bit : Bool) : Prop where
  atPhase : s.phase = phase
  row : s.current = streamRow
  pc : s.pc = 4
  remaining : s.remaining.toNat = n
  timing : s.countdown = 0
  cellBit : s.cellBit = bit
  pins : s.pins = txPins bit

private theorem reserve (s : State a) (n : Nat) (i : Input) (runtime : i.Runtime)
    (position : Boundary s n) (credit : s.canReserve = true) :
    Held (step program i s) .low n s.selectedTx.data[31] := by
  rw [step_busy_eq_clock program s i runtime (by simp [position.phase, Phase.busy])]
  constructor <;> simp [clock, engine, position.phase, credit, position.row, position.pc,
    position.remaining, streamRow, Instruction.isStream, Instruction.cell, data_pins] <;> simp [txCell]

private theorem low_done (s : State a) (n : Nat) (bit : Bool) (i : Input) (runtime : i.Runtime)
    (held : Held s .low n bit) : Held (step program i s) .waiting n bit := by
  rw [step_busy_eq_clock program s i runtime (by simp [held.atPhase, Phase.busy])]
  constructor <;> simp [clock, engine, held.atPhase, held.timing, held.row, held.pc, held.remaining,
    held.cellBit, streamRow, Instruction.isStream, Instruction.cell, Instruction.hasHighGuard,
    Instruction.guard, highGuard, State.highPins, WaitLimit.initialCountdown, data_pins]

private theorem miss (s : State a) (n : Nat) (bit : Bool) (i : Input) (runtime : i.Runtime)
    (held : Held s .waiting n bit) (sample : s.samplerSecond[0] = false) :
    Held (step program i s) .waiting n bit := by
  rw [step_busy_eq_clock program s i runtime (by simp [held.atPhase, Phase.busy])]
  have missed : s.waitReady = false := (ready_high _ held.row).trans sample
  constructor <;> simp [clock, engine, held.atPhase, missed, held.timing, held.row, held.pc,
    held.remaining, held.cellBit, held.pins, streamRow, Instruction.guard, highGuard,
    WaitLimit.expires, WaitLimit.poll]

private theorem matched (s : State a) (n : Nat) (bit : Bool) (i : Input) (runtime : i.Runtime)
    (held : Held s .waiting n bit) (sample : s.samplerSecond[0] = true) :
    Held (step program i s) .high n bit := by
  rw [step_busy_eq_clock program s i runtime (by simp [held.atPhase, Phase.busy])]
  have ready : s.waitReady = true := (ready_high _ held.row).trans sample
  constructor <;> simp [clock, engine, held.atPhase, ready, held.row, held.pc, held.remaining,
    held.cellBit, held.pins, streamRow, Instruction.isStream, Instruction.cell, txCell,
    State.enterHigh, State.captureData]

private theorem high_done (s : State a) (n : Nat) (bit : Bool) (i : Input) (runtime : i.Runtime)
    (held : Held s .high n bit) (positive : 0 < n) :
    if 1 < n then Boundary (step program i s) (n - 1) else HaltReady (step program i s) := by
  rw [step_busy_eq_clock program s i runtime (by simp [held.atPhase, Phase.busy])]
  have remaining : (s.remaining - 1#16).toNat = n - 1 := by
    rw [BitVec.toNat_sub_of_le]
    · simp [held.remaining]
    · change 1 ≤ s.remaining.toNat
      rw [held.remaining]
      omega
  split
  · rename_i more
    constructor <;> try simp [clock, engine, held.atPhase, held.timing, held.row, held.pc, held.remaining,
      streamRow, Instruction.isStream, Instruction.cell, base_pins, more, remaining]
    all_goals omega
  · rename_i last
    have consumed : s.remaining - 1#16 = 0 := by
      apply BitVec.eq_of_toNat_eq
      change (s.remaining - 1#16).toNat = 0
      rw [remaining]
      omega
    constructor <;> simp [clock, engine, held.atPhase, held.timing, held.row, held.pc, held.remaining,
      streamRow, Instruction.isStream, Instruction.cell, base_pins, last, consumed]

private theorem busy_consumed (s : State a) (i : Input) (runtime : i.Runtime)
    (busy : s.phase.busy = true) (trace : BitTrace) :
    (trace.step s i).consumed = trace.consumed ++ s.txEvent := by
  have start : s.canStart i = false := by
    cases phase : s.phase <;> simp [Phase.busy, phase] at busy <;> simp [State.canStart, phase]
  have release : s.canRelease i = false := by
    cases phase : s.phase <;> simp [Phase.busy, phase] at busy <;>
      simp [State.canRelease, Phase.retained, phase]
  simp [BitTrace.step, BitTrace.clock, runtime.1, (show i.command ≠ 15#4 from runtime.2), start, release]

private theorem event_reserve (s : State a) (n : Nat) (position : Boundary s n)
    (credit : s.canReserve = true) : s.txEvent = [s.selectedTx.data[31]] := by
  simp [State.txEvent, State.consumes, position.phase, position.row, credit, streamRow,
    Instruction.isStream, Instruction.cell, txCell]

private theorem event_elsewhere (s : State a) (phase : s.phase ≠ .boundary) : s.txEvent = [] := by
  simp [State.txEvent, State.consumes, phase]

/-- The clocks from one TX reservation through the boundary before the next
reservation. The third raw slot is the independent PHY sampling edge. -/
structure CellInputs where
  reserve : Input
  low : Input
  sample : Input
  poll : Input
  ready : Input
  high : Input

def CellInputs.inputs (cell : CellInputs) : List Input :=
  [cell.reserve, cell.low, cell.sample, cell.poll, cell.ready, cell.high]

structure CellInputs.Timed (cell : CellInputs) : Prop where
  runtime : ∀ i ∈ cell.inputs, i.Runtime
  beforeSetup : cell.reserve.rawInputs[0] = false
  setup : cell.low.rawInputs[0] = false
  rise : cell.sample.rawInputs[0] = true

/-- A six-clock cell launches one data bit, holds it across the PHY sampling
edge, consumes that same single bit, and re-arms on time. Host queue service on
any ordinary clock is permitted. -/
theorem cell_exact (s : State a) (n : Nat) (cell : CellInputs) (trace : BitTrace)
    (position : Boundary s n) (credit : s.canReserve = true) (timed : cell.Timed) :
    let next := run program s cell.inputs
    let bit := s.selectedTx.data[31]
    (if 1 < n then Boundary next (n - 1) else HaltReady next) ∧
    pinTrace program s cell.inputs = [txPins false, txPins bit, txPins bit, txPins bit,
      txPins bit, txPins bit, txPins false] ∧
    (traceRun program s trace cell.inputs).consumed = trace.consumed ++ [bit] := by
  let s1 := step program cell.reserve s
  let s2 := step program cell.low s1
  let s3 := step program cell.sample s2
  let s4 := step program cell.poll s3
  let s5 := step program cell.ready s4
  let s6 := step program cell.high s5
  have r0 := timed.runtime cell.reserve (by simp [CellInputs.inputs])
  have r1 := timed.runtime cell.low (by simp [CellInputs.inputs])
  have r2 := timed.runtime cell.sample (by simp [CellInputs.inputs])
  have r3 := timed.runtime cell.poll (by simp [CellInputs.inputs])
  have r4 := timed.runtime cell.ready (by simp [CellInputs.inputs])
  have r5 := timed.runtime cell.high (by simp [CellInputs.inputs])
  have h1 := reserve s n cell.reserve r0 position credit
  have h2 := low_done s1 n _ cell.low r1 h1
  have raw2 : s2.samplerSecond[0] = false := by
    change (step program cell.low s1).samplerSecond[0] = false
    rw [(step_samples program s1 cell.low r1).2, (step_samples program s cell.reserve r0).1]
    exact timed.beforeSetup
  have h3 := miss s2 n _ cell.sample r2 h2 raw2
  have raw3 : s3.samplerSecond[0] = false := by
    change (step program cell.sample s2).samplerSecond[0] = false
    rw [(step_samples program s2 cell.sample r2).2, (step_samples program s1 cell.low r1).1]
    exact timed.setup
  have h4 := miss s3 n _ cell.poll r3 h3 raw3
  have raw4 : s4.samplerSecond[0] = true := by
    change (step program cell.poll s3).samplerSecond[0] = true
    rw [(step_samples program s3 cell.poll r3).2, (step_samples program s2 cell.sample r2).1]
    exact timed.rise
  have h5 := matched s4 n _ cell.ready r4 h4 raw4
  have ending := high_done s5 n _ cell.high r5 h5 position.positive
  have pins6 : s6.pins = txPins false := by
    by_cases more : 1 < n
    · rw [if_pos more] at ending
      exact ending.pins
    · rw [if_neg more] at ending
      exact ending.pins
  refine ⟨ending, ?_, ?_⟩
  · change [s.pins, s1.pins, s2.pins, s3.pins, s4.pins, s5.pins, s6.pins] = _
    rw [position.pins, h1.pins, h2.pins, h3.pins, h4.pins, h5.pins, pins6]
  · let t1 := trace.step s cell.reserve
    let t2 := t1.step s1 cell.low
    let t3 := t2.step s2 cell.sample
    let t4 := t3.step s3 cell.poll
    let t5 := t4.step s4 cell.ready
    have p1 : s1.phase = .low := h1.atPhase
    have p2 : s2.phase = .waiting := h2.atPhase
    have p3 : s3.phase = .waiting := h3.atPhase
    have p4 : s4.phase = .waiting := h4.atPhase
    have p5 : s5.phase = .high := h5.atPhase
    change (t5.step s5 cell.high).consumed = _
    rw [busy_consumed s5 cell.high r5 (by simp [p5, Phase.busy]),
      event_elsewhere s5 (by simp [p5]), List.append_nil]
    change (t4.step s4 cell.ready).consumed = _
    rw [busy_consumed s4 cell.ready r4 (by simp [p4, Phase.busy]),
      event_elsewhere s4 (by simp [p4]), List.append_nil]
    change (t3.step s3 cell.poll).consumed = _
    rw [busy_consumed s3 cell.poll r3 (by simp [p3, Phase.busy]),
      event_elsewhere s3 (by simp [p3]), List.append_nil]
    change (t2.step s2 cell.sample).consumed = _
    rw [busy_consumed s2 cell.sample r2 (by simp [p2, Phase.busy]),
      event_elsewhere s2 (by simp [p2]), List.append_nil]
    change (t1.step s1 cell.low).consumed = _
    rw [busy_consumed s1 cell.low r1 (by simp [p1, Phase.busy]),
      event_elsewhere s1 (by simp [p1]), List.append_nil]
    change (trace.step s cell.reserve).consumed = _
    rw [busy_consumed s cell.reserve r0 (by simp [position.phase, Phase.busy]),
      event_reserve s n position credit]

/-- HALT removes TX_EN between the final sampling edge and the next PHY bit. -/
theorem halt_exact (s : State a) (i : Input) (trace : BitTrace)
    (position : HaltReady s) (runtime : i.Runtime) :
    (step program i s).phase = .completed ∧ (step program i s).pins = idlePins ∧
      (trace.step s i).consumed = trace.consumed := by
  have busy : s.phase.busy = true := by simp [position.phase, Phase.busy]
  have halt : program.fetch 5 = some .halt := image.program_fetch 5 (by decide +kernel)
  refine ⟨?_, ?_, ?_⟩
  · rw [step_busy_eq_clock program s i runtime busy]
    simp [clock, engine, position.phase, position.pc, halt, State.stop]
  · rw [step_busy_eq_clock program s i runtime busy]
    simp [clock, engine, position.phase, position.pc, halt, State.stop]
    rfl
  · rw [busy_consumed s i runtime busy, event_elsewhere s (by simp [position.phase]), List.append_nil]

end Pinwheel.Program.StreamingEthernetCore
