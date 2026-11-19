import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingUARTQuiet

/-! Receive-only PS/2 image and exact timing through the sampled-ready engine. -/
namespace Pinwheel.Program.StreamingPS2Core
open StreamingReady
open StreamingUART.QuietTiming

set_option linter.unusedSimpArgs false

def idlePins : Pins := {}

/-- Both pads stay released. Each capture starts a 217-clock HIGH phase. -/
def cell : Cell :=
  { lowDuration := 0, highDuration := 216, receive := true, rxInput := 1 }

/-- WAIT qualifies the sampled low level on CLK and can poll indefinitely. -/
def guard : Guard := { mask := 1 }

def streamRow : Instruction := .stream cell (some guard)

def source : List Instruction := [streamRow, .halt]

theorem supported : Supported source := by decide +kernel

def image : Compiled source idlePins := ⟨source.map encode, supported, rfl⟩

abbrev program : Program := image.program

def startCycles : Nat := 3
def rearmCycles : Nat := 220
def finishCycles : Nat := 219

/-- At WAIT, the remaining cells and the partial RX word account for all eleven bits. -/
structure Armed (s : State a) (remaining : Nat) : Prop where
  phase : s.phase = .waiting
  current : s.current = streamRow
  pc : s.pc = 0
  countdown : s.countdown = 0
  pins : s.pins = idlePins
  count : s.remaining.toNat = remaining
  positive : 0 < remaining
  room : s.rx.count.val = 0
  budget : s.rxUsed.toNat + remaining = 11
  aligned : s.rx.head = s.rx.tail

private theorem fetch_first : program.fetch 0 = some streamRow :=
  image.program_fetch 0 (by decide +kernel)

private theorem fetch_halt : program.fetch 1 = some .halt :=
  image.program_fetch 1 (by decide +kernel)

private theorem match_clock (raw : BitVec 2) : guard.matches raw = !raw[0] := by
  decide +revert +kernel

private theorem release_base (high last : Bool) :
    cell.basePins high last = idlePins := by
  cases high <;> cases last <;> rfl

private theorem release_data (high last bit : Bool) :
    cell.dataPins high last bit = idlePins := by
  cases high <;> cases last <;> cases bit <;> rfl

private theorem queue_idle (q : Queue a) : q.tick none false = q := by
  cases q
  simp [Streaming.Queue.tick, Streaming.Queue.willPush, Streaming.Queue.willPop]

private theorem no_host_push (s : State a) (i : Input) (quiet : Quiet i) :
    s.hostPush i = none := by
  simp [State.hostPush, quiet.tx]

private theorem no_host_pop (s : State a) (i : Input) (quiet : Quiet i) :
    s.hostPop i = false := by
  simp [State.hostPop, quiet.rx]

private theorem read_clock (s : State a) (row : s.current = streamRow) :
    s.waitReady = !s.samplerSecond[0] := by
  rw [State.waitReady, row]
  exact match_clock _

theorem armed_capture (s : State a) (n : Nat) (armed : Armed s n)
    (ready : s.samplerSecond[0] = false) :
    s.rxEvent = [s.samplerSecond[1]] := by
  have matched := read_clock s armed.current
  rw [ready] at matched
  simp [State.rxEvent, State.captures, armed.phase, armed.current, matched, streamRow,
    Instruction.cell, Instruction.isStream, cell]

theorem quiet_trace_edge (s : State a) (trace : BitTrace) (i : Input) (quiet : Quiet i) :
    (trace.step s i).captured = trace.captured ++ s.rxEvent := by
  simp [BitTrace.step, BitTrace.clock, quiet.cold, quiet.command]

theorem trace_append (s : State a) (trace : BitTrace) (before after : List Input) :
    traceRun program s trace (before ++ after) =
      traceRun program (run program s before) (traceRun program s trace before) after := by
  induction before generalizing s trace with
  | nil => rfl
  | cons i rest ih => exact ih (step program i s) (trace.step s i)

private theorem wait_miss_step (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .waiting) (row : s.current = streamRow)
    (miss : s.samplerSecond[0] = true) :
    step program i s = s.sample i.rawInputs := by
  have missed : s.waitReady = false := by rw [read_clock s row, miss]; rfl
  simp [quiet_clock program s i quiet, clock, engine, phase, row, missed, streamRow,
    Instruction.guard, guard, WaitLimit.expires, WaitLimit.poll, no_host_pop s i quiet,
    no_host_push s i quiet, State.enginePop, State.enginePush, State.timedOut, State.emittingCapture,
    State.captures, State.sample, queue_idle, Streaming.Queue.willPush, Streaming.Queue.willPop,
    Bool.beq_eq_decide_eq]

theorem wait_miss (s : State a) (n : Nat) (armed : Armed s n) (i : Input) (quiet : Quiet i)
    (miss : s.samplerSecond[0] = true) :
    Armed (step program i s) n ∧ s.rxEvent = [] := by
  constructor
  · rw [wait_miss_step s i quiet armed.phase armed.current miss]
    exact ⟨armed.phase, armed.current, armed.pc, armed.countdown, armed.pins, armed.count,
      armed.positive, armed.room, armed.budget, armed.aligned⟩
  · have missed : s.waitReady = false := by rw [read_clock s armed.current, miss]; rfl
    simp [State.rxEvent, State.captures, armed.phase, missed]

private def captureChunk (s : State a) : Chunk :=
  ⟨s.capturedWord, ⟨s.rxUsed.toNat % 32, Nat.mod_lt _ (by decide)⟩⟩

private def capturedHigh (s : State a) (n : Nat) (raw : BitVec 2) : State a :=
  {s.sample raw with
    phase := .high
    countdown := 216
    rxPartial := if n = 1 then 0 else s.capturedWord
    rxUsed := if n = 1 then 0 else s.rxUsed + 1
    rxProduced := s.rxProduced + 1
    rx := s.rx.tick (if n = 1 then some (captureChunk s) else none) false}

private theorem ready_step (s : State a) (n : Nat) (armed : Armed s n) (i : Input)
    (quiet : Quiet i) (ready : s.samplerSecond[0] = false) :
    step program i s = capturedHigh s n i.rawInputs := by
  have matched : s.waitReady = true := by rw [read_clock s armed.current, ready]; rfl
  have used : s.rxUsed ≠ 31#6 := by
    have h := armed.budget
    intro eq
    simp [eq] at h
    omega
  have last : s.remaining = 1#16 ↔ n = 1 := by
    rw [← armed.count]
    exact ⟨fun h => by simp [h], fun h => BitVec.eq_of_toNat_eq h⟩
  simp [quiet_clock program s i quiet, clock, engine, armed.phase, armed.current, matched,
    State.enterHigh, State.captureData, State.emittingCapture, State.captures, State.enginePush,
    State.timedOut, State.enginePop, State.sample, no_host_push s i quiet, no_host_pop s i quiet,
    queue_idle, Streaming.Queue.willPush, Streaming.Queue.willPop, streamRow, Instruction.isStream,
    Instruction.cell, cell, last, used, Bool.beq_eq_decide_eq, capturedHigh, captureChunk]

private theorem reserve_step (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .boundary) (row : s.current = streamRow) (room : s.rx.count.val = 0) :
    step program i s = {s.sample i.rawInputs with
      phase := .low, countdown := 0, cellBit := false, pins := idlePins} := by
  have available : s.rx.writable = true := by
    simp [Streaming.Queue.writable, room, Streaming.queueDepth_positive]
  simp [quiet_clock program s i quiet, clock, engine, phase, row, State.canReserve,
    State.txReady, State.rxReady, available, State.enginePop, State.enginePush, State.timedOut,
    State.emittingCapture, State.captures, State.sample, State.lastCell,
    no_host_push s i quiet, no_host_pop s i quiet, queue_idle,
    Streaming.Queue.willPush, Streaming.Queue.willPop, streamRow, Instruction.cell,
    Instruction.isStream, cell, Bool.beq_eq_decide_eq]
  exact release_data false _ false

private theorem arm_step (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .low) (row : s.current = streamRow) (zero : s.countdown = 0) :
    step program i s = {s.sample i.rawInputs with
      phase := .waiting, countdown := 0, pins := idlePins} := by
  simp [quiet_clock program s i quiet, clock, engine, phase, row, zero, State.highPins,
    State.lastCell, State.enginePop, State.enginePush, State.timedOut, State.emittingCapture,
    State.captures, State.sample, no_host_push s i quiet, no_host_pop s i quiet,
    queue_idle, Streaming.Queue.willPush, Streaming.Queue.willPop, streamRow,
    Instruction.isStream, Instruction.cell, Instruction.hasHighGuard, Instruction.guard,
    guard, WaitLimit.initialCountdown, Bool.beq_eq_decide_eq, release_data]

private theorem no_event_other (s : State a) (low : s.phase ≠ .low)
    (waiting : s.phase ≠ .waiting) : s.rxEvent = [] := by
  simp [State.rxEvent, State.captures, low, waiting]

private theorem no_event_low (s : State a) (phase : s.phase = .low)
    (row : s.current = streamRow) : s.rxEvent = [] := by
  simp [State.rxEvent, State.captures, phase, row, streamRow, Instruction.hasHighGuard]

private theorem enter_step (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .fetch) (pc : s.pc = 0) (count : s.remaining ≠ 0#16) :
    step program i s =
      {s.sample i.rawInputs with phase := .boundary, current := streamRow, pins := idlePins} := by
  have fetch : program.fetch s.pc.toNat = some streamRow := by simpa [pc] using fetch_first
  simp [quiet_clock program s i quiet, clock, engine, phase, fetch, count,
    no_host_pop s i quiet, no_host_push s i quiet, State.enginePop, State.enginePush,
    State.timedOut, State.emittingCapture, State.captures, State.sample, queue_idle,
    Streaming.Queue.willPush, Streaming.Queue.willPop, streamRow, release_base, Bool.beq_eq_decide_eq]

private theorem leave_step (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .high) (row : s.current = streamRow) (zero : s.countdown = 0) :
    step program i s =
      {s.sample i.rawInputs with
        phase := if s.remaining.toNat > 1 then .boundary else .fetch
        pc := if s.remaining.toNat > 1 then s.pc else s.pc + 1
        remaining := s.remaining - 1
        pins := idlePins} := by
  rw [high_step program s i quiet phase zero]
  simp [highExit, State.sample, row, streamRow, Instruction.isStream, Instruction.cell, release_base]

private theorem halt_step (s : State a) (i : Input) (quiet : Quiet i)
    (phase : s.phase = .fetch) (pc : s.pc = 1) :
    step program i s = {s.sample i.rawInputs with phase := .completed, pins := idlePins} := by
  have fetch : program.fetch s.pc.toNat = some .halt := by simpa [pc] using fetch_halt
  simp [quiet_clock program s i quiet, clock, engine, phase, fetch, no_host_pop s i quiet,
    no_host_push s i quiet, State.enginePop, State.enginePush, State.timedOut, State.emittingCapture,
    State.captures, State.sample, State.stop, queue_idle, Streaming.Queue.willPush,
    Streaming.Queue.willPop, Bool.beq_eq_decide_eq]
  rfl

private theorem high_hold_observations (s : State a) (trace : BitTrace) (inputs : List Input)
    (phase : s.phase = .high) (pins : s.pins = idlePins)
    (quiet : ∀ i ∈ inputs, Quiet i) (within : inputs.length ≤ s.countdown.toNat) :
    (traceRun program s trace inputs).captured = trace.captured ∧
      pinTrace program s inputs = List.replicate (inputs.length + 1) idlePins := by
  induction inputs generalizing s trace with
  | nil => simp [traceRun, pinTrace, pins]
  | cons i rest ih =>
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have nonzero : s.countdown ≠ 0#8 := by intro z; simp [z] at positive
    have q := quiet i (by simp)
    have next := timed_step program s i q (Or.inr phase) nonzero
    have subtract : (s.countdown - 1#8).toNat = s.countdown.toNat - 1 :=
      BitVec.toNat_sub_of_le (by change 1 ≤ s.countdown.toNat; omega)
    have recur := ih (step program i s) (trace.step s i)
      (by rw [next]; exact phase) (by rw [next]; exact pins)
      (fun j mem => quiet j (by simp [mem])) (by
        rw [next]
        change rest.length ≤ (s.countdown - 1#8).toNat
        rw [subtract]
        simp only [List.length_cons] at within
        omega)
    have empty := no_event_other s (by simp [phase]) (by simp [phase])
    simpa [traceRun, quiet_trace_edge s trace i q, empty, pinTrace, pins, List.replicate_succ]
      using recur

private theorem pin_append (s : State a) (before after : List Input) :
    pinTrace program s (before ++ after) =
      (pinTrace program s before).take before.length ++ pinTrace program (run program s before) after := by
  induction before generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.cons_append, pinTrace, List.length_cons, List.take_succ_cons]
    rw [ih]
    rfl

private theorem pins_append_released (s : State a) (before after : List Input)
    (first : pinTrace program s before = List.replicate (before.length + 1) idlePins)
    (second : pinTrace program (run program s before) after =
      List.replicate (after.length + 1) idlePins) :
    pinTrace program s (before ++ after) = List.replicate ((before ++ after).length + 1) idlePins := by
  rw [pin_append, first, second]
  simp [List.take_replicate, List.replicate_append_replicate, Nat.add_assoc]

private theorem capture_hold (s : State a) (n : Nat) (armed : Armed s n) (trace : BitTrace)
    (edge : Input) (hold : List Input) (ready : s.samplerSecond[0] = false)
    (quiet : ∀ i ∈ edge :: hold, Quiet i) (length : hold.length = 216) :
    let inputs := edge :: hold
    run program s inputs =
      {sampleInputs (capturedHigh s n edge.rawInputs) hold with countdown := 0} ∧
      (traceRun program s trace inputs).captured = trace.captured ++ [s.samplerSecond[1]] ∧
      pinTrace program s inputs = List.replicate (inputs.length + 1) idlePins := by
  let high := step program edge s
  have q := quiet edge (by simp)
  have enter : high = capturedHigh s n edge.rawInputs := ready_step s n armed edge q ready
  have phase : high.phase = .high := by rw [enter]; rfl
  have highPins : high.pins = idlePins := by rw [enter]; exact armed.pins
  have clocks : high.countdown.toNat = 216 := by rw [enter]; rfl
  have quietHold j (mem : j ∈ hold) : Quiet j := quiet j (by simp [mem])
  have within : hold.length ≤ high.countdown.toNat := by simp [length, clocks]
  obtain ⟨capture, pins⟩ := high_hold_observations high (trace.step s edge) hold
    phase highPins quietHold within
  dsimp only
  change run program high hold = _ ∧
    (traceRun program high (trace.step s edge) hold).captured = _ ∧
    s.pins :: pinTrace program high hold = _
  refine ⟨?_, ?_, ?_⟩
  · rw [timed_prefix program high hold (Or.inr phase) quietHold within, clocks, length, Nat.sub_self]
    rw [enter]
    rfl
  · rw [capture, quiet_trace_edge s trace edge q, armed_capture s n armed ready]
  · simp [armed.pins, pins, List.replicate_succ]

private theorem capture_leave (s : State a) (n : Nat) (armed : Armed s n) (trace : BitTrace)
    (edge : Input) (hold : List Input) (leave : Input) (ready : s.samplerSecond[0] = false)
    (quiet : ∀ i ∈ (edge :: hold) ++ [leave], Quiet i) (length : hold.length = 216) :
    let inputs := (edge :: hold) ++ [leave]
    let sampled := (sampleInputs (capturedHigh s n edge.rawInputs) hold).sample leave.rawInputs
    run program s inputs = {sampled with
      phase := if n > 1 then .boundary else .fetch
      pc := if n > 1 then 0 else 1
      remaining := s.remaining - 1
      countdown := 0
      pins := idlePins} ∧
      (traceRun program s trace inputs).captured = trace.captured ++ [s.samplerSecond[1]] ∧
      pinTrace program s inputs = List.replicate (inputs.length + 1) idlePins := by
  let before := edge :: hold
  let cut := run program s before
  obtain ⟨held, capture, pins⟩ := capture_hold s n armed trace edge hold ready
    (fun i mem => quiet i (List.mem_append_left _ mem)) length
  change cut = _ at held
  have phase : cut.phase = .high := by rw [held]; simp [capturedHigh]
  have row : cut.current = streamRow := by rw [held]; simpa [capturedHigh, State.sample] using armed.current
  have leaveQuiet := quiet leave (by simp)
  have released := leave_step cut leave leaveQuiet phase row (by rw [held])
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [run_append]
    change step program leave cut = _
    rw [released, held, sampleInputs_eq (capturedHigh s n edge.rawInputs) hold]
    simp [State.sample, capturedHigh, armed.count, armed.pc]
  · rw [trace_append]
    change ((traceRun program s trace before).step cut leave).captured = _
    rw [quiet_trace_edge cut _ leave leaveQuiet, no_event_other cut (by simp [phase]) (by simp [phase])]
    simpa using capture
  · apply pins_append_released s before [leave] pins
    change cut.pins :: (step program leave cut).pins :: [] = _
    rw [released, held, sampleInputs_eq (capturedHigh s n edge.rawInputs) hold]
    simp [capturedHigh, State.sample, armed.pins, List.replicate_succ]

private theorem boundary_wait (s : State a) (n : Nat) (trace : BitTrace) (reserve arm : Input)
    (reserveQuiet : Quiet reserve) (armQuiet : Quiet arm) (phase : s.phase = .boundary)
    (row : s.current = streamRow) (pc : s.pc = 0) (pins : s.pins = idlePins)
    (count : s.remaining.toNat = n) (positive : 0 < n) (room : s.rx.count.val = 0)
    (budget : s.rxUsed.toNat + n = 11) (aligned : s.rx.head = s.rx.tail) :
    Armed (run program s [reserve, arm]) n ∧
      (traceRun program s trace [reserve, arm]).captured = trace.captured ∧
      pinTrace program s [reserve, arm] = List.replicate 3 idlePins := by
  let low := step program reserve s
  have lowState : low = _ := reserve_step s reserve reserveQuiet phase row room
  have lowPhase : low.phase = .low := by rw [lowState]
  have lowRow : low.current = streamRow := by rw [lowState]; exact row
  have waitState := arm_step low arm armQuiet lowPhase lowRow (by rw [lowState])
  change Armed (step program arm low) n ∧
    ((trace.step s reserve).step low arm).captured = trace.captured ∧
    s.pins :: low.pins :: (step program arm low).pins :: [] = _
  refine ⟨?_, ?_, ?_⟩
  · rw [waitState, lowState]
    exact ⟨rfl, row, pc, rfl, rfl, count, positive, room, budget, aligned⟩
  · simp [quiet_trace_edge, reserveQuiet, armQuiet, no_event_low low lowPhase lowRow,
      no_event_other s (by simp [phase]) (by simp [phase])]
  · rw [waitState, lowState, pins]
    rfl

private theorem split_suffix (inputs : List Input) (n m : Nat) (length : inputs.length = n + m) :
    ∃ before after, inputs = before ++ after ∧ before.length = n ∧ after.length = m := by
  refine ⟨inputs.take n, inputs.drop n, (List.take_append_drop n inputs).symm, ?_, ?_⟩
  · simp [List.length_take, length]
  · simp [List.length_drop, length]

/-- Fetch, reserve, and one LOW clock put an accepted eleven-bit START at WAIT. -/
theorem started_waiting (before : State a) (start : Input) (inputs : List Input)
    (count : start.startCount = 11#16) (quiet : ∀ i ∈ inputs, Quiet i)
    (length : inputs.length = startCycles) :
    let seed := before.start program start
    Armed (run program seed inputs) 11 ∧
      (traceRun program seed {} inputs).captured = [] ∧
      pinTrace program seed inputs = List.replicate (inputs.length + 1) idlePins := by
  simp only [startCycles] at length
  rcases inputs with _ | ⟨first, _ | ⟨reserve, _ | ⟨arm, _ | ⟨extra, rest⟩⟩⟩⟩ <;> simp at length
  let seed := before.start program start
  let boundary := step program first seed
  have firstQuiet := quiet first (by simp)
  have setup : boundary = _ := enter_step seed first firstQuiet rfl rfl (by simp [seed, State.start, count])
  have phase : boundary.phase = .boundary := by rw [setup]
  have row : boundary.current = streamRow := by rw [setup]
  have pins : boundary.pins = idlePins := by rw [setup]
  have cells : boundary.remaining.toNat = 11 := by rw [setup]; simp [State.sample, seed, State.start, count]
  let trace := StreamingReady.BitTrace.step ({} : BitTrace) seed first
  have entered := boundary_wait boundary 11 trace reserve arm (quiet reserve (by simp))
    (quiet arm (by simp)) phase row (by rw [setup]; rfl) pins cells (by decide)
    (by rw [setup]; rfl) (by rw [setup]; rfl) (by rw [setup]; rfl)
  change Armed (run program boundary [reserve, arm]) 11 ∧
    (traceRun program boundary trace [reserve, arm]).captured = [] ∧
    seed.pins :: pinTrace program boundary [reserve, arm] = List.replicate 4 idlePins
  refine ⟨entered.1, ?_, ?_⟩
  · rw [entered.2.1]
    dsimp only [trace]
    rw [quiet_trace_edge seed {} first firstQuiet, no_event_other seed (by simp [seed, State.start]) (by simp [seed, State.start])]
    rfl
  · rw [entered.2.2]
    rfl

/-- The capture clock, 217 HIGH clocks, reserve, and LOW return to WAIT. -/
theorem capture_rearm (s : State a) (n : Nat) (armed : Armed s n) (trace : BitTrace)
    (edge : Input) (tail : List Input) (ready : s.samplerSecond[0] = false)
    (quiet : ∀ i ∈ edge :: tail, Quiet i) (length : tail.length = rearmCycles - 1) (more : 1 < n) :
    let inputs := edge :: tail
    Armed (run program s inputs) (n - 1) ∧
      (traceRun program s trace inputs).captured = trace.captured ++ [s.samplerSecond[1]] ∧
      pinTrace program s inputs = List.replicate (tail.length + 2) idlePins := by
  obtain ⟨hold, suffix, parts, holdLength, suffixLength⟩ := split_suffix tail 216 3 length
  rcases suffix with _ | ⟨leave, _ | ⟨reserve, _ | ⟨arm, _ | ⟨extra, rest⟩⟩⟩⟩ <;> simp at suffixLength
  subst tail
  let pre := (edge :: hold) ++ [leave]
  let boundary := run program s pre
  have decomposition : edge :: (hold ++ [leave, reserve, arm]) = pre ++ [reserve, arm] := by
    simp [pre, List.append_assoc]
  rw [decomposition] at quiet
  obtain ⟨state, captured, pins⟩ := capture_leave s n armed trace edge hold leave ready
    (fun i mem => quiet i (List.mem_append_left _ mem)) holdLength
  change boundary = _ at state
  simp only [more, if_true] at state
  have nonlast : n ≠ 1 := by omega
  have sameQueue : boundary.rx = s.rx := by
    rw [state, sampleInputs_eq (capturedHigh s n edge.rawInputs) hold]
    simp [State.sample, capturedHigh, nonlast, queue_idle]
  have decreased : boundary.remaining.toNat = n - 1 := by
    rw [state]
    change (s.remaining - 1#16).toNat = n - 1
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, armed.count]; exact Nat.le_of_lt more)]
    rw [armed.count]
    rfl
  have used : boundary.rxUsed.toNat = s.rxUsed.toNat + 1 := by
    have bound := armed.budget
    rw [state, sampleInputs_eq (capturedHigh s n edge.rawInputs) hold]
    simp only [State.sample, capturedHigh, nonlast, if_false]
    exact BitVec.toNat_add_of_lt (by change s.rxUsed.toNat + 1 < 64; omega)
  have enough : boundary.rxUsed.toNat + (n - 1) = 11 := by rw [used]; have := armed.budget; omega
  let preTrace := traceRun program s trace pre
  have armedAgain := boundary_wait boundary (n - 1) preTrace reserve arm
    (quiet reserve (by simp [pre])) (quiet arm (by simp [pre]))
    (by rw [state]) (by
      rw [state, sampleInputs_eq (capturedHigh s n edge.rawInputs) hold]
      exact armed.current)
    (by rw [state]) (by rw [state]) decreased (by omega)
    (by rw [sameQueue]; exact armed.room) enough (by rw [sameQueue]; exact armed.aligned)
  dsimp only
  rw [decomposition, run_append, trace_append]
  refine ⟨armedAgain.1, armedAgain.2.1.trans captured, ?_⟩
  have result := pins_append_released s pre [reserve, arm] pins armedAgain.2.2
  simpa [pre, Nat.add_assoc] using result

/-- The last sample flushes the eleven-bit RX chunk. HIGH and HALT finish the transfer. -/
theorem capture_complete (s : State a) (armed : Armed s 1) (trace : BitTrace)
    (edge : Input) (tail : List Input) (ready : s.samplerSecond[0] = false)
    (quiet : ∀ i ∈ edge :: tail, Quiet i) (length : tail.length = finishCycles - 1) :
    let inputs := edge :: tail
    let final := run program s inputs
    final.phase = .completed ∧ final.rx.count.val = 1 ∧ final.rx.peek.validBits = 11 ∧
      (traceRun program s trace inputs).captured = trace.captured ++ [s.samplerSecond[1]] ∧
      pinTrace program s inputs = List.replicate (tail.length + 2) idlePins := by
  obtain ⟨hold, suffix, parts, holdLength, suffixLength⟩ := split_suffix tail 216 2 length
  rcases suffix with _ | ⟨leave, _ | ⟨halt, _ | ⟨extra, rest⟩⟩⟩ <;> simp at suffixLength
  subst tail
  let pre := (edge :: hold) ++ [leave]
  let fetch := run program s pre
  have decomposition : edge :: (hold ++ [leave, halt]) = pre ++ [halt] := by
    simp [pre, List.append_assoc]
  rw [decomposition] at quiet
  obtain ⟨state, captured, pins⟩ := capture_leave s 1 armed trace edge hold leave ready
    (fun i mem => quiet i (List.mem_append_left _ mem)) holdLength
  change fetch = _ at state
  have phase : fetch.phase = .fetch := by rw [state]; rfl
  have pc : fetch.pc = 1 := by rw [state]; rfl
  have released : fetch.pins = idlePins := by rw [state]
  have haltQuiet := quiet halt (by simp [pre])
  have complete := halt_step fetch halt haltQuiet phase pc
  have retained : fetch.rx = s.rx.tick (some (captureChunk s)) false := by
    rw [state, sampleInputs_eq (capturedHigh s 1 edge.rawInputs) hold]
    rfl
  have room : s.rx.writable = true := by
    simp [Streaming.Queue.writable, armed.room, Streaming.queueDepth_positive]
  have one : (s.rx.tick (some (captureChunk s)) false).count.val = 1 := by
    simp [Streaming.Queue.tick, Streaming.Queue.willPush, Streaming.Queue.willPop, room, armed.room]
  have chunk : (s.rx.tick (some (captureChunk s)) false).peek = captureChunk s := by
    simp [Streaming.Queue.peek, Streaming.Queue.tick, Streaming.Queue.willPush, Streaming.Queue.willPop,
      room, armed.aligned]
  have eleven : (captureChunk s).validBits = 11 := by
    have used : s.rxUsed.toNat = 10 := by have := armed.budget; omega
    simp [captureChunk, Streaming.Chunk.validBits, used]
    rfl
  dsimp only
  rw [decomposition, run_append, trace_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (step program halt fetch).phase = _
    rw [complete]
  · change (step program halt fetch).rx.count.val = _
    rw [complete]
    change fetch.rx.count.val = _
    exact congrArg (fun q : Queue a => q.count.val) retained |>.trans one
  · change (step program halt fetch).rx.peek.validBits = _
    rw [complete]
    change fetch.rx.peek.validBits = _
    rw [retained, chunk, eleven]
  · change ((traceRun program s trace pre).step fetch halt).captured = _
    rw [quiet_trace_edge fetch _ halt haltQuiet,
      no_event_other fetch (by simp [phase]) (by simp [phase]), List.append_nil]
    exact captured
  · have lastPins : pinTrace program fetch [halt] = List.replicate 2 idlePins := by
      change fetch.pins :: (step program halt fetch).pins :: [] = _
      rw [complete, released]
      rfl
    have result := pins_append_released s pre [halt] pins lastPins
    simpa [pre, Nat.add_assoc] using result

end Pinwheel.Program.StreamingPS2Core
