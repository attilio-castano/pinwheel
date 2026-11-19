import Pinwheel.Program.StreamingSPI
import Pinwheel.Program.StreamingReadyBitTrace

/-! SPI's transmit reservation, physical leading edge, and delayed receive aperture. -/
namespace Pinwheel.Program.StreamingSPI
open StreamingReady

private def mosiEdge (mode : Mode) (before after : Pins) : List Bool :=
  if leading mode before after then [after.levels[0]] else []

private def misoEdge (mode : Mode) (before after : Pins) (raw : BitVec 2) : List Bool :=
  if leading mode before after then [raw[0]] else []

/-- The physical MOSI value at each leading SCK edge. -/
def mosiOnLeading (mode : Mode) : List Pins → List Bool
  | before :: after :: rest => mosiEdge mode before after ++ mosiOnLeading mode (after :: rest)
  | _ => []

/-- One sample from the corresponding external aperture for each leading SCK edge. -/
def misoOnLeading (mode : Mode) : List Pins → List (BitVec 2) → List Bool
  | before :: after :: rest, raw :: later =>
    misoEdge mode before after raw ++ misoOnLeading mode (after :: rest) later
  | _, _ => []

/-- Raw input history aligned to pre-edge stage two. The final two entries
    are unused when paired with a pin trace from the same input list. -/
def apertureInputs (s : State a) (inputs : List Input) : List (BitVec 2) :=
  s.samplerSecond :: s.samplerFirst :: inputs.map (·.rawInputs)

/-- One TX bit can be reserved ahead of its leading edge. Pulse rows reserve none. -/
private def flight (s : State a) : List Bool :=
  if s.phase == .low && s.current.isStream then [s.cellBit] else []

private theorem data_step (mode : Mode) (d : Fin 256) (s : State a) (i : Input)
    (h : Positioned mode d s) (ordinary : Unreleased i) :
    let next := step (image mode d).program i s
    flight s ++ s.txEvent = mosiEdge mode s.pins next.pins ++ flight next ∧
    s.rxEvent = misoEdge mode s.pins next.pins s.samplerSecond ∧
    (leading mode s.pins next.pins = true → selected s.pins = true ∧ selected next.pins = true) := by
  dsimp only
  have next := positioned_step mode d s i h ordinary
  have nextClock := next.clock
  have nextSelect := next.select
  rw [step_eq_clock mode d s i h ordinary] at nextClock nextSelect ⊢
  have lead : leading mode s.pins (clock (image mode d).program i s).pins =
      (!(s.pc.toNat == 1 && s.phase == .high) &&
        ((clock (image mode d).program i s).pc.toNat == 1 &&
          (clock (image mode d).program i s).phase == .high)) := by
    simp only [leading,h.clock,nextClock]
  simp only [mosiEdge,misoEdge,lead,h.select,nextSelect,selectedState]
  rcases h.phase with phase | (phase | phase | phase) | phase
  · cases fetched : (image mode d).program.fetch s.pc.toNat with
    | none => simp [flight,State.txEvent,State.consumes,State.rxEvent,State.captures,
        clock,engine,phase,fetched,State.stop]
    | some instruction =>
      cases instruction <;> by_cases empty : s.remaining = 0#16 <;>
        simp [flight,State.txEvent,State.consumes,State.rxEvent,State.captures,
          clock,engine,phase,fetched,State.stop,empty]
  · rcases current_kind mode d s h (Or.inl phase) with ⟨_,current⟩ | ⟨_,current⟩
    · have transmits : (cell mode d).transmit = true := rfl
      cases credit : s.canReserve <;>
        simp [flight,State.txEvent,State.consumes,State.rxEvent,State.captures,
          clock,engine,phase,current,credit,Instruction.isStream,Instruction.cell,transmits]
    · cases credit : s.canReserve <;>
        simp [flight,State.txEvent,State.consumes,State.rxEvent,State.captures,
          clock,engine,phase,current,credit,pulse,Instruction.isStream]
  · rcases current_kind mode d s h (Or.inr (Or.inl phase)) with ⟨slot,current⟩ | ⟨slot,current⟩
    · have receives : (cell mode d).receive = true := rfl
      have port : (cell mode d).rxInput.val = 0 := rfl
      have bit := (cell_data mode d true s.lastCell s.cellBit).2.2.2
      by_cases zero : s.countdown = 0#8 <;>
        simp [flight,State.txEvent,State.consumes,State.rxEvent,State.captures,
          clock,engine,phase,current,zero,slot,Instruction.isStream,Instruction.hasHighGuard,
          Instruction.cell,State.enterHigh,State.captureData,State.highPins,receives,port,bit]
    · by_cases zero : s.countdown = 0#8 <;>
        simp [flight,State.txEvent,State.consumes,State.rxEvent,State.captures,
          clock,engine,phase,current,zero,slot,pulse,Instruction.isStream,Instruction.hasHighGuard,
          State.enterHigh,State.captureData]
  · by_cases zero : s.countdown = 0#8
    · cases stream : s.current.isStream <;> by_cases more : s.remaining.toNat > 1 <;>
        simp [flight,State.txEvent,State.consumes,State.rxEvent,State.captures,
          clock,engine,phase,zero,stream,more]
    · simp [flight,State.txEvent,State.consumes,State.rxEvent,State.captures,clock,engine,phase,zero]
  · simp [flight,State.txEvent,State.consumes,State.rxEvent,State.captures,clock,engine,phase]


private theorem trace_step_eq_clock (mode : Mode) (d : Fin 256) (s : State a) (i : Input)
    (h : Positioned mode d s) (ordinary : Unreleased i) (trace : BitTrace) :
    trace.step s i = trace.clock s i := by
  rcases ordinary with ⟨⟨cold,warm⟩,release⟩
  have notFree : s.phase ≠ .free := by
    rcases h.phase with phase | (phase | phase | phase) | phase <;> simp [phase]
  simp [BitTrace.step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,notFree]

private theorem mosi_cons (mode : Mode) (p : Program) (s : State a) (i : Input)
    (inputs : List Input) :
    mosiOnLeading mode (pinTrace p s (i :: inputs)) =
      mosiEdge mode s.pins (step p i s).pins ++ mosiOnLeading mode (pinTrace p (step p i s) inputs) := by
  cases inputs <;> rfl

private theorem miso_cons (mode : Mode) (p : Program) (s : State a) (i : Input)
    (inputs : List Input) (runtime : i.Runtime) :
    misoOnLeading mode (pinTrace p s (i :: inputs)) (apertureInputs s (i :: inputs)) =
      misoEdge mode s.pins (step p i s).pins s.samplerSecond ++
        misoOnLeading mode (pinTrace p (step p i s) inputs) (apertureInputs (step p i s) inputs) := by
  have samples := step_samples p s i runtime
  simp only [apertureInputs,samples.1,samples.2,List.map_cons]
  cases inputs <;> rfl

/-- Track one reserved MOSI bit across a finite prefix and every received MISO bit. -/
private theorem trace_data (mode : Mode) (d : Fin 256) (s : State a) (trace : BitTrace)
    (sent : List Bool) (prior : trace.consumed = sent ++ flight s) (inputs : List Input)
    (h : Positioned mode d s) (ordinary : ∀ i ∈ inputs, Unreleased i) :
    let p := (image mode d).program
    let wire := pinTrace p s inputs
    let final := run p s inputs
    let result := traceRun p s trace inputs
    result.consumed = (sent ++ mosiOnLeading mode wire) ++ flight final ∧
    result.captured = trace.captured ++ misoOnLeading mode wire (apertureInputs s inputs) := by
  induction inputs generalizing s trace sent with
  | nil => simpa [traceRun,pinTrace,run,mosiOnLeading,misoOnLeading] using prior
  | cons i rest ih =>
    let p := (image mode d).program
    let next := step p i s
    have first := ordinary i List.mem_cons_self
    have data := data_step mode d s i h first
    have accumulate := trace_step_eq_clock mode d s i h first trace
    have advanced : (trace.step s i).consumed = (sent ++ mosiEdge mode s.pins next.pins) ++ flight next := by
      rw [accumulate]
      simp only [BitTrace.clock,prior,List.append_assoc,data.1]
      rfl
    have inherited := ih next (trace.step s i) (sent ++ mosiEdge mode s.pins next.pins)
      advanced (positioned_step mode d s i h first) (fun j member => ordinary j (List.mem_cons_of_mem i member))
    change (traceRun p next (trace.step s i) rest).consumed =
        (sent ++ mosiOnLeading mode (pinTrace p s (i :: rest))) ++ flight (run p next rest) ∧
      (traceRun p next (trace.step s i) rest).captured = trace.captured ++
        misoOnLeading mode (pinTrace p s (i :: rest)) (apertureInputs s (i :: rest))
    rw [mosi_cons mode p s i rest,miso_cons mode p s i rest first.1]
    constructor
    · simpa only [List.append_assoc,next,p] using inherited.1
    · rw [inherited.2,accumulate]
      simp only [BitTrace.clock,data.2.1,List.append_assoc,next,p]

/-- Every reserved bit has reached MOSI by completion. The RX sequence consists
    of exactly the corresponding prior raw MISO samples in edge order. -/
theorem completed_data (mode : Mode) (d : Fin 256) (before : State a) (start : Input)
    (inputs : List Input) (ordinary : ∀ i ∈ inputs, Unreleased i)
    (completed : (run (image mode d).program (before.start (image mode d).program start) inputs).phase =
      .completed) :
    let p := (image mode d).program
    let s := before.start p start
    let wire := pinTrace p s inputs
    let result := traceRun p s {} inputs
    result.consumed = mosiOnLeading mode wire ∧
    result.captured = misoOnLeading mode wire (apertureInputs s inputs) := by
  have history := trace_data mode d (before.start (image mode d).program start) {} [] rfl inputs
    (positioned_start mode d before start) ordinary
  simpa [flight,completed] using history


private theorem edge_counts (mode : Mode) (before after : Pins) (raw : BitVec 2)
    (safe : leading mode before after = true → selected before = true ∧ selected after = true) :
    (mosiEdge mode before after).length = (observed mode before after).count .leading ∧
    (misoEdge mode before after raw).length = (observed mode before after).count .leading := by
  cases lead : leading mode before after
  · cases oldSelect : selected before <;> cases newSelect : selected after <;>
      cases tailEdge : trailing mode before after <;>
      simp [mosiEdge,misoEdge,observed,lead,oldSelect,newSelect,tailEdge] <;> split <;> decide +kernel
  · obtain ⟨oldSelect,newSelect⟩ := safe lead
    simp [mosiEdge,misoEdge,observed,lead,oldSelect,newSelect]

private theorem data_counts (mode : Mode) (d : Fin 256) (s : State a) (inputs : List Input)
    (h : Positioned mode d s) (ordinary : ∀ i ∈ inputs, Unreleased i) :
    let wire := pinTrace (image mode d).program s inputs
    (mosiOnLeading mode wire).length = (events mode wire).count .leading ∧
    (misoOnLeading mode wire (apertureInputs s inputs)).length = (events mode wire).count .leading := by
  induction inputs generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons i rest ih =>
    let p := (image mode d).program
    let next := step p i s
    have first := ordinary i List.mem_cons_self
    have data := data_step mode d s i h first
    have counts := edge_counts mode s.pins next.pins s.samplerSecond data.2.2
    have tail := ih next (positioned_step mode d s i h first)
      (fun j member => ordinary j (List.mem_cons_of_mem i member))
    dsimp only
    rw [mosi_cons,miso_cons mode _ s i rest first.1,events_pinTrace_cons,List.count_append]
    simp only [List.length_append,counts.1,counts.2,tail.1,tail.2,next,p,and_self]

/-- Each complete SPI clock pair accounts for one transmitted and one received bit. -/
theorem completed_count (mode : Mode) (d : Fin 256) (before : State a) (start : Input)
    (inputs : List Input) (ordinary : ∀ i ∈ inputs, Unreleased i)
    (completed : (run (image mode d).program (before.start (image mode d).program start) inputs).phase =
      .completed) :
    let p := (image mode d).program
    let s := before.start p start
    let wire := pinTrace p s inputs
    (mosiOnLeading mode wire).length = start.startCount.toNat ∧
    (misoOnLeading mode wire (apertureInputs s inputs)).length = start.startCount.toNat := by
  have countFor (n : Nat) : (edgesFor n).count .leading = n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [edgesFor,ih]
  have counts := data_counts mode d _ inputs (positioned_start mode d before start) ordinary
  dsimp only at counts
  rw [completed_exchange mode d before start inputs ordinary completed] at counts
  simpa [List.count_cons,List.count_append,countFor] using counts


private theorem start_clock_cut (mode : Mode) (d : Fin 256) (before : State a) (start i : Input)
    (ordinary : Unreleased i) :
    let p := (image mode d).program
    let initial := before.start p start
    let next := step p i initial
    next.phase = .boundary ∧ clockActive mode next.pins = false := by
  let p := (image mode d).program
  let initial := before.start p start
  have positioned := positioned_start mode d before start
  have fetched : (image mode d).program.fetch 0 = some (pulse mode d) := by
    simpa [row] using fetch mode d 0 (by decide)
  have pc : initial.pc.toNat = 0 := rfl
  have phase : initial.phase = .fetch := rfl
  have nextPhase : (step (image mode d).program i initial).phase = .boundary := by
    rw [step_eq_clock mode d initial i positioned ordinary]
    simp [clock,engine,phase,pc,fetched,pulse]
  refine ⟨nextPhase,?_⟩
  rw [(positioned_step mode d initial i positioned ordinary).clock]
  simp [nextPhase]

private theorem following_clock_idle (mode : Mode) (d : Fin 256) (s : State a) (i : Input)
    (h : Positioned mode d s) (ordinary : Unreleased i) (phase : s.phase = .boundary) :
    clockActive mode (step (image mode d).program i s).pins = false := by
  rw [(positioned_step mode d s i h ordinary).clock,step_eq_clock mode d s i h ordinary]
  cases credit : s.canReserve <;> simp [clock,engine,phase,credit]

/-- The leading-edge samples from START depend on the external inputs of the
    run, with a delay of two clocks. The first two aperture entries can be
    placeholders because neither step emits a leading edge. -/
theorem start_apertures (mode : Mode) (d : Fin 256) (before : State a) (start : Input)
    (inputs : List Input) (ordinary : ∀ i ∈ inputs, Unreleased i) :
    let p := (image mode d).program
    let initial := before.start p start
    let wire := pinTrace p initial inputs
    misoOnLeading mode wire (apertureInputs initial inputs) =
      misoOnLeading mode wire (0 :: 0 :: inputs.map (·.rawInputs)) := by
  cases inputs with
  | nil => rfl
  | cons i rest =>
    let p := (image mode d).program
    let initial := before.start p start
    have h := positioned_start mode d before start
    have first := ordinary i List.mem_cons_self
    have cut := start_clock_cut mode d before start i first
    have edge1 : leading mode initial.pins (step p i initial).pins = false := by
      simp [leading,show clockActive mode (step p i initial).pins = false from cut.2]
    cases rest with
    | nil => simp [pinTrace,misoOnLeading,apertureInputs,misoEdge,edge1,p,initial]
    | cons j rest =>
      have second := ordinary j (List.mem_cons_of_mem _ List.mem_cons_self)
      have idle : clockActive mode (step p j (step p i initial)).pins = false :=
        following_clock_idle mode d _ j (positioned_step mode d initial i h first) second cut.1
      have edge2 : leading mode (step p i initial).pins (step p j (step p i initial)).pins = false := by
        simp [leading,idle]
      cases rest <;> simp [pinTrace,misoOnLeading,apertureInputs,misoEdge,edge1,edge2,p,initial]

end Pinwheel.Program.StreamingSPI
