import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingReadyBitTrace
import Pinwheel.Program.StreamingReadyTiming
import Pinwheel.Program.StreamingReadyEventualService
import Pinwheel.Program.StreamingI2CRead

/-! Successful execution and qualified bus events for the standard Ready I²C image. -/
namespace Pinwheel.Program.StreamingI2CTrace
open StreamingReady

set_option linter.unusedSimpArgs false

def program : Program := (i2cImage .standard).program

def row : Nat → Instruction
  | 0 => .driveWait ⟨0,0⟩ (i2cGuard .standard 3 3)
  | 1 => i2cHold .standard 2
  | 2 => .stream (i2cCell .standard) (some (i2cGuard .standard 1 1))
  | 3 => i2cStopLow .standard
  | 4 => .driveWait ⟨0,2⟩ (i2cGuard .standard 1 1)
  | 5 => i2cHold .standard 2
  | _ => .halt

theorem fetch (pc : Nat) (bound : pc ≤ 6) :
    program.fetch pc = some (row pc) := by
  unfold program
  rw [(i2cImage .standard).program_fetch pc (show pc < (i2cSource .standard).length by
    change pc < 7
    omega)]
  have slots : pc = 0 ∨ pc = 1 ∨ pc = 2 ∨ pc = 3 ∨ pc = 4 ∨ pc = 5 ∨ pc = 6 := by omega
  rcases slots with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

def Cyclic (s : State a) : Prop :=
  s.phase = .boundary ∨ s.phase = .low ∨ s.phase = .high

def cycleRow (pc : Nat) : Prop := pc = 1 ∨ pc = 2 ∨ pc = 3 ∨ pc = 5

def waitRow (pc : Nat) : Prop := pc = 0 ∨ pc = 2 ∨ pc = 4

/-- Only open-drain enables change. Rows 0 and 4 wait for START and STOP
preconditions. Stream WAIT and HIGH keep the reserved SDA value. -/
def enables (pc : Nat) (phase : Phase) (bit : Bool) : BitVec 3 :=
  if phase = .completed then 0
  else match pc with
  | 0 => 0
  | 1 => if phase = .fetch then 0 else 2
  | 2 => match phase with
    | .fetch => 2
    | .boundary => 1
    | .low => if bit then 1 else 3
    | _ => if bit then 0 else 2
  | 3 => if phase = .fetch then 1 else 3
  | 4 => if phase = .fetch then 3 else 2
  | _ => 2

structure Positioned (s : State a) : Prop where
  phase : s.phase = .fetch ∨ Cyclic s ∨ s.phase = .waiting ∨ s.phase = .completed
  cursor : s.pc.toNat ≤ 6
  cycles : Cyclic s → cycleRow s.pc.toNat
  waits : s.phase = .waiting → waitRow s.pc.toNat
  current : Cyclic s ∨ s.phase = .waiting → s.current = row s.pc.toNat
  live : s.pc.toNat ≤ 2 → 0 < s.remaining.toNat
  spent : 3 ≤ s.pc.toNat → s.remaining.toNat = 0
  finished : s.phase = .completed → s.pc.toNat = 6
  pads : s.pins = ⟨0,enables s.pc.toNat s.phase s.cellBit⟩

def Unreleased (i : Input) : Prop := i.Runtime ∧ i.command ≠ 4#4

theorem positioned_start (s : State a) (i : Input) (positive : 0 < i.startCount.toNat) :
    Positioned (s.start program i) := by
  constructor <;> simp [State.start,Cyclic,enables,positive,program,Compiled.program]

theorem step_eq_clock (s : State a) (i : Input) (h : Positioned s) (ordinary : Unreleased i) :
    step program i s = clock program i s := by
  rcases ordinary with ⟨⟨cold,warm⟩,release⟩
  have notFree : s.phase ≠ .free := by
    rcases h.phase with phase | (phase | phase | phase) | phase | phase <;> simp [phase]
  simp [step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,notFree]

private theorem pc_next (pc : BitVec 7) (bound : pc.toNat < 6) :
    (pc + 1#7).toNat = pc.toNat + 1 := by
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

private theorem cell_base (high last : Bool) :
    (i2cCell .standard).basePins high last = ⟨0,if high then 0 else 1⟩ := by
  cases high <;> cases last <;> decide +kernel

private theorem cell_data (high last bit : Bool) :
    (i2cCell .standard).dataPins high last bit =
      ⟨0,if high then (if bit then 0 else 2) else (if bit then 1 else 3)⟩ := by
  cases high <;> cases last <;> cases bit <;> decide +kernel

inductive Event where
  | start
  | slot
  | stop
  deriving DecidableEq, Repr

/-- Only guarded data captures qualify as data clocks. The frame edges refer
to the programmed START and STOP cuts, whose resolved levels are proved below. -/
def observed (s : State a) : List Event :=
  if s.phase = .fetch ∧ s.pc.toNat = 1 then [.start]
  else if s.captures then [.slot]
  else if s.phase = .fetch ∧ s.pc.toNat = 6 then [.stop]
  else []

def pending (s : State a) : List Event :=
  (if s.pc.toNat = 0 ∨ s.pc.toNat = 1 ∧ s.phase = .fetch then [.start] else []) ++
  List.replicate (s.remaining.toNat - (if s.pc.toNat = 2 ∧ s.phase = .high then 1 else 0)) .slot ++
  (if s.phase = .completed then [] else [.stop])

private theorem fetch_transition (s : State a) (h : Positioned s) (phase : s.phase = .fetch) :
    let n := engine program s
    Positioned n ∧ pending s = observed s ++ pending n := by
  have fetched := fetch s.pc.toNat h.cursor
  have range : s.pc.toNat = 0 ∨ s.pc.toNat = 1 ∨ s.pc.toNat = 2 ∨ s.pc.toNat = 3 ∨
      s.pc.toNat = 4 ∨ s.pc.toNat = 5 ∨ s.pc.toNat = 6 := by have := h.cursor; omega
  have reads : s.captures = false := by simp [State.captures,phase]
  rcases range with pc | pc | pc | pc | pc | pc | pc
  · simp only [engine,phase,fetched]
    simp only [pc,row]
    constructor
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,live,row]
      done
    · simp [pending,observed,phase,pc,reads]
  · simp only [engine,phase,fetched]
    simp only [pc,row,i2cHold]
    constructor
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,live,row,i2cHold]
      done
    · simp [pending,observed,phase,pc,reads]
  · have live := h.live (show s.pc.toNat ≤ 2 by omega)
    have nz : s.remaining ≠ 0#16 := by
      intro zero
      simp [zero] at live
    simp only [engine,phase,fetched]
    simp [pc,row,nz,cell_base]
    constructor
    · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,live,row]
      done
    · simp [pending,observed,phase,pc,reads]
  · simp only [engine,phase,fetched]
    simp only [pc,row,i2cStopLow]
    constructor
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,spent,row,i2cStopLow]
      done
    · simp [pending,observed,phase,pc,reads]
  · simp only [engine,phase,fetched]
    simp only [pc,row]
    constructor
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,spent,row]
      done
    · simp [pending,observed,phase,pc,reads]
  · simp only [engine,phase,fetched]
    simp only [pc,row,i2cHold]
    constructor
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,spent,row,i2cHold]
      done
    · simp [pending,observed,phase,pc,reads]
  · simp only [engine,phase,fetched]
    simp only [pc,row,State.stop]
    constructor
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,spent,row,program,Compiled.program]
      done
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      simp [pending,observed,phase,pc,reads,spent]

private theorem boundary_transition (s : State a) (h : Positioned s) (phase : s.phase = .boundary) :
    let n := engine program s
    Positioned n ∧ pending s = observed s ++ pending n := by
  have cyc : Cyclic s := Or.inl phase
  have current := h.current (Or.inl cyc)
  have reads : s.captures = false := by simp [State.captures,phase]
  cases credit : s.canReserve
  · simp [engine,phase,credit,h,observed,reads]
  · rcases h.cycles cyc with pc | pc | pc | pc
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      simp [engine,phase,credit,current,pc,row,i2cHold,Instruction.cell,Instruction.isStream]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,live,row,i2cHold]
        done
      · simp [pending,observed,phase,pc,reads]
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      simp [engine,phase,credit,current,pc,row,Instruction.cell,Instruction.isStream,
        show (i2cCell .standard).transmit = true from rfl,cell_data]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,live,row]
        done
      · simp [pending,observed,phase,pc,reads]
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      simp [engine,phase,credit,current,pc,row,i2cStopLow,Instruction.cell,Instruction.isStream]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,spent,row,i2cStopLow]
        done
      · simp [pending,observed,phase,pc,reads]
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      simp [engine,phase,credit,current,pc,row,i2cHold,Instruction.cell,Instruction.isStream]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,spent,row,i2cHold]
        done
      · simp [pending,observed,phase,pc,reads]

private theorem low_transition (s : State a) (h : Positioned s) (phase : s.phase = .low) :
    let n := engine program s
    Positioned n ∧ pending s = observed s ++ pending n := by
  have cyc : Cyclic s := Or.inr (Or.inl phase)
  have current := h.current (Or.inl cyc)
  by_cases zero : s.countdown = 0#8
  · rcases h.cycles cyc with pc | pc | pc | pc
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      have reads : s.captures = false := by simp [State.captures,current,pc,row,i2cHold,Instruction.isStream]
      simp [engine,phase,zero,current,pc,row,i2cHold,Instruction.hasHighGuard,State.enterHigh,
        State.captureData,State.highPins,Instruction.cell,Instruction.isStream]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,live,row,i2cHold]
        done
      · simp [pending,observed,phase,pc,reads]
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      have reads : s.captures = false := by simp [State.captures,current,phase,pc,row,Instruction.hasHighGuard]
      simp [engine,phase,zero,current,pc,row,Instruction.hasHighGuard,State.highPins,
        Instruction.cell,Instruction.isStream,cell_data]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,live,row]
        done
      · simp [pending,observed,phase,pc,reads]
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      have reads : s.captures = false := by simp [State.captures,current,pc,row,i2cStopLow,Instruction.isStream]
      simp [engine,phase,zero,current,pc,row,i2cStopLow,Instruction.hasHighGuard,State.enterHigh,
        State.captureData,State.highPins,Instruction.cell,Instruction.isStream]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,spent,row,i2cStopLow]
        done
      · simp [pending,observed,phase,pc,reads]
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      have reads : s.captures = false := by simp [State.captures,current,pc,row,i2cHold,Instruction.isStream]
      simp [engine,phase,zero,current,pc,row,i2cHold,Instruction.hasHighGuard,State.enterHigh,
        State.captureData,State.highPins,Instruction.cell,Instruction.isStream]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,spent,row,i2cHold]
        done
      · simp [pending,observed,phase,pc,reads]
  · have e : engine program s = {s with countdown := s.countdown - 1} := by simp [engine,phase,zero]
    rw [e]
    refine ⟨⟨h.phase,h.cursor,h.cycles,h.waits,h.current,h.live,h.spent,h.finished,h.pads⟩,?_⟩
    simp [pending,observed,phase,State.captures,zero]

private theorem high_transition (s : State a) (h : Positioned s) (phase : s.phase = .high) :
    let n := engine program s
    Positioned n ∧ pending s = observed s ++ pending n := by
  have cyc : Cyclic s := Or.inr (Or.inr phase)
  have current := h.current (Or.inl cyc)
  have reads : s.captures = false := by simp [State.captures,phase]
  have next := pc_next s.pc (by rcases h.cycles cyc with pc | pc | pc | pc <;> omega)
  by_cases zero : s.countdown = 0#8
  · rcases h.cycles cyc with pc | pc | pc | pc
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      simp [engine,phase,zero,current,pc,row,i2cHold,Instruction.cell,Instruction.isStream,
        Streaming.Cell.basePins,State.lastCell]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,next,pc,live,row]
        done
      · simp [pending,observed,phase,pc,reads,next]
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      have left : (s.remaining - 1#16).toNat = s.remaining.toNat - 1 := by
        apply BitVec.toNat_sub_of_le
        change 1 ≤ s.remaining.toNat
        omega
      by_cases more : 1 < s.remaining.toNat
      · have still : 0 < s.remaining.toNat - 1 := by omega
        simp [engine,phase,zero,current,pc,row,Instruction.isStream,Instruction.cell,cell_base,more]
        constructor
        · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,row,left,still]
          done
        · simp [pending,observed,phase,pc,reads,left]
      · have one : s.remaining.toNat = 1 := by omega
        simp [engine,phase,zero,current,pc,row,Instruction.isStream,Instruction.cell,cell_base,more]
        constructor
        · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,next,pc,row,left,one]
          done
        · simp [pending,observed,phase,pc,reads,left,one,next]
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      simp [engine,phase,zero,current,pc,row,i2cStopLow,Instruction.cell,Instruction.isStream,
        Streaming.Cell.basePins,State.lastCell]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,next,pc,spent,row]
        done
      · simp [pending,observed,phase,pc,reads,next]
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      simp [engine,phase,zero,current,pc,row,i2cHold,Instruction.cell,Instruction.isStream,
        Streaming.Cell.basePins,State.lastCell]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,next,pc,spent,row]
        done
      · simp [pending,observed,phase,pc,reads,next]
  · have e : engine program s = {s with countdown := s.countdown - 1} := by simp [engine,phase,zero]
    rw [e]
    refine ⟨⟨h.phase,h.cursor,h.cycles,h.waits,h.current,h.live,h.spent,h.finished,h.pads⟩,?_⟩
    simp [pending,observed,phase,reads]

private theorem wait_transition (s : State a) (h : Positioned s) (phase : s.phase = .waiting)
    (safe : (engine program s).phase ≠ .fault) :
    let n := engine program s
    Positioned n ∧ pending s = observed s ++ pending n := by
  have current := h.current (Or.inr phase)
  have next := pc_next s.pc (by rcases h.waits phase with pc | pc | pc <;> omega)
  cases ready : s.waitReady
  · have miss : s.current.guard.limit.expires s.countdown = false := by
      cases expires : s.current.guard.limit.expires s.countdown
      · rfl
      · simp [engine,phase,ready,expires,State.timeoutFault] at safe
    have e : engine program s =
        {s with countdown := s.current.guard.limit.poll s.countdown} := by simp [engine,phase,ready,miss]
    rw [e]
    refine ⟨⟨h.phase,h.cursor,h.cycles,h.waits,h.current,h.live,h.spent,h.finished,h.pads⟩,?_⟩
    simp [pending,observed,phase,ready,State.captures]
  · rcases h.waits phase with pc | pc | pc
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      have pads := h.pads
      rw [pc,phase] at pads
      have reads : s.captures = false := by simp [State.captures,current,pc,row,Instruction.isStream]
      simp [engine,phase,ready,current,pc,row,Instruction.isStream]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,next,pc,live,row,pads]
        done
      · simp [pending,observed,phase,pc,reads,next]
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      have pads := h.pads
      rw [pc,phase] at pads
      have reads : s.captures = true := by
        simp [State.captures,current,pc,row,phase,ready,Instruction.isStream,Instruction.cell,
          i2cCell]
      simp [engine,phase,ready,current,pc,row,Instruction.isStream,State.enterHigh,State.captureData]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,pc,live,row,pads]
        done
      · simp [pending,observed,phase,pc,reads]
        obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt live)
        simp [hn,List.replicate_succ]
    · have spent := h.spent (show 3 ≤ s.pc.toNat by omega)
      have pads := h.pads
      rw [pc,phase] at pads
      have reads : s.captures = false := by simp [State.captures,current,pc,row,Instruction.isStream]
      simp [engine,phase,ready,current,pc,row,Instruction.isStream]
      constructor
      · constructor <;> simp [Cyclic,waitRow,cycleRow,enables,next,pc,spent,row,pads]
        done
      · simp [pending,observed,phase,pc,reads,next]

private theorem positioned_clock (s : State a) (i : Input) (h : Positioned s)
    (safe : (clock program i s).phase ≠ .fault) :
    let n := clock program i s
    Positioned n ∧ pending s = observed s ++ pending n := by
  have update : Positioned (engine program s) ∧ pending s = observed s ++ pending (engine program s) := by
    rcases h.phase with phase | (phase | phase | phase) | phase | phase
    · exact fetch_transition s h phase
    · exact boundary_transition s h phase
    · exact low_transition s h phase
    · exact high_transition s h phase
    · exact wait_transition s h phase safe
    · simp [engine,phase,h,observed,State.captures]
  obtain ⟨n,flow⟩ := update
  exact ⟨⟨n.phase,n.cursor,n.cycles,n.waits,n.current,n.live,n.spent,n.finished,n.pads⟩,flow⟩

theorem positioned_step (s : State a) (i : Input) (h : Positioned s) (ordinary : Unreleased i)
    (safe : (step program i s).phase ≠ .fault) :
    let n := step program i s
    Positioned n ∧ pending s = observed s ++ pending n := by
  rw [step_eq_clock s i h ordinary] at safe ⊢
  exact positioned_clock s i h safe

theorem fault_run (s : State a) (inputs : List Input) (fault : s.phase = .fault)
    (ordinary : ∀ i ∈ inputs, Unreleased i) : (run program s inputs).phase = .fault := by
  induction inputs generalizing s with
  | nil => exact fault
  | cons i rest ih =>
    have ⟨⟨cold,warm⟩,release⟩ := ordinary i List.mem_cons_self
    have stays : (step program i s).phase = .fault := by
      simp [step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,fault,clock,engine]
    exact ih _ stays (fun j mem => ordinary j (List.mem_cons_of_mem _ mem))

def frameEvents (s : State a) : List Input → List Event
  | [] => []
  | i::rest => observed s ++ frameEvents (step program i s) rest

def txQualified (s : State a) : List Bool := if s.captures then [s.cellBit] else []

def txQualifiedRun (s : State a) : List Input → List Bool
  | [] => []
  | i::rest => txQualified s ++ txQualifiedRun (step program i s) rest

theorem run_schedule (s : State a) (inputs : List Input) (h : Positioned s)
    (ordinary : ∀ i ∈ inputs, Unreleased i) (safe : (run program s inputs).phase ≠ .fault) :
    let n := run program s inputs
    Positioned n ∧ pending s = frameEvents s inputs ++ pending n := by
  induction inputs generalizing s with
  | nil => exact ⟨h,rfl⟩
  | cons i rest ih =>
    have tail : ∀ j ∈ rest, Unreleased j := fun j mem => ordinary j (List.mem_cons_of_mem _ mem)
    have safeStep : (step program i s).phase ≠ .fault := fun fault =>
      safe (fault_run _ rest fault tail)
    obtain ⟨next,edge⟩ := positioned_step s i h (ordinary i List.mem_cons_self) safeStep
    obtain ⟨last,flow⟩ := ih (step program i s) next tail safe
    refine ⟨last,?_⟩
    change pending s = (observed s ++ frameEvents (step program i s) rest) ++
      pending (run program (step program i s) rest)
    rw [List.append_assoc,← flow]
    exact edge

theorem completed_frame (before : State a) (start : Input) (inputs : List Input)
    (positive : 0 < start.startCount.toNat) (ordinary : ∀ i ∈ inputs, Unreleased i)
    (completed : (run program (before.start program start) inputs).phase = .completed) :
    frameEvents (before.start program start) inputs = [.start] ++
      List.replicate start.startCount.toNat .slot ++ [.stop] := by
  have safe : (run program (before.start program start) inputs).phase ≠ .fault := by
    simp [completed]
  obtain ⟨position,flow⟩ := run_schedule _ inputs (positioned_start before start positive) ordinary safe
  have pc := position.finished completed
  have spent := position.spent (by omega)
  have empty : pending (run program (before.start program start) inputs) = [] := by
    simp [pending,pc,spent,completed]
  rw [empty,List.append_nil] at flow
  simpa [pending,State.start] using flow.symm

theorem capture_cut (s : State a) (h : Positioned s) (capture : s.captures = true) :
    s.phase = .waiting ∧ s.pc.toNat = 2 ∧ s.waitReady = true ∧
    s.pins.enabled.getLsbD 0 = false ∧ s.pins.enabled.getLsbD 1 = !s.cellBit ∧
    s.rxEvent = [s.samplerSecond.getLsbD 1] := by
  have shape := captures_fields s capture
  have lowImpossible : s.phase ≠ .low := by
    intro low
    have cyclic : Cyclic s := Or.inr (Or.inl low)
    have current := h.current (Or.inl cyclic)
    rcases h.cycles cyclic with pc | pc | pc | pc <;>
      simp [State.captures,current,row,pc,low,i2cHold,i2cStopLow,Instruction.isStream,
        Instruction.hasHighGuard] at capture
  have waiting : s.phase = .waiting := shape.2.2.resolve_left lowImpossible
  have current := h.current (Or.inr waiting)
  have pc : s.pc.toNat = 2 := by
    rcases h.waits waiting with zero | two | four
    · simp [current,row,zero,Instruction.isStream] at shape
    · exact two
    · simp [current,row,four,Instruction.isStream] at shape
  have ready : s.waitReady = true := by
    simpa [State.captures,waiting,shape.1,shape.2.1] using capture
  have pads : s.pins = ⟨0,if s.cellBit then 0 else 2⟩ := by
    simpa [pc,waiting,enables] using h.pads
  refine ⟨waiting,pc,ready,?_,?_,?_⟩
  · cases bit : s.cellBit <;> simp [pads,bit]
  · cases bit : s.cellBit <;> simp [pads,bit]
  · simp [State.rxEvent,capture,current,pc,row,Instruction.cell,i2cCell]

private theorem prev_armed (s : State a) (i : Input) (h : Positioned s) (ordinary : Unreleased i)
    (atStream : (step program i s).pc.toNat = 2)
    (late : (step program i s).phase = .waiting ∨
      (step program i s).phase = .low ∧ (step program i s).countdown = 0#8) :
    s.pc.toNat = 2 ∧ (s.phase = .waiting ∨ s.phase = .low) ∧
    (step program i s).cellBit = s.cellBit ∧
    ((step program i s).phase = .waiting → s.phase = .waiting ∨ s.phase = .low ∧ s.countdown = 0#8) := by
  rw [step_eq_clock s i h ordinary] at atStream late ⊢
  rcases h.phase with phase | (phase | phase | phase) | phase | phase
  · have fetched := fetch s.pc.toNat h.cursor
    have range : s.pc.toNat = 0 ∨ s.pc.toNat = 1 ∨ s.pc.toNat = 2 ∨ s.pc.toNat = 3 ∨
        s.pc.toNat = 4 ∨ s.pc.toNat = 5 ∨ s.pc.toNat = 6 := by have := h.cursor; omega
    simp only [clock,engine,phase,fetched] at atStream late
    rcases range with pc | pc | pc | pc | pc | pc | pc
    · simp [pc,row] at atStream
    · simp [pc,row,i2cHold] at late
    · have live := h.live (show s.pc.toNat ≤ 2 by omega)
      have nz : s.remaining ≠ 0#16 := by
        intro zero
        simp [zero] at live
      simp [pc,row,nz] at late
    · simp [pc,row,i2cStopLow] at late
    · simp [pc,row] at atStream
    · simp [pc,row,i2cHold] at late
    · simp [pc,row,State.stop] at late
  · have cyc : Cyclic s := Or.inl phase
    have rowEq := h.current (Or.inl cyc)
    cases credit : s.canReserve
    · simp [clock,engine,phase,credit] at late
    · rcases h.cycles cyc with pc | pc | pc | pc <;>
        simp [clock,engine,phase,credit,rowEq,pc,row,i2cHold,i2cStopLow,i2cCell,
          I2cProfile.standard,Instruction.cell] at late
  · have cyc : Cyclic s := Or.inr (Or.inl phase)
    have rowEq := h.current (Or.inl cyc)
    by_cases zero : s.countdown = 0#8
    · have pc : s.pc.toNat = 2 := by
        rcases h.cycles cyc with pc | pc | pc | pc <;>
          simp [clock,engine,phase,zero,rowEq,pc,row,i2cHold,i2cStopLow,
            Instruction.hasHighGuard,State.enterHigh,State.captureData] at atStream ⊢
      simp [clock,engine,phase,zero,pc,rowEq,row,Instruction.hasHighGuard]
    · have pc : s.pc.toNat = 2 := by simpa [clock,engine,phase,zero] using atStream
      simp [clock,engine,phase,zero,pc]
  · by_cases zero : s.countdown = 0#8
    · cases stream : s.current.isStream <;> by_cases more : 1 < s.remaining.toNat <;>
        simp [clock,engine,phase,zero,stream,more] at late
    · simp [clock,engine,phase,zero] at late
  · cases ready : s.waitReady
    · cases expires : s.current.guard.limit.expires s.countdown
      · have pc : s.pc.toNat = 2 := by simpa [clock,engine,phase,ready,expires] using atStream
        simp [clock,engine,phase,ready,expires,pc]
      · simp [clock,engine,phase,ready,expires,State.timeoutFault] at late
    · cases stream : s.current.isStream <;>
        simp [clock,engine,phase,ready,stream,State.enterHigh,State.captureData] at late
  · simp [clock,engine,phase] at late

private theorem sda_flight (s : State a) (h : Positioned s) (pc : s.pc.toNat = 2)
    (flight : s.phase = .waiting ∨ s.phase = .low) :
    s.pins.enabled.getLsbD 1 = !s.cellBit := by
  rcases flight with phase | phase <;>
    cases bit : s.cellBit <;> simp [h.pads,pc,phase,bit,enables]

private theorem aperture_holds (s : State a) (first second : Input) (h : Positioned s)
    (one : Unreleased first) (two : Unreleased second)
    (q : State a) (history : q = step program second (step program first s))
    (shape : Positioned q) (capture : q.captures = true) :
    s.pins.enabled.getLsbD 1 = q.pins.enabled.getLsbD 1 := by
  let mid := step program first s
  have midSafe : mid.phase ≠ .fault := by
    intro fault
    have terminal := fault_run mid [second] fault (by simp [two])
    have bad : q.phase = .fault := by rw [history]; exact terminal
    rcases shape.phase with phase | (phase | phase | phase) | phase | phase <;> simp [phase] at bad
  have midShape := (positioned_step s first h one midSafe).1
  obtain ⟨wait,pc,_,_,sda,_⟩ := capture_cut q shape capture
  have later := prev_armed mid second midShape two
    (by rw [← history]; exact pc) (Or.inl (by rw [← history]; exact wait))
  have earlier := prev_armed s first h one later.1
    (later.2.2.2 (by rw [← history]; exact wait))
  rw [sda_flight s h earlier.1 earlier.2.1, sda, history, later.2.2.1, earlier.2.2.1]

def qualifiedStates (s : State a) : List Input → List (State a)
  | [] => []
  | i :: rest => (if s.captures then [s] else []) ++ qualifiedStates (step program i s) rest

theorem txQualified_states (s : State a) (inputs : List Input) :
    txQualifiedRun s inputs = (qualifiedStates s inputs).map State.cellBit := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [txQualifiedRun,qualifiedStates,List.map_append,ih]
    cases cap : s.captures <;> simp [txQualified,cap]

theorem qualified_position (s : State a) (inputs : List Input) (h : Positioned s)
    (ordinary : ∀ i ∈ inputs, Unreleased i) (safe : (run program s inputs).phase ≠ .fault) :
    ∀ q ∈ qualifiedStates s inputs, Positioned q ∧ q.captures = true := by
  induction inputs generalizing s with
  | nil => simp [qualifiedStates]
  | cons i rest ih =>
    intro q mem
    have tail : ∀ j ∈ rest, Unreleased j := fun j m => ordinary j (List.mem_cons_of_mem _ m)
    have safeNext : (step program i s).phase ≠ .fault := fun fault =>
      safe (fault_run _ rest fault tail)
    have positioned := (positioned_step s i h (ordinary i List.mem_cons_self) safeNext).1
    by_cases cap : s.captures = true
    · have picked : q = s ∨ q ∈ qualifiedStates (step program i s) rest := by
        simpa [qualifiedStates,cap] using mem
      rcases picked with rfl | later
      · exact ⟨h,cap⟩
      · exact ih _ positioned tail safe q later
    · have later : q ∈ qualifiedStates (step program i s) rest := by
        simpa [qualifiedStates,cap] using mem
      exact ih _ positioned tail safe q later

private theorem trace_step_eq_clock (s : State a) (i : Input) (trace : BitTrace)
    (h : Positioned s) (ordinary : Unreleased i) :
    trace.step s i = trace.clock s i := by
  rcases ordinary with ⟨⟨cold,warm⟩,release⟩
  have notFree : s.phase ≠ .free := by
    rcases h.phase with phase | (phase | phase | phase) | phase | phase <;> simp [phase]
  simp [BitTrace.step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,notFree]

theorem captured_qualified (s : State a) (inputs : List Input) (trace : BitTrace)
    (h : Positioned s) (ordinary : ∀ i ∈ inputs, Unreleased i)
    (safe : (run program s inputs).phase ≠ .fault) :
    (traceRun program s trace inputs).captured = trace.captured ++
      (qualifiedStates s inputs).map (fun q => q.samplerSecond.getLsbD 1) := by
  induction inputs generalizing s trace with
  | nil => simp [traceRun,qualifiedStates]
  | cons i rest ih =>
    have oi := ordinary i List.mem_cons_self
    have tail : ∀ j ∈ rest, Unreleased j := fun j m => ordinary j (List.mem_cons_of_mem _ m)
    have safeNext : (step program i s).phase ≠ .fault := fun fault =>
      safe (fault_run _ rest fault tail)
    have positioned := (positioned_step s i h oi safeNext).1
    have traceNext := trace_step_eq_clock s i trace h oi
    rw [traceRun,ih _ (trace.step s i) positioned tail safe,traceNext]
    by_cases cap : s.captures = true
    · simp [BitTrace.clock,qualifiedStates,cap,(capture_cut s h cap).2.2.2.2.2,List.append_assoc]
    · simp [BitTrace.clock,qualifiedStates,cap,State.rxEvent]

open StreamingI2CRead in
/-- Each raw input is obtained from the actual controller pad state and the
peer's independent low/release choice at that core clock. -/
def Connected (s : State a) (inputs : List Input) (peer : Nat → I2C.Pins) : Prop :=
  ∀ (earlier : List Input) (clock : Input) (rest : List Input),
    inputs = earlier ++ clock :: rest →
    clock.rawInputs = resolvedRaw (run program s earlier).pins (peer earlier.length)

def Released : I2C.Pins := ⟨.release,.release⟩

def Starting (s : State a) : Prop := s.phase = .fetch ∧ s.pc.toNat = 1
def Stopping (s : State a) : Prop := s.phase = .fetch ∧ s.pc.toNat = 6

open StreamingI2CRead in
/-- Digital setup contract at the sampler aperture of each qualified cell.
The required SDA drive of the peer is generated from its own payload. -/
structure ReadPeer (s : State a) (inputs : List Input)
    (payload : List (BitVec 8)) (peer : Nat → I2C.Pins) : Prop where
  setup : ∀ k q, (qualifiedStates s inputs)[k]? = some q →
    ∃ (earlier : List Input) (first second : Input) (rest : List Input) (stretchLow : Bool),
      inputs = earlier ++ first :: second :: rest ∧
      q = run program s (earlier ++ [first,second]) ∧
      peer earlier.length = peerPins payload k stretchLow
  frame : ∀ (earlier : List Input) (clock : Input) (rest : List Input),
    inputs = earlier ++ clock :: rest →
    Starting (run program s earlier) ∨ Stopping (run program s earlier) →
      peer earlier.length = Released

open StreamingI2CRead in
/-- Peer drive is held during each observed controller transition. At the
START/STOP cuts, the resolved bus changes SDA while SCL is HIGH. -/
def ResolvedFraming (s : State a) (inputs : List Input) (peer : Nat → I2C.Pins) : Prop :=
  ∀ (earlier : List Input) (clock : Input) (rest : List Input),
    inputs = earlier ++ clock :: rest →
    let q := run program s earlier
    let before := resolvedRaw q.pins (peer earlier.length)
    let after := resolvedRaw (step program clock q).pins (peer earlier.length)
    (Starting q → before = 3#2 ∧ after = 1#2) ∧
    (Stopping q → before = 1#2 ∧ after = 3#2)

private theorem frame_poses (s : State a) (i : Input) (h : Positioned s) (ordinary : Unreleased i) :
    (Starting s → s.pins = ⟨0,0⟩ ∧ (step program i s).pins = ⟨0,2⟩) ∧
    (Stopping s → s.pins = ⟨0,2⟩ ∧ (step program i s).pins = ⟨0,0⟩) := by
  have fetched := fetch s.pc.toNat h.cursor
  rw [step_eq_clock s i h ordinary]
  constructor
  · rintro ⟨phase,pc⟩
    have pads := h.pads
    rw [pc,phase] at pads
    simp only [clock,engine,phase,fetched]
    simpa [enables,pc,row,i2cHold] using pads
  · rintro ⟨phase,pc⟩
    have pads := h.pads
    rw [pc,phase] at pads
    simp only [clock,engine,phase,fetched]
    simpa [enables,pc,row,State.stop,program,Compiled.program] using pads

theorem resolved_framing (s : State a) (inputs : List Input)
    (payload : List (BitVec 8)) (peer : Nat → I2C.Pins)
    (h : Positioned s) (ordinary : ∀ i ∈ inputs, Unreleased i)
    (safe : (run program s inputs).phase ≠ .fault) (legal : ReadPeer s inputs payload peer) :
    ResolvedFraming s inputs peer := by
  intro earlier i rest history
  let q := run program s earlier
  have legalEarlier : ∀ j ∈ earlier, Unreleased j := fun j mem =>
    ordinary j (history ▸ List.mem_append_left _ mem)
  have legalRest : ∀ j ∈ i :: rest, Unreleased j := fun j mem =>
    ordinary j (history ▸ List.mem_append_right _ mem)
  have safeEarlier : q.phase ≠ .fault := by
    intro fault
    apply safe
    rw [history]
    simpa [run,List.foldl_append,q] using fault_run q (i::rest) fault legalRest
  have shape := (run_schedule s earlier h legalEarlier safeEarlier).1
  have cuts := frame_poses q i shape (legalRest i List.mem_cons_self)
  constructor
  · intro start
    obtain ⟨a,b⟩ := cuts.1 start
    rw [legal.frame earlier i rest history (Or.inl start)]
    rw [a,b]
    decide +kernel
  · intro stop
    obtain ⟨a,b⟩ := cuts.2 stop
    rw [legal.frame earlier i rest history (Or.inr stop)]
    rw [a,b]
    decide +kernel

open StreamingI2CRead in
theorem completed_read (before : State a) (start : Input) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Unreleased i)
    (completed : (run program (before.start program start) inputs).phase = .completed)
    (count : start.startCount = 585#16)
    (payload : List (BitVec 8)) (peer : Nat → I2C.Pins) (size : payload.length = 64)
    (connected : Connected (before.start program start) inputs peer)
    (legal : ReadPeer (before.start program start) inputs payload peer)
    (tx : txQualifiedRun (before.start program start) inputs = hostBits) :
    let initial := before.start program start
    frameEvents initial inputs = [.start] ++ List.replicate 585 .slot ++ [.stop] ∧
      ResolvedFraming initial inputs peer ∧
      (traceRun program initial {} inputs).captured = wireBits payload := by
  let initial := before.start program start
  have positive : 0 < start.startCount.toNat := by rw [count]; decide +kernel
  have h := positioned_start before start positive
  have safe : (run program initial inputs).phase ≠ .fault := by
    change (run program (before.start program start) inputs).phase ≠ .fault
    simp [completed]
  refine ⟨?_,resolved_framing initial inputs payload peer h ordinary safe legal,?_⟩
  · rw [completed_frame before start inputs positive ordinary completed,count]
    rfl
  · have captured := captured_qualified initial inputs {} h ordinary safe
    change (traceRun program initial {} inputs).captured = wireBits payload
    rw [captured]
    simp only [List.nil_append]
    let slots := qualifiedStates initial inputs
    have txMap : slots.map State.cellBit = hostBits :=
      (txQualified_states initial inputs).symm.trans tx
    have len : slots.length = 585 := by
      simpa only [List.length_map,hostBits_length] using congrArg List.length txMap
    apply List.ext_getElem?
    intro k
    change (slots.map (fun q => q.samplerSecond.getLsbD 1))[k]? = (wireBits payload)[k]?
    by_cases inside : k < slots.length
    · let q := slots[k]
      have atK : slots[k]? = some q := List.getElem?_eq_getElem inside
      have capture := qualified_position initial inputs h ordinary safe q (List.getElem_mem inside)
      have cut := capture_cut q capture.1 capture.2
      have txAt := congrArg (fun l : List Bool => l[k]?) txMap
      rw [List.getElem?_map,atK] at txAt
      have bit : q.cellBit = hostBit k := by
        simp [hostBit,← txAt]
      obtain ⟨earlier,first,second,rest,stretch,history,state,stimulus⟩ := legal.setup k q atK
      have one : first.Runtime := (ordinary first (by rw [history]; simp)).1
      have two : second.Runtime := (ordinary second (by rw [history]; simp)).1
      have aperture : q.samplerSecond = first.rawInputs := by
        rw [state]
        exact (run_two_samples program initial earlier first second one two).2
      have raw := connected earlier first (second::rest) history
      have legalEarlier : ∀ j ∈ earlier, Unreleased j := fun j mem =>
        ordinary j (history ▸ List.mem_append_left _ mem)
      have legalRest : ∀ j ∈ first :: second :: rest, Unreleased j := fun j mem =>
        ordinary j (history ▸ List.mem_append_right _ mem)
      have safeEarlier : (run program initial earlier).phase ≠ .fault := by
        intro fault
        apply safe
        rw [history]
        simpa [run,List.foldl_append] using
          fault_run (run program initial earlier) (first :: second :: rest) fault legalRest
      have earlierShape := (run_schedule initial earlier h legalEarlier safeEarlier).1
      have holds := aperture_holds (run program initial earlier) first second earlierShape
        (ordinary first (by rw [history]; simp)) (ordinary second (by rw [history]; simp)) q
        (by simpa [run,List.foldl_append] using state) capture.1 capture.2
      have command : (run program initial earlier).pins.enabled.getLsbD 1 = !hostBit k :=
        holds.trans (by simpa [bit] using cut.2.2.2.2.1)
      rw [List.getElem?_map,atK,wireBits_get payload size k (len ▸ inside),Option.map_some]
      rw [aperture,raw,stimulus,resolvedRaw_peer_sda _ payload k stretch command]
    · have outside : 585 ≤ k := by omega
      rw [List.getElem?_map,List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (by rw [wireBits_length payload size]; exact outside)]
      rfl

end Pinwheel.Program.StreamingI2CTrace
