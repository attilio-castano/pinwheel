import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingReadyEventualService
import Pinwheel.Program.StreamingReadyTiming

/-! The SPI images differ in SCK polarity. Both clock the data cell on its
leading edge and park only at the mode's idle clock level. -/
namespace Pinwheel.Program.StreamingSPI
open StreamingReady

set_option linter.unusedSimpArgs false

inductive Mode where
  | mode0
  | mode2
  deriving DecidableEq, Repr

def Mode.cpol : Mode → Bool
  | .mode0 => false
  | .mode2 => true

def idlePins (mode : Mode) : Pins := ⟨if mode.cpol then 6 else 4, 7⟩

def clockPins (mode : Mode) (active : Bool) : Pins :=
  ⟨if (mode.cpol != active) then 2 else 0, 7⟩

def cell (mode : Mode) (d : Fin 256) : Cell :=
  {(Streaming.spiCell d) with lowPins := clockPins mode false, highPins := clockPins mode true}

def pulse (mode : Mode) (d : Fin 256) : Instruction :=
  .pulse {
    lowDuration := d, highDuration := d
    lowPins := clockPins mode false, highPins := clockPins mode false}

def source (mode : Mode) (d : Fin 256) : List Instruction :=
  [pulse mode d, .stream (cell mode d) none, pulse mode d, .halt]

theorem supported (mode : Mode) (d : Fin 256) : Supported (source mode d) := by
  simp [Supported,source,pulse,supportedFrom,List.countP_cons,Instruction.isStream,
    Instruction.Canonical,Streaming.Cell.PulseCanonical]

def image (mode : Mode) (d : Fin 256) : Compiled (source mode d) (idlePins mode) :=
  ⟨(source mode d).map encode, supported mode d, rfl⟩

theorem mode0_words (d : Fin 256) : (image .mode0 d).words = (Streaming.spiImage d).words := by
  change ((Streaming.spiSource d).map liftInstruction).map encode = _
  simp only [Streaming.spiImage,List.map_map,Function.comp_def,encode_lift]

def row (mode : Mode) (d : Fin 256) (pc : Nat) : Instruction :=
  if pc = 1 then .stream (cell mode d) none
  else if pc = 3 then .halt else pulse mode d

theorem fetch (mode : Mode) (d : Fin 256) (pc : Nat) (bound : pc ≤ 3) :
    (image mode d).program.fetch pc = some (row mode d pc) := by
  rw [(image mode d).program_fetch pc (show pc < (source mode d).length by change pc < 4; omega)]
  have slots : pc = 0 ∨ pc = 1 ∨ pc = 2 ∨ pc = 3 := by omega
  rcases slots with rfl|rfl|rfl|rfl <;> rfl

def active (s : State a) : Prop :=
  s.phase = .boundary ∨ s.phase = .low ∨ s.phase = .high

def clockActive (mode : Mode) (pins : Pins) : Bool := pins.levels[1] != mode.cpol

def selected (pins : Pins) : Bool := !pins.levels[2]

def leading (mode : Mode) (before after : Pins) : Bool :=
  !clockActive mode before && clockActive mode after

def trailing (mode : Mode) (before after : Pins) : Bool :=
  clockActive mode before && !clockActive mode after

def selectedState (s : State a) : Bool :=
  !(s.phase == .completed || (s.pc.toNat == 0 && s.phase == .fetch))

structure Positioned (mode : Mode) (d : Fin 256) (s : State a) : Prop where
  phase : s.phase = .fetch ∨ active s ∨ s.phase = .completed
  cursor : s.pc.toNat ≤ 3
  current : active s → s.pc.toNat < 3 ∧ s.current = row mode d s.pc.toNat
  live : active s → s.pc.toNat = 1 → 0 < s.remaining.toNat
  spent : 2 ≤ s.pc.toNat → s.remaining.toNat = 0
  finished : s.phase = .completed → s.pc.toNat = 3
  clock : clockActive mode s.pins = (s.pc.toNat == 1 && s.phase == .high)
  select : selected s.pins = selectedState s
  enabled : s.pins.enabled = 7#3

private theorem idle_signal (mode : Mode) :
    clockActive mode (idlePins mode) = false ∧ selected (idlePins mode) = false ∧
      (idlePins mode).enabled = 7#3 := by
  cases mode <;> decide +kernel

private theorem clock_signal (mode : Mode) (on : Bool) :
    clockActive mode (clockPins mode on) = on ∧ selected (clockPins mode on) = true ∧
      (clockPins mode on).enabled = 7#3 := by
  cases mode <;> cases on <;> decide +kernel

theorem cell_base (mode : Mode) (d : Fin 256) (high last : Bool) :
    (cell mode d).basePins high last = clockPins mode high := by
  cases mode <;> cases high <;> cases last <;> decide +revert +kernel

theorem cell_data (mode : Mode) (d : Fin 256) (high last bit : Bool) :
    let pins := (cell mode d).dataPins high last bit
    clockActive mode pins = high ∧ selected pins = true ∧ pins.enabled = 7#3 ∧
      pins.levels[0] = bit := by
  cases mode <;> cases high <;> cases last <;> cases bit <;> decide +revert +kernel

theorem positioned_start (mode : Mode) (d : Fin 256) (s : State a) (i : Input) :
    Positioned mode d (s.start (image mode d).program i) := by
  have ⟨c, cs, oe⟩ := idle_signal mode
  constructor <;> simp [State.start,active,selectedState,image,Compiled.program,c,cs,oe]

theorem current_kind (mode : Mode) (d : Fin 256) (s : State a)
    (h : Positioned mode d s) (on : active s) :
    (s.pc.toNat = 1 ∧ s.current = .stream (cell mode d) none) ∨
    (s.pc.toNat ≠ 1 ∧ s.current = pulse mode d) := by
  obtain ⟨bound,current⟩ := h.current on
  have stop : s.pc.toNat ≠ 3 := by omega
  by_cases data : s.pc.toNat = 1 <;> simp [row,data,stop] at current ⊢ <;> exact current

inductive Edge where
  | select
  | leading
  | trailing
  | deselect
  | invalidSelect
  deriving DecidableEq, Repr

def observed (mode : Mode) (before after : Pins) : List Edge :=
  if selected before != selected after then
    if clockActive mode before || clockActive mode after then [.invalidSelect]
    else if selected after then [.select] else [.deselect]
  else if leading mode before after then [.leading]
  else if trailing mode before after then [.trailing]
  else []

def edgesFor : Nat → List Edge
  | 0 => []
  | n+1 => .leading :: .trailing :: edgesFor n

def pending (s : State a) : List Edge :=
  let high := s.pc.toNat == 1 && s.phase == .high
  (if s.phase == .fetch && s.pc.toNat == 0 then [.select] else []) ++
    (if high then .trailing :: edgesFor (s.remaining.toNat - 1) else edgesFor s.remaining.toNat) ++
    (if s.phase == .completed then [] else [.deselect])

def events (mode : Mode) : List Pins → List Edge
  | before :: after :: rest => observed mode before after ++ events mode (after :: rest)
  | _ => []

theorem events_pinTrace_cons (mode : Mode) (p : Program) (s : State a) (i : Input) (inputs : List Input) :
    events mode (pinTrace p s (i :: inputs)) =
      observed mode s.pins (step p i s).pins ++ events mode (pinTrace p (step p i s) inputs) := by
  cases inputs <;> rfl

def Unreleased (i : Input) : Prop := i.Runtime ∧ i.command ≠ 4#4

theorem step_eq_clock (mode : Mode) (d : Fin 256) (s : State a) (i : Input)
    (h : Positioned mode d s) (ordinary : Unreleased i) :
    step (image mode d).program i s = clock (image mode d).program i s := by
  rcases ordinary with ⟨⟨cold,warm⟩,release⟩
  have notFree : s.phase ≠ .free := by
    rcases h.phase with phase | (phase | phase | phase) | phase <;> simp [phase]
  simp [step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,notFree]


private theorem pc_succ (pc : BitVec 7) (bound : pc.toNat < 3) :
    (pc+1#7).toNat = pc.toNat + 1 := by
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

private theorem remaining_sub (bits : BitVec 16) (live : 0 < bits.toNat) :
    (bits-1#16).toNat = bits.toNat - 1 := by
  apply BitVec.toNat_sub_of_le
  exact BitVec.le_def.mpr (by change 1 ≤ bits.toNat; omega)

private theorem pulse_low (mode : Mode) (d : Fin 256) :
    (pulse mode d).cell.lowPins = clockPins mode false := rfl

private theorem pulse_high (mode : Mode) (d : Fin 256) :
    (pulse mode d).cell.highPins = clockPins mode false := rfl

private theorem pulse_base (mode : Mode) (d : Fin 256) :
    (pulse mode d).cell.basePins false false = clockPins mode false := rfl

private theorem fetch_transition (mode : Mode) (d : Fin 256) (s : State a)
    (h : Positioned mode d s) (phase : s.phase = .fetch) :
    let n := engine (image mode d).program s
    Positioned mode d n ∧ pending s = observed mode s.pins n.pins ++ pending n := by
  have fetched := fetch mode d s.pc.toNat h.cursor
  have ⟨clk,cs,oe⟩ := clock_signal mode false
  dsimp
  rcases (show s.pc.toNat = 0 ∨ s.pc.toNat = 1 ∨ s.pc.toNat = 2 ∨ s.pc.toNat = 3 by
    have := h.cursor
    omega) with pc|pc|pc|pc
  · have e : engine (image mode d).program s =
        {s with phase := .boundary, current := pulse mode d, pins := clockPins mode false} := by
      simp only [engine,phase,fetched]
      simp [row,pc,pulse]
    rw [e]
    constructor
    · constructor <;> simp [active,pc,row,clk,cs,oe,selectedState]
    · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,clk,cs]
  · by_cases empty : s.remaining = 0#16
    · have e : engine (image mode d).program s = {s with pc := s.pc+1} := by
        simp only [engine,phase,fetched]
        simp [row,pc,empty]
      have next : (s.pc+1#7).toNat = 2 := by
        rw [pc_succ s.pc (by omega),pc]
      rw [e]
      constructor
      · constructor <;> simp [active,phase,pc,next,empty,h.clock,h.select,h.enabled,selectedState]
      · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,empty,next]
    · have positive : 0 < s.remaining.toNat := by
        have nz : s.remaining.toNat ≠ 0 := fun eq =>
          empty (BitVec.eq_of_toNat_eq (by simpa using eq))
        omega
      have e : engine (image mode d).program s =
          {s with
            phase := .boundary
            current := .stream (cell mode d) none
            pins := clockPins mode false} := by
        simp only [engine,phase,fetched]
        simp [row,pc,empty,cell_base]
      rw [e]
      constructor
      · constructor <;> simp [active,pc,row,clk,cs,oe,selectedState,positive]
      · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,clk,cs]
  · have spent := h.spent (show 2 ≤ s.pc.toNat by omega)
    have e : engine (image mode d).program s =
        {s with phase := .boundary, current := pulse mode d, pins := clockPins mode false} := by
      simp only [engine,phase,fetched]
      simp [row,pc,pulse]
    rw [e]
    constructor
    · constructor <;> simp [active,pc,row,clk,cs,oe,selectedState,spent]
    · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,clk,cs]
  · have spent := h.spent (show 2 ≤ s.pc.toNat by omega)
    have ⟨idleClock,idleSelect,idleEnabled⟩ := idle_signal mode
    have e : engine (image mode d).program s = s.stop (image mode d).program false := by
      simp only [engine,phase,fetched]
      simp [row,pc]
    rw [e]
    change Positioned mode d {s with phase := .completed, pins := idlePins mode} ∧
      pending s = observed mode s.pins (idlePins mode) ++
        pending {s with phase := .completed, pins := idlePins mode}
    constructor
    · constructor <;> simp [active,pc,row,idleClock,idleSelect,idleEnabled,selectedState,spent]
    · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,
        idleClock,idleSelect,spent,edgesFor]

private theorem boundary_transition (mode : Mode) (d : Fin 256) (s : State a)
    (h : Positioned mode d s) (phase : s.phase = .boundary) :
    let n := engine (image mode d).program s
    Positioned mode d n ∧ pending s = observed mode s.pins n.pins ++ pending n := by
  have on : active s := Or.inl phase
  have ⟨bound,current⟩ := h.current on
  have live := h.live on
  dsimp
  cases credit : s.canReserve with
  | false =>
    simp [engine,phase,credit,observed,leading,trailing,h,h.clock,h.select,selectedState]
  | true =>
    rcases current_kind mode d s h on with ⟨pc,kind⟩ | ⟨pc,kind⟩
    · have ⟨clk,cs,oe,_⟩ := cell_data mode d false s.lastCell (s.selectedTx.data[31])
      have tx : (cell mode d).transmit = true := rfl
      simp only [engine,phase,credit,if_true,kind,Instruction.isStream,Instruction.cell,tx,
        Bool.true_and]
      constructor
      · constructor <;> simp [active,pc,row,clk,cs,oe,selectedState,live]
      · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,clk,cs]
    · have ⟨clk,cs,oe⟩ := clock_signal mode false
      have stream : (pulse mode d).isStream = false := rfl
      have stop : s.pc.toNat ≠ 3 := by omega
      simp only [engine,phase,credit,if_true,kind,stream,Bool.false_eq_true,if_false,pulse_low]
      constructor
      · constructor <;> simp [active,h.cursor,bound,row,pc,stop,clk,cs,oe,selectedState,live]
        exact h.spent
      · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,clk,cs]


private theorem edgesFor_pos (n : Nat) (positive : 0 < n) :
    edgesFor n = .leading :: .trailing :: edgesFor (n-1) := by
  cases n with
  | zero => omega
  | succ n => rfl

private theorem low_transition (mode : Mode) (d : Fin 256) (s : State a)
    (h : Positioned mode d s) (phase : s.phase = .low) :
    let n := engine (image mode d).program s
    Positioned mode d n ∧ pending s = observed mode s.pins n.pins ++ pending n := by
  have on : active s := Or.inr (Or.inl phase)
  have ⟨bound,current⟩ := h.current on
  have live := h.live on
  dsimp
  by_cases done : s.countdown = 0#8
  · rcases current_kind mode d s h on with ⟨pc,kind⟩ | ⟨pc,kind⟩
    · have ⟨clk,cs,oe,_⟩ := cell_data mode d true (s.remaining == 1#16) s.cellBit
      simp only [engine,phase,done,beq_self_eq_true,if_true,State.highPins,State.lastCell,kind,
        Instruction.isStream,Instruction.cell,Instruction.hasHighGuard,if_false,Bool.false_eq_true,
        Bool.true_and,State.enterHigh,State.captureData]
      constructor
      · constructor <;> simp [active,pc,row,clk,cs,oe,selectedState,live]
      · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,clk,cs]
        exact congrArg (· ++ [.deselect]) (edgesFor_pos _ (live pc))
    · have ⟨clk,cs,oe⟩ := clock_signal mode false
      have stream : (pulse mode d).isStream = false := rfl
      have guard : (pulse mode d).hasHighGuard = false := rfl
      have stop : s.pc.toNat ≠ 3 := by omega
      simp only [engine,phase,done,beq_self_eq_true,if_true,State.highPins,kind,stream,guard,
        Bool.false_eq_true,if_false,State.enterHigh,State.captureData,pulse_high]
      constructor
      · constructor <;> simp [active,h.cursor,bound,row,pc,stop,clk,cs,oe,selectedState,live]
        exact h.spent
      · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,clk,cs]
  · have e : engine (image mode d).program s = {s with countdown := s.countdown - 1} := by
      simp [engine,phase,done]
    rw [e]
    refine ⟨⟨h.phase,h.cursor,h.current,h.live,h.spent,h.finished,h.clock,h.select,h.enabled⟩,?_⟩
    simp [pending,observed,leading,trailing,h.select,h.clock,phase,selectedState]

private theorem high_transition (mode : Mode) (d : Fin 256) (s : State a)
    (h : Positioned mode d s) (phase : s.phase = .high) :
    let n := engine (image mode d).program s
    Positioned mode d n ∧ pending s = observed mode s.pins n.pins ++ pending n := by
  have on : active s := Or.inr (Or.inr phase)
  have ⟨bound,current⟩ := h.current on
  have live := h.live on
  have ⟨clk,cs,oe⟩ := clock_signal mode false
  have next := pc_succ s.pc bound
  dsimp
  by_cases done : s.countdown = 0#8
  · rcases current_kind mode d s h on with ⟨pc,kind⟩ | ⟨pc,kind⟩
    · have positive := live pc
      have left := remaining_sub s.remaining positive
      by_cases more : 1 < s.remaining.toNat
      · have still : 0 < s.remaining.toNat - 1 := by omega
        simp [engine,phase,done,kind,Instruction.isStream,Instruction.cell,cell_base,more]
        constructor
        · constructor <;> simp [active,pc,row,clk,cs,oe,selectedState,left,still]
        · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,clk,cs,left]
      · have one : s.remaining.toNat = 1 := by omega
        simp [engine,phase,done,kind,Instruction.isStream,Instruction.cell,cell_base,more]
        constructor
        · constructor <;> simp [active,pc,row,clk,cs,oe,selectedState,left,one,next]
        · simp [pending,observed,leading,trailing,h.select,h.clock,phase,pc,selectedState,
            clk,cs,left,one,next,edgesFor]
    · have stream : (pulse mode d).isStream = false := rfl
      have last : s.lastCell = false := by simp [State.lastCell,kind,stream]
      have places : s.pc.toNat = 0 ∨ s.pc.toNat = 2 := by omega
      rcases places with place | place
      · simp [engine,phase,done,kind,stream,last,pulse_base]
        constructor
        · constructor <;> simp [active,place,next,clk,cs,oe,selectedState]
        · simp [pending,observed,leading,trailing,h.select,h.clock,phase,place,selectedState,
            clk,cs,next]
      · have spent := h.spent (show 2 ≤ s.pc.toNat by omega)
        simp [engine,phase,done,kind,stream,last,pulse_base]
        constructor
        · constructor <;> simp [active,place,next,clk,cs,oe,selectedState,spent]
        · simp [pending,observed,leading,trailing,h.select,h.clock,phase,place,selectedState,
            clk,cs,next]
  · have e : engine (image mode d).program s = {s with countdown := s.countdown - 1} := by
      simp [engine,phase,done]
    rw [e]
    refine ⟨⟨h.phase,h.cursor,h.current,h.live,h.spent,h.finished,h.clock,h.select,h.enabled⟩,?_⟩
    simp only [observed]
    cases hs : selected s.pins <;> cases hc : clockActive mode s.pins <;>
      simp [hs,hc,leading,trailing,pending]

private theorem positioned_clock (mode : Mode) (d : Fin 256) (s : State a) (i : Input)
    (h : Positioned mode d s) :
    let n := clock (image mode d).program i s
    Positioned mode d n ∧ pending s = observed mode s.pins n.pins ++ pending n := by
  have update : Positioned mode d (engine (image mode d).program s) ∧
      pending s = observed mode s.pins (engine (image mode d).program s).pins ++
        pending (engine (image mode d).program s) := by
    rcases h.phase with phase | (phase | phase | phase) | phase
    · exact fetch_transition mode d s h phase
    · exact boundary_transition mode d s h phase
    · exact low_transition mode d s h phase
    · exact high_transition mode d s h phase
    · simp [engine,phase,h,observed,leading,trailing]
  obtain ⟨n,flow⟩ := update
  exact ⟨⟨n.phase,n.cursor,n.current,n.live,n.spent,n.finished,n.clock,n.select,n.enabled⟩,flow⟩

theorem positioned_step (mode : Mode) (d : Fin 256) (s : State a) (i : Input)
    (h : Positioned mode d s) (ordinary : Unreleased i) :
    Positioned mode d (step (image mode d).program i s) := by
  rw [step_eq_clock mode d s i h ordinary]
  exact (positioned_clock mode d s i h).1

theorem run_schedule (mode : Mode) (d : Fin 256) (s : State a) (inputs : List Input)
    (h : Positioned mode d s) (ordinary : ∀ i ∈ inputs, Unreleased i) :
    let last := run (image mode d).program s inputs
    Positioned mode d last ∧ pending s = events mode (pinTrace (image mode d).program s inputs) ++
      pending last := by
  induction inputs generalizing s with
  | nil => exact ⟨h,rfl⟩
  | cons i rest ih =>
    have first := ordinary i List.mem_cons_self
    have actual := step_eq_clock mode d s i h first
    obtain ⟨next,edge⟩ := positioned_clock mode d s i h
    rw [← actual] at next edge
    obtain ⟨last,tail⟩ := ih _ next (fun j member => ordinary j (List.mem_cons_of_mem _ member))
    refine ⟨last,?_⟩
    rw [events_pinTrace_cons,List.append_assoc]
    change pending s = observed mode s.pins (step (image mode d).program i s).pins ++
      (events mode (pinTrace (image mode d).program (step (image mode d).program i s) rest) ++
        pending (run (image mode d).program (step (image mode d).program i s) rest))
    rw [← tail]
    exact edge

theorem completed_exchange (mode : Mode) (d : Fin 256) (before : State a) (start : Input)
    (inputs : List Input) (ordinary : ∀ i ∈ inputs, Unreleased i)
    (completed : (run (image mode d).program (before.start (image mode d).program start) inputs).phase = .completed) :
    events mode (pinTrace (image mode d).program (before.start (image mode d).program start) inputs) =
      .select :: edgesFor start.startCount.toNat ++ [.deselect] := by
  obtain ⟨h,trace⟩ := run_schedule mode d _ inputs (positioned_start mode d before start) ordinary
  have pc := h.finished completed
  have spent := h.spent (show 2 ≤ (run (image mode d).program (before.start (image mode d).program start)
      inputs).pc.toNat by omega)
  have empty : pending (run (image mode d).program (before.start (image mode d).program start) inputs) = [] := by
    simp [pending,pc,spent,completed,edgesFor]
  rw [empty,List.append_nil] at trace
  simpa [pending,State.start] using trace.symm


theorem eventually_completed (mode : Mode) (d : Fin 256) (before : State a) (start : Input)
    (incoming : Nat → Input) (ordinary : ∀ n, Unreleased (incoming n))
    (credits : ∀ n, (EventualService.state (image mode d).program
      (before.start (image mode d).program start) incoming n).phase = .boundary →
      ∃ m, n ≤ m ∧ (EventualService.state (image mode d).program
        (before.start (image mode d).program start) incoming m).canReserve = true) :
    ∃ edges,
      (run (image mode d).program (before.start (image mode d).program start)
        (EventualService.clocks incoming edges)).phase = .completed := by
  have admitted : ∀ edges i, i ∈ EventualService.clocks incoming edges → Unreleased i := by
    intro edges i member
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp member
    exact ordinary n
  have positions := fun edges => (run_schedule mode d _ (EventualService.clocks incoming edges)
    (positioned_start mode d before start) (admitted edges)).1
  have fair : EventualService.Fair (image mode d).program (before.start (image mode d).program start) incoming := by
    refine ⟨credits, ?_⟩
    intro n waiting
    rw [EventualService.state_eq_run] at waiting
    rcases (positions n).phase with phase | (phase | phase | phase) | phase <;> simp_all
  obtain ⟨edges,retained⟩ := EventualService.started (image mode d).program before start incoming
    (fun n => (ordinary n).1) fair
  refine ⟨edges,?_⟩
  rcases (positions edges).phase with phase | (phase | phase | phase) | phase <;>
    simp [phase,Phase.retained] at retained ⊢

/-- Waiting for FIFO credit keeps the selected bus at its idle clock polarity. -/
theorem stalled_idle (mode : Mode) (d : Fin 256) (s : State a) (i : Input)
    (h : Positioned mode d s) (ordinary : Unreleased i)
    (phase : s.phase = .boundary) (blocked : s.canReserve = false) :
    clockActive mode s.pins = false ∧ selected s.pins = true ∧ (step (image mode d).program i s).pins = s.pins := by
  rw [step_eq_clock mode d s i h ordinary,h.clock,h.select]
  simp [phase,selectedState,clock,engine,blocked]

theorem leading_cut (mode : Mode) (d : Fin 256) (s : State a) (i : Input)
    (h : Positioned mode d s) (ordinary : Unreleased i)
    (edge : leading mode s.pins (step (image mode d).program i s).pins = true) :
    s.phase = .low ∧ s.pc.toNat = 1 ∧ s.countdown = 0#8 ∧
    (step (image mode d).program i s).phase = .high ∧
    (step (image mode d).program i s).countdown.toNat = d.val := by
  have hnext := positioned_step mode d s i h ordinary
  have edges : clockActive mode s.pins = false ∧
      clockActive mode (step (image mode d).program i s).pins = true := by
    simpa [leading] using edge
  rw [hnext.clock] at edges
  have next := edges.2
  simp only [Bool.and_eq_true,beq_iff_eq] at next
  obtain ⟨pcNext,high⟩ := next
  have held := edges.1
  rw [h.clock] at held
  rw [step_eq_clock mode d s i h ordinary] at pcNext high ⊢
  rcases h.phase with phase | (phase | phase | phase) | phase
  · have fetched := fetch mode d s.pc.toNat h.cursor
    rcases (show s.pc.toNat = 0 ∨ s.pc.toNat = 1 ∨ s.pc.toNat = 2 ∨ s.pc.toNat = 3 by
      have := h.cursor
      omega) with pc | pc | pc | pc
    · simp only [clock,engine,phase,fetched] at high
      simp [row,pc,pulse] at high
    · simp only [clock,engine,phase,fetched] at high
      by_cases empty : s.remaining = 0#16 <;> simp [row,pc,empty,phase] at high
    · simp only [clock,engine,phase,fetched] at high
      simp [row,pc,pulse] at high
    · simp only [clock,engine,phase,fetched] at high
      simp [row,pc,State.stop] at high
  · cases credit : s.canReserve <;> simp [clock,engine,phase,credit] at high
  · by_cases zero : s.countdown = 0#8
    · rcases current_kind mode d s h (Or.inr (Or.inl phase)) with ⟨pc,kind⟩ | ⟨pc,kind⟩
      · refine ⟨phase,pc,zero,high,?_⟩
        simp [clock,engine,phase,zero,kind,State.enterHigh,State.captureData,Instruction.hasHighGuard,
          Instruction.cell,cell,Streaming.spiCell,BitVec.toNat_ofNat,Nat.mod_eq_of_lt d.isLt]
      · have guard : (pulse mode d).hasHighGuard = false := rfl
        simp [clock,engine,phase,zero,kind,guard,State.enterHigh,State.captureData,pc] at pcNext
    · simp [clock,engine,phase,zero] at high
  · by_cases zero : s.countdown = 0#8
    · have endPhase := step_high_terminal (image mode d).program s i ordinary.1 phase zero
      rw [step_eq_clock mode d s i h ordinary] at endPhase
      rw [endPhase] at high
      split at high <;> contradiction
    · simp [clock,engine,phase,zero] at pcNext
      simp [phase,pcNext] at held
  · simp [clock,engine,phase] at high

/-- The leading edge starts exactly `d.val + 1` core cycles of active SCK.
Every earlier prefix keeps the entire driven pad pose, independent of credits. -/
theorem leading_interval (mode : Mode) (d : Fin 256) (s : State a) (edge : Input)
    (within : List Input) (last : Input) (h : Positioned mode d s) (ordinary : Unreleased edge)
    (rise : leading mode s.pins (step (image mode d).program edge s).pins = true)
    (service : ∀ i ∈ within, Unreleased i) (lastOrdinary : Unreleased last)
    (length : within.length = d.val) :
    let p := (image mode d).program
    let data := step p edge s
    let endActive := run p data within
    (∀ k ≤ d.val, (run p data (within.take k)).pins = data.pins) ∧
      trailing mode endActive.pins (step p last endActive).pins = true := by
  let p := (image mode d).program
  let data := step p edge s
  have ⟨_,_,_,phase,count⟩ := leading_cut mode d s edge h ordinary rise
  have started := positioned_step mode d s edge h ordinary
  have runtime : ∀ i ∈ within, i.Runtime := fun i member => (service i member).1
  refine ⟨?_,?_⟩
  · intro k le
    have short : (within.take k).length ≤ data.countdown.toNat := by
      rw [count,List.length_take,length]
      omega
    exact (high_prefix p data (within.take k) phase
      (fun i member => runtime i (List.mem_of_mem_take member)) short).2.2.1
  · have exactLength : within.length = data.countdown.toNat := length.trans count.symm
    obtain ⟨_,pins,fall⟩ := high_interval p data within last phase runtime lastOrdinary.1 exactLength
    have activeHigh : clockActive mode data.pins = true := by
      have active := rise
      simp only [leading,Bool.and_eq_true] at active
      exact active.2
    have ended := (run_schedule mode d data within started service).1
    have post := positioned_step mode d (run p data within) last ended lastOrdinary
    change trailing mode (run p data within).pins (step p last (run p data within)).pins = true
    rw [trailing,pins,activeHigh,post.clock]
    simp
    exact Or.inr fall


/-- After reserving a data bit the inactive SCK and MOSI pose remain stable
for exactly the programmed LOW countdown and the terminal interval. -/
theorem reserved_idle_interval (mode : Mode) (d : Fin 256) (s : State a) (edge : Input)
    (within : List Input) (last : Input) (h : Positioned mode d s) (ordinary : Unreleased edge)
    (boundary : s.phase = .boundary) (atCell : s.pc.toNat = 1) (credit : s.canReserve = true)
    (service : ∀ i ∈ within, Unreleased i) (lastOrdinary : Unreleased last)
    (length : within.length = d.val) :
    let p := (image mode d).program
    let reserved := step p edge s
    let endIdle := run p reserved within
    clockActive mode reserved.pins = false ∧
      (∀ k ≤ d.val, (run p reserved (within.take k)).pins = reserved.pins) ∧
      leading mode endIdle.pins (step p last endIdle).pins = true := by
  let p := (image mode d).program
  let reserved := step p edge s
  have kind := ((current_kind mode d s h (Or.inl boundary)).resolve_right
    fun contrary => contrary.1 atCell).2
  have ⟨phase,count,current⟩ :
      reserved.phase = .low ∧ reserved.countdown.toNat = d.val ∧
      reserved.current = .stream (cell mode d) none := by
    change (step p edge s).phase = .low ∧ (step p edge s).countdown.toNat = d.val ∧
      (step p edge s).current = .stream (cell mode d) none
    rw [step_eq_clock mode d s edge h ordinary]
    simp [clock,engine,boundary,credit,kind,Instruction.cell,cell,Streaming.spiCell,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt d.isLt]
  have pos := positioned_step mode d s edge h ordinary
  have idle : clockActive mode reserved.pins = false := by
    have clock := pos.clock
    change clockActive mode reserved.pins = _ at clock
    rw [clock,phase]
    simp
  have runtime : ∀ i ∈ within, i.Runtime := fun i mem => (service i mem).1
  refine ⟨idle,?_,?_⟩
  · intro k le
    have short : (within.take k).length ≤ reserved.countdown.toNat := by
      rw [count,List.length_take,length]
      omega
    exact (low_prefix p reserved (within.take k) phase
      (fun i mem => runtime i (List.mem_of_mem_take mem)) short).2.2.1
  · have exactLength : within.length = reserved.countdown.toNat := length.trans count.symm
    obtain ⟨stillLow, left, pins, _, kind'⟩ := low_prefix p reserved within phase runtime (Nat.le_of_eq exactLength)
    have zero : (run p reserved within).countdown = 0#8 := by
      apply BitVec.eq_of_toNat_eq
      simp [left,exactLength]
    have high := step_low_terminal p (run p reserved within) last lastOrdinary.1 stillLow zero
    change leading mode (run p reserved within).pins (step p last (run p reserved within)).pins = true
    rw [leading,pins,idle,high.2.1]
    have highClock : clockActive mode (run p reserved within).highPins = true := by
      rw [State.highPins,kind',current]
      simp only [Instruction.isStream,if_true,Instruction.cell]
      exact (cell_data mode d true (run p reserved within).lastCell (run p reserved within).cellBit).1
    simp [highClock]

/-- Every snapshot of a started SPI program continues to drive MOSI, SCK and CS. -/
theorem driven_trace (mode : Mode) (d : Fin 256) (s : State a) (inputs : List Input)
    (h : Positioned mode d s) (ordinary : ∀ i ∈ inputs, Unreleased i) :
    ∀ pins ∈ pinTrace (image mode d).program s inputs, pins.enabled = 7#3 := by
  induction inputs generalizing s with
  | nil => simp [pinTrace,h.enabled]
  | cons i is ih =>
    intro pins member
    simp only [pinTrace,List.mem_cons] at member
    rcases member with rfl | tail
    · exact h.enabled
    · exact ih _ (positioned_step mode d s i h (ordinary i List.mem_cons_self))
        (fun i mem => ordinary i (List.mem_cons_of_mem _ mem)) pins tail

/-- Every leading edge is followed by exactly the declared number of
identical active pad snapshots, then a trailing edge. -/
def activePulses (mode : Mode) (duration : Nat) : List Pins → Prop
  | before :: after :: rest =>
    (leading mode before after = true →
      ∃ next tail, rest = List.replicate duration after ++ next :: tail ∧ trailing mode after next = true) ∧
      activePulses mode duration (after :: rest)
  | _ => True

private theorem pinTrace_head (p : Program) (s : State a) (inputs : List Input) :
    pinTrace p s inputs = s.pins :: (pinTrace p s inputs).tail := by
  cases inputs <;> rfl

private theorem activePulses_cons (mode : Mode) (duration : Nat) (p : Program) (s : State a)
    (i : Input) (inputs : List Input) :
    activePulses mode duration (pinTrace p s (i :: inputs)) =
      ((leading mode s.pins (step p i s).pins = true →
        ∃ next tail, (pinTrace p (step p i s) inputs).tail =
          List.replicate duration (step p i s).pins ++ next :: tail ∧
          trailing mode (step p i s).pins next = true) ∧
        activePulses mode duration (pinTrace p (step p i s) inputs)) := by
  cases inputs <;> rfl

private theorem pinTrace_append_clock (p : Program) (s : State a) (before : List Input)
    (i : Input) (after : List Input) :
    pinTrace p s (before ++ i :: after) =
      pinTrace p s before ++ pinTrace p (step p i (run p s before)) after := by
  induction before generalizing s with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.cons_append,pinTrace,List.cons.injEq,true_and]
    exact ih (step p j s)

private theorem pinTrace_high (p : Program) (s : State a) (inputs : List Input)
    (phase : s.phase = .high) (ordinary : ∀ i ∈ inputs, i.Runtime)
    (length : inputs.length ≤ s.countdown.toNat) :
    pinTrace p s inputs = List.replicate (inputs.length + 1) s.pins := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have nonzero : s.countdown ≠ 0#8 := by
      intro zero
      simp [zero] at length
    have after := step_high_wait p s i (ordinary i List.mem_cons_self) phase nonzero
    have sub : (s.countdown-1#8).toNat = s.countdown.toNat - 1 := by
      apply BitVec.toNat_sub_of_le
      change 1 ≤ s.countdown.toNat
      simp only [List.length_cons] at length
      omega
    have remains : rest.length ≤ (step p i s).countdown.toNat := by
      rw [after.2.1,sub]
      simp only [List.length_cons] at length
      omega
    have tail := ih (step p i s) after.1 (fun j mem => ordinary j (List.mem_cons_of_mem _ mem)) remains
    simp [pinTrace,tail,after.2.2.1,List.replicate_succ]

/-- Completed SPI traces contain every complete SCK pulse with its exact
active duration, regardless of idle intervals spent waiting for credit. -/
theorem completed_timing (mode : Mode) (d : Fin 256) (s : State a) (inputs : List Input)
    (h : Positioned mode d s) (ordinary : ∀ i ∈ inputs, Unreleased i)
    (completed : (run (image mode d).program s inputs).phase = .completed) :
    activePulses mode d.val (pinTrace (image mode d).program s inputs) := by
  induction inputs generalizing s with
  | nil => exact True.intro
  | cons i rest ih =>
    let p := (image mode d).program
    let data := step p i s
    have first := ordinary i List.mem_cons_self
    have pos := positioned_step mode d s i h first
    have later : ∀ j ∈ rest, Unreleased j := fun j mem => ordinary j (List.mem_cons_of_mem _ mem)
    have laterRuntime : ∀ j ∈ rest, j.Runtime := fun j mem => (later j mem).1
    have finished : (run p data rest).phase = .completed := completed
    rw [activePulses_cons]
    refine ⟨?_, ih data pos later finished⟩
    intro rise
    have ⟨_, _, _, phase, count⟩ := leading_cut mode d s i h first rise
    have width : d.val < rest.length := by
      by_cases short : rest.length ≤ d.val
      · have remains := high_prefix p data rest phase laterRuntime (show rest.length ≤ data.countdown.toNat by
            rw [count]
            exact short)
        rw [finished] at remains
        simp at remains
      · omega
    let within := rest.take d.val
    have withinLength : within.length = d.val := by simp [within, Nat.min_eq_left (Nat.le_of_lt width)]
    have withinService : ∀ j ∈ within, Unreleased j := fun j mem => later j (List.mem_of_mem_take mem)
    have withinRuntime : ∀ j ∈ within, j.Runtime := fun j mem => (withinService j mem).1
    have decomposition : within ++ rest.drop d.val = rest := List.take_append_drop _ _
    cases tailEq : rest.drop d.val with
    | nil =>
      rw [tailEq,List.append_nil] at decomposition
      have len := congrArg List.length decomposition
      omega
    | cons last tail =>
      rw [tailEq] at decomposition
      have lastOrdinary : Unreleased last :=
        later last (decomposition ▸ List.mem_append_right within List.mem_cons_self)
      have pulse := leading_interval mode d s i within last h first rise withinService lastOrdinary withinLength
      have noChange := pulse.1 d.val (Nat.le_refl _)
      rw [List.take_of_length_le (Nat.le_of_eq withinLength)] at noChange
      let next := step p last (run p data within)
      have fall : trailing mode (run p data within).pins next.pins = true := pulse.2
      rw [noChange] at fall
      change ∃ nextPins tailPins, (pinTrace p data rest).tail =
        List.replicate d.val data.pins ++ nextPins :: tailPins ∧ trailing mode data.pins nextPins = true
      refine ⟨next.pins, (pinTrace p next tail).tail, ?_,fall⟩
      have snapshots := pinTrace_high p data within phase withinRuntime (Nat.le_of_eq (withinLength.trans count.symm))
      rw [← decomposition,pinTrace_append_clock,snapshots,withinLength,List.replicate_succ,List.cons_append,List.tail_cons]
      rw [← pinTrace_head p next tail]

end Pinwheel.Program.StreamingSPI
