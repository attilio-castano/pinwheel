import Pinwheel.Program.StreamingJTAG
import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingReadyBitTrace
import Pinwheel.Program.StreamingReadyEventualService
import Pinwheel.Program.StreamingReadyTiming

/-! Link the compiled JTAG program to the edges of the sampled-ready core.
    Queue service may park the core between data clocks. -/
namespace Pinwheel.Program.StreamingJTAG
open Pinwheel.Program.StreamingReady

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

def source (d : Fin 256) : List Instruction :=
  (Streaming.jtagSource d).map liftInstruction

def idlePins : Engine.Reactive.Pins := ⟨0,7⟩

theorem supported (d : Fin 256) : Supported (source d) := by
  simp [Supported, source, Streaming.jtagSource, Streaming.jtagPulse, liftInstruction,
    supportedFrom, List.countP_cons, Instruction.isStream, Instruction.Canonical,
    Streaming.Cell.PulseCanonical]

def image (d : Fin 256) : Compiled (source d) idlePins :=
  ⟨(source d).map encode, supported d, rfl⟩

theorem original_words (d : Fin 256) : (image d).words = (Streaming.jtagImage d).words := by
  simp only [image, Streaming.jtagImage, source, List.map_map, Function.comp_def, encode_lift]

def rowTms (pc : Nat) : Bool := pc < 5 || pc == 6 || pc == 10

def pulse (d : Fin 256) (tms : Bool) : Instruction :=
  liftInstruction (Streaming.jtagPulse d tms)

def row (d : Fin 256) (pc : Nat) : Instruction :=
  if pc = 9 then .stream (Streaming.jtagCell d) none
  else if pc = 12 then .halt else pulse d (rowTms pc)

theorem fetch (d : Fin 256) (pc : Nat) (bound : pc ≤ 12) :
    (image d).program.fetch pc = some (row d pc) := by
  rw [(image d).program_fetch pc (show pc < (source d).length by change pc < 13; omega)]
  have slots : pc = 0 ∨ pc = 1 ∨ pc = 2 ∨ pc = 3 ∨ pc = 4 ∨ pc = 5 ∨
      pc = 6 ∨ pc = 7 ∨ pc = 8 ∨ pc = 9 ∨ pc = 10 ∨ pc = 11 ∨ pc = 12 := by omega
  rcases slots with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

inductive ScanClock where
  | navigation (tms : Bool)
  | data (tms : Bool)
  deriving DecidableEq

def ScanClock.tms : ScanClock → Bool
  | .navigation bit | .data bit => bit

def scanClocks : Nat → List ScanClock
  | 0 => []
  | n+1 => List.replicate n (.data false) ++ [.data true]

def rowClocks (count : Nat) : Instruction → List ScanClock
  | .pulse c => [.navigation (c.highPins.levels[2])]
  | .stream _ _ => scanClocks count
  | _ => []

def schedule (d : Fin 256) (pc count : Nat) : List ScanClock :=
  ((source d).drop pc).flatMap (rowClocks count)

def pending (d : Fin 256) (s : State a) : List ScanClock :=
  (schedule d s.pc.toNat s.remaining.toNat).drop (if s.phase = .high then 1 else 0)

private theorem row_at (d : Fin 256) (pc : Nat) (bound : pc ≤ 12) :
    (source d)[pc]? = some (row d pc) := by
  rw [← (image d).program_fetch pc (show pc < (source d).length by change pc < 13; omega)]
  exact fetch d pc bound

private theorem schedule_row (d : Fin 256) (pc count : Nat) (bound : pc ≤ 12) :
    schedule d pc count = rowClocks count (row d pc) ++ schedule d (pc+1) count := by
  unfold schedule
  have cells := List.drop_eq_getElem_cons (l := source d) (i := pc) (by change pc < 13; omega)
  rw [cells,List.flatMap_cons]
  congr 2
  exact Option.some.inj ((List.getElem?_eq_getElem (by change pc < 13; omega)).symm.trans
    (row_at d pc bound))

private theorem schedule_suffix (d : Fin 256) (count : Nat) :
    schedule d 10 count = [.navigation true,.navigation false] := by
  change schedule (0 : Fin 256) 10 0 = _
  decide +kernel

def tck (s : State a) : Bool := s.pins.levels[1]

def rose (s next : State a) : Bool := !tck s && tck next

def active (s : State a) : Prop :=
  s.phase = .boundary ∨ s.phase = .low ∨ s.phase = .high

structure Positioned (d : Fin 256) (s : State a) : Prop where
  phase : s.phase = .fetch ∨ active s ∨ s.phase = .completed
  cursor : s.pc.toNat ≤ 12
  current : active s → s.pc.toNat < 12 ∧ s.current = row d s.pc.toNat
  scanLeft : active s → s.pc.toNat = 9 → 0 < s.remaining.toNat
  finished : s.phase = .completed → s.pc.toNat = 12
  clock : tck s = (s.phase == .high)
  pins : s.pins.enabled = 7#3

theorem positioned_start (d : Fin 256) (s : State a) (i : Input) :
    Positioned d (s.start (image d).program i) := by
  constructor <;> simp [State.start, active, tck, image, Compiled.program, idlePins]

private theorem pin_pulse (d : Fin 256) (tms : Bool) :
    ((pulse d tms).cell.lowPins.levels[1] = false) ∧
    ((pulse d tms).cell.highPins.levels[1] = true) ∧
    ((pulse d tms).cell.highPins.levels[2] = tms) ∧
    ((pulse d tms).cell.lowPins.enabled = 7#3) ∧ ((pulse d tms).cell.highPins.enabled = 7#3) := by
  cases tms <;> decide +revert +kernel

private theorem pin_scan (d : Fin 256) (high last bit : Bool) :
    let pins := (Streaming.jtagCell d).dataPins high last bit
    pins.levels[1] = high ∧ pins.levels[2] = last ∧ pins.enabled = 7#3 := by
  cases high <;> cases last <;> cases bit <;> decide +revert +kernel

private theorem pin_scan_low (d : Fin 256) (last : Bool) :
    let pins := (Streaming.jtagCell d).basePins false last
    pins.levels[1] = false ∧ pins.enabled = 7#3 := by
  cases last <;> decide +revert +kernel

private theorem pc_next (pc : BitVec 7) (bound : pc.toNat < 12) :
    (pc + 1#7).toNat = pc.toNat + 1 := by
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

def observed (s next : State a) : List ScanClock :=
  if rose s next then
    let tms := next.pins.levels[2]
    [if s.captures then .data tms else .navigation tms]
  else []

private theorem empty_schedule (d : Fin 256) (n : Nat) : schedule d 12 n = [] := by
  change schedule (0 : Fin 256) 12 0 = _
  decide +kernel

private theorem fetch_transition (d : Fin 256) (s : State a) (h : Positioned d s) (phase : s.phase = .fetch) :
    let n := engine (image d).program s
    Positioned d n ∧ pending d s = observed s n ++ pending d n := by
  have fetched := fetch d s.pc.toNat h.cursor
  have low : s.pins.levels[1] = false := by change tck s = false; rw [h.clock,phase]; rfl
  dsimp only
  by_cases stop : s.pc.toNat = 12
  · have e : engine (image d).program s = s.stop (image d).program false := by
      simp only [engine,phase,fetched]
      simp [row,stop]
    rw [e]
    constructor
    · constructor <;> simp [State.stop,stop,tck,active,image,Compiled.program,idlePins]
    · simp [observed,rose,tck,low,pending,phase,State.stop,stop,empty_schedule,image,Compiled.program,idlePins]
  · have bound : s.pc.toNat < 12 := by have := h.cursor; omega
    by_cases frame : s.pc.toNat = 9
    · by_cases zero : s.remaining = 0#16
      · have e : engine (image d).program s = {s with pc := s.pc+1} := by
          simp only [engine,phase,fetched]
          simp [row,frame,zero]
        have cursor := pc_next s.pc bound
        rw [e]
        constructor
        · constructor <;> simp [active,phase,cursor,frame,tck,low,h.pins]
        · have plan := schedule_row d s.pc.toNat s.remaining.toNat h.cursor
          rw [row,if_pos frame] at plan
          simpa [observed,rose,low,zero,pending,phase,cursor,rowClocks,scanClocks,tck] using plan
      · have e : engine (image d).program s =
            {s with
              phase := .boundary, current := .stream (Streaming.jtagCell d) none
              pins := (Streaming.jtagCell d).basePins false (s.remaining == 1#16)} := by
          simp only [engine,phase,fetched]
          simp [row,frame,zero]
        have live : 0 < s.remaining.toNat := by
          have nz : s.remaining.toNat ≠ 0 := fun eq =>
            zero (BitVec.eq_of_toNat_eq (by simpa using eq))
          omega
        rw [e]
        constructor
        · obtain ⟨clock,enabled⟩ := pin_scan_low d (s.remaining == 1#16)
          constructor <;> simp [active,tck,frame,row,bound,live,clock,enabled]
        · simp [observed,rose,low,pending,phase,tck,State.stop,image,Compiled.program,idlePins, (pin_scan_low d (s.remaining == 1#16)).1, (pin_pulse d (rowTms s.pc.toNat)).1]
    · have e : engine (image d).program s =
          {s with
            phase := .boundary, current := pulse d (rowTms s.pc.toNat)
            pins := (pulse d (rowTms s.pc.toNat)).cell.lowPins} := by
        simp only [engine,phase,fetched]
        simp [row,frame,stop,pulse,liftInstruction,Streaming.jtagPulse,Instruction.cell]
      rw [e]
      constructor
      · have clock := (pin_pulse d (rowTms s.pc.toNat)).1
        have enabled := (pin_pulse d (rowTms s.pc.toNat)).2.2.2.1
        constructor <;> simp [active,tck,row,frame,stop,bound,h.cursor,clock,enabled]
      · simp [observed,rose,low,pending,phase,tck,State.stop,image,Compiled.program,idlePins, (pin_scan_low d (s.remaining == 1#16)).1, (pin_pulse d (rowTms s.pc.toNat)).1]

private theorem current_kind (d : Fin 256) (s : State a) (h : Positioned d s) (on : active s) :
    (s.pc.toNat = 9 ∧ s.current = .stream (Streaming.jtagCell d) none) ∨
    (s.pc.toNat ≠ 9 ∧ s.current = pulse d (rowTms s.pc.toNat)) := by
  obtain ⟨bound,current⟩ := h.current on
  have stop : s.pc.toNat ≠ 12 := by omega
  by_cases frame : s.pc.toNat = 9 <;> simp [frame,stop,row] at current ⊢ <;> exact current

private theorem boundary_transition (d : Fin 256) (s : State a)
    (h : Positioned d s) (phase : s.phase = .boundary) :
    let n := engine (image d).program s
    Positioned d n ∧ pending d s = observed s n ++ pending d n := by
  have on : active s := Or.inl phase
  obtain ⟨bound,current⟩ := h.current on
  have live := h.scanLeft on
  have low : s.pins.levels[1] = false := by change tck s = false; rw [h.clock,phase]; rfl
  cases credit : s.canReserve with
  | false =>
    simp [engine,phase,credit,observed,rose,tck,low,h]
  | true =>
    rcases current_kind d s h on with ⟨frame,kind⟩ | ⟨frame,kind⟩
    · have pins := pin_scan d false s.lastCell
        (true && (Streaming.jtagCell d).transmit && s.selectedTx.data[31])
      dsimp only at pins
      simp only [Bool.true_and] at pins
      obtain ⟨clk,_,enabled⟩ := pins
      dsimp only
      simp only [engine,phase,credit,if_true,kind,Instruction.isStream,Instruction.cell]
      constructor
      · constructor <;>
          simp [active,tck,row,frame,bound,h.cursor,live,clk,enabled]
      · simp [pending,phase,observed,rose,tck,clk]
    · have ⟨clk,_,_,enabled,_⟩ := pin_pulse d (rowTms s.pc.toNat)
      have stream : (pulse d (rowTms s.pc.toNat)).isStream = false := rfl
      have stop : s.pc.toNat ≠ 12 := by omega
      dsimp only
      simp only [engine,phase,credit,if_true,kind,stream,Bool.false_eq_true,if_false]
      constructor
      · constructor <;> simp [active,tck,row,frame,stop,bound,h.cursor,live,clk,enabled]
      · simp [pending,phase,observed,rose,tck,clk]

private theorem scanClocks_cons (n : Nat) (live : 0 < n) :
    scanClocks n = .data (decide (n = 1)) :: (scanClocks n).drop 1 := by
  cases n with
  | zero => omega
  | succ n => cases n <;> rfl

private theorem schedule_scan_first (d : Fin 256) (s : State a) (frame : s.pc.toNat = 9)
    (live : 0 < s.remaining.toNat) :
    schedule d s.pc.toNat s.remaining.toNat =
      .data (s.remaining == 1#16) :: (schedule d s.pc.toNat s.remaining.toNat).drop 1 := by
  have bound : s.pc.toNat ≤ 12 := by omega
  have count : (s.remaining == 1#16) = decide (s.remaining.toNat = 1) := by
    apply Bool.eq_iff_iff.mpr
    simp [← BitVec.toNat_inj]
  rw [count,schedule_row d s.pc.toNat s.remaining.toNat bound,row,if_pos frame]
  simp only [rowClocks]
  have head := scanClocks_cons s.remaining.toNat live
  generalize scanClocks s.remaining.toNat = clocks at *
  -- The head is the only edge emitted on the transition into HIGH.
  cases clocks with
  | nil => simp_all
  | cons c cs =>
    simp only [List.drop_succ_cons,List.drop_zero,List.cons.injEq] at head
    simp [head.1]

private theorem low_transition (d : Fin 256) (s : State a)
    (h : Positioned d s) (phase : s.phase = .low) :
    let n := engine (image d).program s
    Positioned d n ∧ pending d s = observed s n ++ pending d n := by
  have on : active s := Or.inr (Or.inl phase)
  obtain ⟨bound,current⟩ := h.current on
  have live := h.scanLeft on
  have low : s.pins.levels[1] = false := by change tck s = false; rw [h.clock,phase]; rfl
  by_cases done : s.countdown = 0#8
  · rcases current_kind d s h on with ⟨frame,kind⟩ | ⟨frame,kind⟩
    · obtain ⟨clk,tms,enabled⟩ := pin_scan d true (s.remaining == 1#16) s.cellBit
      have cap : s.captures = true := by
        simp [State.captures,phase,done,kind,Instruction.isStream,Instruction.cell,
          Instruction.hasHighGuard,Streaming.jtagCell]
      have first := schedule_scan_first d s frame (live frame)
      dsimp only
      simp only [engine,phase,done,beq_self_eq_true,if_true,State.highPins,State.lastCell,kind,
        Instruction.isStream,Instruction.cell,Instruction.hasHighGuard,if_false,Bool.false_eq_true,
        Bool.true_and,State.enterHigh,State.captureData]
      constructor
      · constructor <;> simp [active,tck,row,frame,bound,h.cursor,current,live,clk,enabled]
      · simpa [pending,phase,observed,rose,tck,low,clk,tms,cap] using first
    · obtain ⟨_,clk,tms,_,enabled⟩ := pin_pulse d (rowTms s.pc.toNat)
      have stop : s.pc.toNat ≠ 12 := by omega
      have guard : (pulse d (rowTms s.pc.toNat)).hasHighGuard = false := rfl
      have stream : (pulse d (rowTms s.pc.toNat)).isStream = false := rfl
      have cap : s.captures = false := by simp [State.captures,kind,stream]
      have plan := schedule_row d s.pc.toNat s.remaining.toNat h.cursor
      rw [row,if_neg frame,if_neg stop] at plan
      have clocks : rowClocks s.remaining.toNat (pulse d (rowTms s.pc.toNat)) =
          [.navigation (rowTms s.pc.toNat)] := by
        change [ScanClock.navigation (pulse d (rowTms s.pc.toNat)).cell.highPins.levels[2]] = _
        simp [tms]
      rw [clocks] at plan
      dsimp only
      simp only [engine,phase,done,beq_self_eq_true,if_true,State.highPins,kind,stream,guard,
        Bool.false_eq_true,if_false,State.enterHigh,State.captureData]
      constructor
      · constructor <;> simp [active,tck,row,frame,stop,bound,h.cursor,live,clk,enabled]
      · have tail := congrArg (List.drop 1) plan
        simp [pending,phase,observed,rose,tck,low,cap,clk,tms,tail]
        exact plan
  · have e : engine (image d).program s = {s with countdown := s.countdown - 1} := by
      simp [engine,phase,done]
    rw [e]
    constructor
    · constructor <;> simp [active,phase,bound,current,h.cursor,live,tck,low,h.pins]
      exact live
    · simp [pending,observed,rose,tck,phase,low]

private theorem high_transition (d : Fin 256) (s : State a)
    (h : Positioned d s) (phase : s.phase = .high) :
    let n := engine (image d).program s
    Positioned d n ∧ pending d s = observed s n ++ pending d n := by
  have on : active s := Or.inr (Or.inr phase)
  obtain ⟨bound,current⟩ := h.current on
  have cursor := pc_next s.pc bound
  have live := h.scanLeft on
  have hi : tck s = true := by rw [h.clock,phase]; rfl
  have plan := schedule_row d s.pc.toNat s.remaining.toNat h.cursor
  by_cases done : s.countdown = 0#8
  · rcases current_kind d s h on with ⟨frame,kind⟩ | ⟨frame,kind⟩
    · have positive := live frame
      have rem : (s.remaining - 1#16).toNat = s.remaining.toNat - 1 := by
        apply BitVec.toNat_sub_of_le
        exact BitVec.le_def.mpr (by change 1 ≤ s.remaining.toNat; omega)
      have isStream : s.current.isStream = true := by rw [kind]; rfl
      have last : s.lastCell = (s.remaining == 1#16) := by simp [State.lastCell,isStream]
      obtain ⟨clk,enabled⟩ := pin_scan_low d (s.remaining == 1#16)
      rw [row,if_pos frame] at plan
      simp only [rowClocks] at plan
      by_cases more : s.remaining.toNat > 1
      · have still : 0 < s.remaining.toNat - 1 := by omega
        have suffix := schedule_suffix d (s.remaining.toNat - 1)
        have suffix' := schedule_suffix d s.remaining.toNat
        have tail : (scanClocks s.remaining.toNat ++ schedule d 10 s.remaining.toNat).drop 1 =
            scanClocks (s.remaining.toNat - 1) ++ schedule d 10 (s.remaining.toNat - 1) := by
          rw [suffix,suffix']
          generalize s.remaining.toNat = count at *
          cases count with
          | zero => omega
          | succ n => cases n with
            | zero => omega
            | succ n => rfl
        have nextPlan := schedule_row d s.pc.toNat (s.remaining.toNat-1) h.cursor
        rw [row,if_pos frame] at nextPlan
        dsimp only
        simp [engine,phase,done,more,kind,Instruction.isStream,Instruction.cell,last]
        constructor
        · constructor <;> simp [active,tck,row,frame,bound,h.cursor,rem,still,clk,enabled]
        · simp [pending,observed,rose,hi,phase,rem]
          rw [plan,nextPlan]
          simpa [frame,rowClocks] using tail
      · have one : s.remaining.toNat = 1 := by omega
        dsimp only
        simp [engine,phase,done,more,kind,Instruction.isStream,Instruction.cell,last]
        constructor
        · constructor <;> simp [active,tck,frame,cursor,clk,enabled]
        · simp [pending,observed,rose,hi,phase,rem,cursor]
          rw [plan]
          simp [one,scanClocks,frame,schedule_suffix]
    · have stop : s.pc.toNat ≠ 12 := by omega
      have stream : (pulse d (rowTms s.pc.toNat)).isStream = false := rfl
      have noLast : s.lastCell = false := by simp [State.lastCell,kind,stream]
      have ⟨clk,_,_,enabled,_⟩ := pin_pulse d (rowTms s.pc.toNat)
      have base : (pulse d (rowTms s.pc.toNat)).cell.basePins false false =
          (pulse d (rowTms s.pc.toNat)).cell.lowPins := rfl
      have tail := congrArg (List.drop 1) plan
      rw [row,if_neg frame,if_neg stop] at tail
      have clocks : rowClocks s.remaining.toNat (pulse d (rowTms s.pc.toNat)) =
          [ScanClock.navigation (pulse d (rowTms s.pc.toNat)).cell.highPins.levels[2]] := rfl
      simp only [clocks,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero] at tail
      dsimp only
      simp [engine,phase,done,kind,stream,noLast,base]
      constructor
      · have nextBound := h.cursor
        constructor <;> simp [active,tck,cursor,clk,enabled] <;> omega
      · simpa [pending,observed,rose,hi,phase,cursor] using tail
  · have e : engine (image d).program s = {s with countdown := s.countdown - 1} := by
      simp [engine,phase,done]
    rw [e]
    constructor
    · constructor <;> simp [active,phase,bound,current,h.cursor,live,tck,h.pins]
      · exact live
      · exact hi
    · simp [pending,observed,rose,phase,hi]

theorem positioned_clock (d : Fin 256) (s : State a) (i : Input) (h : Positioned d s) :
    let n := clock (image d).program i s
    Positioned d n ∧ pending d s = observed s n ++ pending d n := by
  have update : Positioned d (engine (image d).program s) ∧
      pending d s = observed s (engine (image d).program s) ++
        pending d (engine (image d).program s) := by
    rcases h.phase with phase | (phase | phase | phase) | phase
    · exact fetch_transition d s h phase
    · exact boundary_transition d s h phase
    · exact low_transition d s h phase
    · exact high_transition d s h phase
    · have low : tck s = false := by rw [h.clock,phase]; rfl
      simp [engine,phase,h,observed,rose,low]
  obtain ⟨n,flow⟩ := update
  exact ⟨⟨n.phase,n.cursor,n.current,n.scanLeft,n.finished,n.clock,n.pins⟩,flow⟩


/-- Ordinary service clocks between START and the final RELEASE. -/
def Unreleased (i : Input) : Prop := i.Runtime ∧ i.command ≠ 4#4

private theorem not_free (h : Positioned d s) : s.phase ≠ .free := by
  rcases h.phase with phase | (phase | phase | phase) | phase <;> simp [phase]

private theorem step_eq_clock (d : Fin 256) (s : State a) (i : Input)
    (h : Positioned d s) (ordinary : Unreleased i) :
    step (image d).program i s = clock (image d).program i s := by
  rcases ordinary with ⟨⟨cold,warm⟩,release⟩
  simp [step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,not_free h]

private theorem trace_step_eq_clock (s : State a) (i : Input) (trace : BitTrace)
    (h : Positioned d s) (ordinary : Unreleased i) :
    trace.step s i = trace.clock s i := by
  rcases ordinary with ⟨⟨cold,warm⟩,release⟩
  simp [BitTrace.step,cold,(show i.command ≠ 15#4 from warm),release,State.canStart,not_free h]

def ScanClock.sample (raw : BitVec 2) : ScanClock → List Bool
  | .navigation _ => []
  | .data _ => [raw[0]]

def sampledTdo (s next : State a) : List Bool :=
  (observed s next).flatMap (ScanClock.sample s.samplerSecond)

theorem rx_on_data_edge (d : Fin 256) (s : State a) (i : Input) (h : Positioned d s) :
    s.rxEvent = sampledTdo s (clock (image d).program i s) := by
  by_cases capture : s.captures = true
  · have waiting : s.phase ≠ .waiting := by
      rcases h.phase with phase | (phase | phase | phase) | phase <;> simp [phase]
    have ready : s.phase = .low ∧ s.countdown = 0#8 := by
      have cut := capture
      simp [State.captures,waiting,Bool.and_assoc] at cut
      exact ⟨cut.2.2.1,cut.2.2.2.1⟩
    obtain ⟨phase,done⟩ := ready
    have on : active s := Or.inr (Or.inl phase)
    obtain ⟨_,kind⟩ := (current_kind d s h on).resolve_right fun ⟨_,pulseRow⟩ => by
      simp [State.captures,pulseRow,pulse,liftInstruction,Streaming.jtagPulse,Instruction.isStream] at capture
    have high : (clock (image d).program i s).phase = .high := by
      simp [clock,engine,phase,done,kind,Instruction.hasHighGuard,State.enterHigh]
    have rise : rose s (clock (image d).program i s) = true := by
      rw [rose,h.clock,(positioned_clock d s i h).1.clock,phase,high]
      rfl
    have port : s.current.cell.rxInput.val = 0 := by rw [kind]; rfl
    simp [State.rxEvent,sampledTdo,observed,rise,capture,port,ScanClock.sample]
  · simp [State.rxEvent,sampledTdo,observed,capture,ScanClock.sample]

def wireRun (d : Fin 256) (s : State a) : List Input → List ScanClock
  | [] => []
  | i :: rest =>
    let next := step (image d).program i s
    observed s next ++ wireRun d next rest

def tdoRun (d : Fin 256) (s : State a) : List Input → List Bool
  | [] => []
  | i :: rest =>
    let next := step (image d).program i s
    sampledTdo s next ++ tdoRun d next rest

theorem run_schedule (d : Fin 256) (s : State a) (inputs : List Input)
    (h : Positioned d s) (ordinary : ∀ i ∈ inputs, Unreleased i) :
    let last := run (image d).program s inputs
    Positioned d last ∧ pending d s = wireRun d s inputs ++ pending d last := by
  induction inputs generalizing s with
  | nil => exact ⟨h,rfl⟩
  | cons i rest ih =>
    have first := ordinary i (List.mem_cons_self)
    have actual := step_eq_clock d s i h first
    obtain ⟨next,edge⟩ := positioned_clock d s i h
    rw [← actual] at next edge
    obtain ⟨last,tail⟩ := ih _ next (fun j member => ordinary j (List.mem_cons_of_mem _ member))
    refine ⟨last,?_⟩
    change pending d s = (observed s (step (image d).program i s) ++
      wireRun d (step (image d).program i s) rest) ++
      pending d (run (image d).program (step (image d).program i s) rest)
    rw [List.append_assoc,← tail]
    exact edge

theorem tdo_trace (d : Fin 256) (s : State a) (inputs : List Input) (trace : BitTrace)
    (h : Positioned d s) (ordinary : ∀ i ∈ inputs, Unreleased i) :
    (traceRun (image d).program s trace inputs).captured = trace.captured ++ tdoRun d s inputs := by
  induction inputs generalizing s trace with
  | nil => simp [traceRun,tdoRun]
  | cons i rest ih =>
    have first := ordinary i (List.mem_cons_self)
    have actual := step_eq_clock d s i h first
    have next := (positioned_clock d s i h).1
    rw [← actual] at next
    rw [traceRun,ih _ _ next (fun j member => ordinary j (List.mem_cons_of_mem _ member))]
    rw [trace_step_eq_clock s i trace h first]
    simp [BitTrace.clock,tdoRun,actual,rx_on_data_edge d s i h,List.append_assoc]

private theorem schedule_start (d : Fin 256) (count : Nat) :
    schedule d 0 count = (beforeScan d).map .navigation ++ scanClocks count ++
      (afterScan d).map .navigation := by
  rfl

theorem scanClocks_tms (d : Fin 256) (body : List Bool) (last : Bool) :
    (scanClocks (body ++ [last]).length).map ScanClock.tms = dataClocks d (body ++ [last]) := by
  simp [data_clock_bits,scanClocks,List.map_replicate,ScanClock.tms]

/-- Exact digital TCK/TMS trace for a completed START with a positive count. -/
theorem completed_scan (d : Fin 256) (before : State a) (start : Input) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Unreleased i)
    (completed : (run (image d).program (before.start (image d).program start) inputs).phase = .completed)
    (positive : 0 < start.startCount.toNat) :
    let wire := wireRun d (before.start (image d).program start) inputs
    wire = (beforeScan d).map .navigation ++ scanClocks start.startCount.toNat ++
      (afterScan d).map .navigation ∧
    ∀ tap, (walk tap (wire.map ScanClock.tms)).1 = .idle ∧
      (walk tap (wire.map ScanClock.tms)).2 = start.startCount.toNat + (if tap = .shiftDR then 1 else 0) := by
  obtain ⟨position,edges⟩ := run_schedule d _ inputs (positioned_start d before start) ordinary
  have cursor := position.finished completed
  have exactWire : wireRun d (before.start (image d).program start) inputs =
      (beforeScan d).map .navigation ++ scanClocks start.startCount.toNat ++
      (afterScan d).map .navigation := by
    rw [← schedule_start]
    have empty : pending d (run (image d).program (before.start (image d).program start) inputs) = [] := by
      simp [pending,completed,cursor,empty_schedule]
    rw [empty,List.append_nil] at edges
    exact edges.symm
  refine ⟨exactWire, ?_⟩
  intro tap
  let body := List.replicate (start.startCount.toNat - 1) false
  have length : start.startCount.toNat = (body ++ [false]).length := by
    simp [body]
    omega
  rw [exactWire,length,List.map_append,List.map_append,scanClocks_tms]
  simpa [ScanClock.tms,List.map_map,Function.comp_def,
    reset_preamble_count,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    compiled_scan_control tap d body false

def ScanClock.isData : ScanClock → Bool
  | .navigation _ => false
  | .data _ => true

theorem tdo_count (d : Fin 256) (s : State a) (inputs : List Input) :
    (tdoRun d s inputs).length = (wireRun d s inputs).countP ScanClock.isData := by
  have count (raw : BitVec 2) (edges : List ScanClock) :
      (edges.flatMap (ScanClock.sample raw)).length = edges.countP ScanClock.isData := by
    induction edges with
    | nil => rfl
    | cons edge rest ih =>
      cases edge <;> simp [ScanClock.sample,ScanClock.isData,ih,List.countP_cons,Nat.add_comm]
  induction inputs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp [tdoRun,wireRun,ih,sampledTdo,count,List.countP_append]

theorem completed_tdo_count (d : Fin 256) (before : State a) (start : Input) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, Unreleased i)
    (completed : (run (image d).program (before.start (image d).program start) inputs).phase = .completed)
    (positive : 0 < start.startCount.toNat) :
    (tdoRun d (before.start (image d).program start) inputs).length = start.startCount.toNat := by
  have navigation (bits : List Bool) : (bits.map ScanClock.navigation).countP ScanClock.isData = 0 := by
    induction bits with
    | nil => rfl
    | cons bit bits ih => simp [ScanClock.isData,ih]
  rw [tdo_count,(completed_scan d before start inputs ordinary completed positive).1]
  cases start.startCount.toNat <;>
    simp [List.countP_append,navigation,scanClocks,ScanClock.isData,List.countP_cons,List.countP_replicate,
      Nat.add_comm]

/-- A serviced scan reaches completed, including when the host parks it for finite intervals. -/
theorem eventually_completed (d : Fin 256) (before : State a) (start : Input) (incoming : Nat → Input)
    (ordinary : ∀ n, Unreleased (incoming n))
    (credits : ∀ n, (EventualService.state (image d).program (before.start (image d).program start)
      incoming n).phase = .boundary →
        ∃ m, n ≤ m ∧ (EventualService.state (image d).program (before.start (image d).program start)
          incoming m).canReserve = true) :
    ∃ edges,
      (run (image d).program (before.start (image d).program start)
        (EventualService.clocks incoming edges)).phase = .completed := by
  have admissible : ∀ edges i, i ∈ EventualService.clocks incoming edges → Unreleased i := by
    intro edges i member
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp member
    exact ordinary n
  have positions := fun edges => (run_schedule d _ (EventualService.clocks incoming edges)
    (positioned_start d before start) (admissible edges)).1
  have fair : EventualService.Fair (image d).program (before.start (image d).program start) incoming := by
    refine ⟨credits, ?_⟩
    intro n waiting
    rw [EventualService.state_eq_run] at waiting
    rcases (positions n).phase with phase | (phase | phase | phase) | phase <;> simp_all
  obtain ⟨edges,retained⟩ := EventualService.started (image d).program before start incoming
    (fun n => (ordinary n).1) fair
  refine ⟨edges,?_⟩
  rcases (positions edges).phase with phase | (phase | phase | phase) | phase <;>
    simp [phase,Phase.retained] at retained ⊢

/-- The peer's TDO value at the sampling aperture two core clocks before the data edge. -/
theorem tdo_after_two (d : Fin 256) (s : State a) (earlier : List Input) (first second edge : Input) :
    let before := run (image d).program s (earlier ++ [first,second])
    first.Runtime → second.Runtime →
    sampledTdo before (step (image d).program edge before) =
      (observed before (step (image d).program edge before)).flatMap (ScanClock.sample first.rawInputs) := by
  intro before one two
  rw [sampledTdo]
  rw [(run_two_samples (image d).program s earlier first second one two).2]

end Pinwheel.Program.StreamingJTAG
