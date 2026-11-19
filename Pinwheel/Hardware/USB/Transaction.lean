import Pinwheel.Hardware.USB.Refinement

namespace Pinwheel.Hardware.USB
open Pinwheel.Hardware
open Pinwheel.USBClockFeasibility Pinwheel.USBOnlineFeasibility Pinwheel.USBPacketFeasibility
open Pinwheel.USBWaveformConstruction (ackClocks ackSymbols padValue)

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def wireCode : Wire → BitVec 2
  | .se0 => 0 | .k => 1 | .j => 2 | .se1 => 3

def idleInput : Values Input := fun _ => 0

theorem idle_quiet : Quiet idleInput := ⟨rfl,rfl⟩

def idleWithRaw (raw : Wire) : Values Input
  | _, .rawInputs => wireCode raw
  | _, _ => 0

structure Live (s : CoreState) (code : BitVec 3) : Prop where
  busy : s (.base .phase) = 7
  state : s .mode = code
  rxEmpty : s (.base .rxCount) = 0
  released : s (.base .enabled) = 0

theorem Live.active (h : Live s code) (n : code ≠ 0) : s .mode ≠ 0 := by
  rw [h.state]
  exact n

theorem live_next (i : Values Input) (s : CoreState) (oldCode newCode : BitVec 3)
    (q : Quiet i) (old : Live s oldCode) (nonzero : oldCode ≠ 0)
    (mode : circuit.step i s .mode = newCode)
    (good : failed.eval i s = 0#1) (pending : sent.eval i s = 0#1) :
    Live (circuit.step i s) newCode := by
  have fields := live_publication i s q old.busy (old.active nonzero)
  simp [good,pending,old.rxEmpty] at fields
  exact ⟨fields.2.2.1,mode,fields.2.2.2.1,fields.1⟩

theorem failed_next (i : Values Input) (s : CoreState) (oldCode : BitVec 3)
    (q : Quiet i) (old : Live s oldCode) (nonzero : oldCode ≠ 0)
    (bad : failed.eval i s = 1#1) (pending : sent.eval i s = 0#1) :
    let n : CoreState := circuit.step i s
    n .mode = 0 ∧ n (.base .phase) = 6 ∧ n (.base .enabled) = 0 ∧ n (.base .rxCount) = 0 := by
  have fields := live_publication i s q old.busy (old.active nonzero)
  simp [bad,pending,old.rxEmpty] at fields
  dsimp only
  rw [eval_next_mode_live i s q old.busy]
  simp [Expr.eval,either,bad,pending,fields]

theorem evaluate_not_sending (i : Values Input) (s : CoreState) (n : s .mode ≠ 5#3) :
    sent.eval i s = 0#1 := by simp [sent,sending,isMode,eq,both,Expr.eval,n]

theorem wire_stays_disabled (i : Values Input) (s : CoreState) (code : BitVec 3)
    (live : Live s code) (n : code ≠ 5) : circuit.observe i s .enabled = 0 := by
  have mode : s .mode ≠ 5#3 := fun h => n (live.state.symm.trans h)
  simp [circuit,Circuit.observe,output,sending,isMode,eq,Expr.eval,mode,
    StreamingReady.Core.output,baseState,live.released]

theorem installed_receiver (i : Values Input) (s : CoreState) (q : Quiet i)
    (fetch : s (.base .phase) = 1#3)
    (inBounds : (s (.base .pc)).toNat < (s (.base .count)).toNat)
    (stored : s (.base (.word ((s (.base .pc)).extractLsb' 0 6))) = word)
    (count : s (.base .remaining) = 64#16)
    (idlePins : s (.base .idleEnabled) = 0#3)
    (txEmpty : s (.base .txCount) = 0#4) (rxEmpty : s (.base .rxCount) = 0#4)
    (noTX : s (.base .txValid) = 0#6) (noRX : s (.base .rxUsed) = 0#6)
    (nothingProduced : s (.base .rxProduced) = 0#16) :
    entering.eval i s = 1#1 := by
  have readEntry : StreamingReady.Core.entryWord.eval i (baseState s) = word := by
    rw [StreamingReady.Core.entryWord,Execution.readTree_correct]
    exact stored
  have reset : StreamingReady.Core.resetting.eval i (baseState s) = 0 := by
    simpa using quiet_reset i s q
  rw [entering,eval_lift]
  simp [StreamingReady.Core.fetching,StreamingReady.Core.both,StreamingReady.Core.isPhase,
    StreamingReady.Core.entryBounds,StreamingReady.Core.drained,Expr.eval,baseState,
    reset,readEntry,fetch,inBounds,count,idlePins,txEmpty,rxEmpty,noTX,noRX,nothingProduced]

theorem gate_accepts_word (i : Values Input) (s : CoreState) (q : Quiet i)
    (entered : entering.eval i s = 1#1)
    (idle : s .mode = 0#3)
    (empty : s (.base .rxCount) = 0)
    (first : s (.base (.rxWord 0#1)) = 0)
    (second : s (.base (.rxWord 1#1)) = 0) :
    let n : CoreState := circuit.step i s
    Live n 1 ∧ n .age = 0 ∧ n .timer = 0 ∧ getCapture n = {} := by
  have clearReset := quiet_reset i s q
  have k : clocked.eval i s = 0#1 := by
    simp [clocked,receiving,waiting,isMode,eq,both,either,Expr.eval,idle]
  have waitingBit : logicalBit.eval i s = 0#1 := by
    simp [logicalBit,symbol,both,Expr.eval,k]
  have gate {w : Nat} (r : StreamingReady.Core.Register 1 w) :
      circuit.step i s (.base r) = (receivingBase r).eval i s := by
    simp [Circuit.step,circuit,next,nextBase,Expr.eval,clearReset,entered,both,either]
  have cleared {w : Nat} (r : Register w) (v : BitVec w) (e : E w) (body : next r = clear v e) :
      circuit.step i s r = v := by
    change (next r).eval i s = v
    rw [body]
    simp [clear,Expr.eval,clearReset,entered,either]
  have mode : circuit.step i s .mode = 1#3 := by
    simp [Circuit.step,circuit,next,nextMode,Expr.eval,clearReset,entered]
  refine ⟨⟨?_,mode,?_,?_⟩,cleared .age 0 _ rfl,cleared .timer 0 _ rfl,?_⟩
  · simp [gate,receivingBase,Expr.eval,entered]
  · simp [gate,receivingBase,Expr.eval,sent,sending,isMode,eq,both,idle,empty]
  · simp [gate,receivingBase,Expr.eval]
  have levelNext := cleared .level 0 _ rfl
  have countdown := cleared .sample 0 _ rfl
  have prev := cleared .previous 0 _ rfl
  have ones := cleared .ones 0 _ rfl
  have count := cleared .consumed 0 _ rfl
  have headerNext := cleared .header 0 _ rfl
  have crc := cleared .crc 0xFFFF _ rfl
  simp [getCapture,levelNext,countdown,prev,ones,count,headerNext,crc,gate,receivingBase,
    Expr.eval,dataBit,both,waitingBit,first,second]

theorem waiting_idle (i : Values Input) (s : CoreState) (q : Quiet i)
    (h : Live s 1) (raw : s (.base .stage2) = 2#2) (early : (s .age).toNat < 127) :
    Live (circuit.step i s) 1 ∧ getCapture (circuit.step i s) = getCapture s := by
  have mode : s .mode = 1#3 := h.state
  have beforeDeadline : (s .age).toNat < 2047 := by omega
  have notTimeout : s .age ≠ 127#12 := fun e => by
    have v := (isNat (s .age) 127 (by decide)).mp e
    omega
  have stopped : clocked.eval i s = 0#1 := by
    simp [clocked,receiving,waiting,isMode,eq,both,either,Expr.eval,wireK,wireJ,wire,mode,raw]
  have good : failed.eval i s = 0#1 := by
    simp [failed,late,sending,waiting,receiving,marker,isMode,eq,both,either,lt,Expr.eval,
      wireJ,wireK,wireSE0,wireSE1,wire,mode,raw,beforeDeadline,notTimeout]
  have pending := evaluate_not_sending i s (by simp [mode])
  have stays : circuit.step i s .mode = 1#3 := by
    rw [eval_next_mode_live i s q h.busy]
    simp [good,pending,waiting,receiving,marker,delaying,isMode,eq,both,either,Expr.eval,
      wireJ,wireK,wireSE0,wire,mode,raw]
  exact ⟨live_next i s 1 1 q h (by decide) stays good pending,
    capture_not_clocked i s q h.busy (h.active (by decide)) stopped⟩

theorem waiting_timeout (i : Values Input) (s : CoreState) (q : Quiet i)
    (h : Live s 1) (raw : s (.base .stage2) = 2#2) (elapsed : (s .age).toNat = 127) :
    let n : CoreState := circuit.step i s
    n .mode = 0 ∧ n (.base .phase) = 6 ∧ n (.base .enabled) = 0 ∧ n (.base .rxCount) = 0 := by
  have time : s .age = 127#12 := (isNat (s .age) 127 (by decide)).mpr elapsed
  have bad : failed.eval i s = 1#1 := by
    simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
      wireJ,wireK,wireSE0,wireSE1,wire,raw,h.state,time]
  exact failed_next i s 1 q h (by decide) bad (evaluate_not_sending i s (by simp [h.state]))

theorem pulse_data_step (i : Values Input) (s : CoreState) (q : Quiet i)
    (starting : oldCode = 1 ∨ oldCode = 2) (h : Live s oldCode)
    (bit : Bool) (raw : s (.base .stage2) = (if bit then 1 else 2))
    (startsWithK : oldCode = 1 → bit = true) (early : (s .age).toNat < 2047)
    (ones : (s .ones).toNat ≤ 6) (count : (s .consumed).toNat ≤ 97)
    (cap : Capture) (sampled : sampleOnTick (getCapture s) bit = some cap) :
    Live (circuit.step i s) 2 ∧ getCapture (circuit.step i s) = cap := by
  have live : s .mode ≠ 0 := h.active (by rcases starting with e|e <;> simp [e])
  have tick : clocked.eval i s = 1 := by
    rcases starting with e|e
    · have mode : s .mode = 1#3 := h.state.trans e
      have k := startsWithK e
      simp [clocked,receiving,waiting,isMode,eq,both,either,Expr.eval,wireK,wireJ,wire,mode,raw,k]
    · exact eval_clocked_body i s bit raw (h.state.trans e)
  have update := sampled_decoder i s bit q h.busy live (eval_wireK i s bit raw) tick ones count
  have noStuff : (both symbol (both stuffed decoded)).eval i s = 0#1 := by
    rw [sampled] at update
    by_cases fault : (both symbol (both stuffed decoded)).eval i s = 1#1
    · simp [fault] at update
    · exact (BitVec.eq_zero_or_eq_one _).resolve_right fault
  have nextCapture : getCapture (circuit.step i s) = cap := by
    have result : some cap = some (getCapture (circuit.step i s)) := by
      simpa [noStuff,sampled] using update
    exact (Option.some.inj result).symm
  have good : failed.eval i s = 0#1 := by
    rcases starting with e|e
    · have mode : s .mode = 1#3 := h.state.trans e
      have k := startsWithK e
      simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
        wireJ,wireK,wireSE0,wireSE1,wire,mode,raw,k,early]
    · have mode : s .mode = 2#3 := h.state.trans e
      have f := noStuff
      simp only [both,Expr.eval] at f
      cases bit <;>
        simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
          wireJ,wireK,wireSE0,wireSE1,wire,mode,raw,early,f]
  have pending : sent.eval i s = 0#1 := by
    apply evaluate_not_sending
    rcases starting with e|e <;> simp [h.state,e]
  have came : circuit.step i s .mode = 2#3 := by
    rw [eval_next_mode_live i s q h.busy]
    rcases starting with e|e
    · have mode : s .mode = 1#3 := h.state.trans e
      simp [good,pending,waiting,isMode,eq,both,either,Expr.eval,wireK,wire,mode,raw,startsWithK e]
    · have mode : s .mode = 2#3 := h.state.trans e
      cases bit <;> simp [good,pending,waiting,receiving,marker,delaying,isMode,eq,both,either,Expr.eval,
        wireJ,wireK,wireSE0,wire,mode,raw]
  exact ⟨live_next i s oldCode 2 q h (fun n => live (h.state.trans n)) came good pending,nextCapture⟩

theorem hold_capture (i : Values Input) (s : CoreState) (q : Quiet i) (h : Live s code)
    (afterBody : code = 3 ∨ code = 4 ∨ code = 5) :
    getCapture (circuit.step i s) = getCapture s := by
  rcases afterBody with e | e | e <;>
    apply capture_not_clocked i s q h.busy (h.active (by simp [e])) <;>
    simp [clocked,waiting,receiving,isMode,eq,both,either,Expr.eval,h.state,e]

theorem marker_clock (i : Values Input) (s : CoreState) (q : Quiet i)
    (stage : oldCode = 2 ∨ oldCode = 3) (h : Live s oldCode)
    (raw : s (.base .stage2) = 0#2) (early : (s .age).toNat < 2047)
    (room : oldCode = 3 → (s .timer).toNat < 33) :
    Live (circuit.step i s) 3 ∧ getCapture (circuit.step i s) = getCapture s ∧
    (circuit.step i s .timer).toNat = (if oldCode = 2 then 1 else (s .timer).toNat+1) := by
  have nz : oldCode ≠ 0 := by rcases stage with e|e <;> simp [e]
  have stopped : clocked.eval i s = 0#1 := by
    rcases stage with e|e <;> simp [clocked,waiting,receiving,isMode,eq,both,either,Expr.eval,
      wireK,wireJ,wire,raw,h.state,e]
  have proofCap := capture_not_clocked i s q h.busy (h.active nz) stopped
  have pending : sent.eval i s = 0#1 := by
    apply evaluate_not_sending
    rcases stage with e|e <;> simp [h.state,e]
  have good : failed.eval i s = 0#1 := by
    have noSymbol : symbol.eval i s = 0#1 := by simp [symbol,both,Expr.eval,stopped]
    rcases stage with e|e
    · simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
        wireJ,wireK,wireSE0,wireSE1,wire,raw,h.state,e,early,noSymbol]
    · have width := room e
      simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
        wireJ,wireK,wireSE0,wireSE1,wire,raw,h.state,e,early,timerLt,width]
  have nextMode : circuit.step i s .mode = 3#3 := by
    rw [eval_next_mode_live i s q h.busy]
    rcases stage with e|e <;>
      simp [good,pending,waiting,receiving,marker,delaying,isMode,eq,both,either,Expr.eval,
        wireJ,wireK,wireSE0,wire,raw,h.state,e]
  refine ⟨live_next i s oldCode 3 q h nz nextMode good pending, proofCap, ?_⟩
  rw [timer_update i s q h.busy]
  rcases stage with e|e
  · simp [receiving,marker,sending,delaying,isMode,eq,both,either,Expr.eval,wireJ,wireSE0,wire,raw,h.state,e]
  · have width := room e
    simp [receiving,marker,sending,delaying,isMode,eq,both,either,Expr.eval,wireJ,wireSE0,wire,raw,h.state,e] <;>
      omega

theorem arm_ack (i : Values Input) (s : CoreState) (q : Quiet i) (h : Live s 3)
    (raw : s (.base .stage2) = 2#2) (early : (s .age).toNat < 2047)
    (widthLo : 31 ≤ (s .timer).toNat) (widthHi : (s .timer).toNat < 34)
    (data : ∃ p, verifyFrame (getCapture s) = .data p) :
    Live (circuit.step i s) 4 ∧ getCapture (circuit.step i s) = getCapture s ∧
    (circuit.step i s .timer).toNat = 46 := by
  have accepts : frameOK.eval i s = 1#1 := (eval_frameOK i s).mpr data
  have pending := evaluate_not_sending i s (by simp [h.state])
  have width := Nat.not_lt.mpr widthLo
  have good : failed.eval i s = 0#1 := by
    simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
      wireJ,wireK,wireSE0,wireSE1,wire,raw,h.state,early,timerLt,markerWidthOK,width,widthHi,accepts]
  have nextMode : circuit.step i s .mode = 4#3 := by
    rw [eval_next_mode_live i s q h.busy]
    simp [good,pending,waiting,receiving,marker,delaying,isMode,eq,both,either,Expr.eval,
      wireJ,wireK,wireSE0,wire,raw,h.state]
  refine ⟨live_next i s 3 4 q h (by decide) nextMode good pending,
    hold_capture i s q h (Or.inl rfl),?_⟩
  rw [timer_update i s q h.busy]
  simp [receiving,marker,sending,delaying,isMode,eq,both,either,Expr.eval,wireJ,wireSE0,wire,raw,h.state]

theorem reject_marked_packet (i : Values Input) (s : CoreState) (q : Quiet i) (h : Live s 3)
    (raw : s (.base .stage2) = 2#2)
    (invalid : ¬ ∃ p, verifyFrame (getCapture s) = .data p) :
    let n : CoreState := circuit.step i s
    n .mode = 0 ∧ n (.base .phase) = 6 ∧ n (.base .enabled) = 0 ∧ n (.base .rxCount) = 0 := by
  have refuses : frameOK.eval i s = 0#1 := by
    exact (BitVec.eq_zero_or_eq_one _).resolve_right (fun ok => invalid ((eval_frameOK i s).mp ok))
  have bad : failed.eval i s = 1#1 := by
    simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
      wireJ,wireK,wireSE0,wireSE1,wire,raw,h.state,markerWidthOK,refuses]
  exact failed_next i s 3 q h (by decide) bad (evaluate_not_sending i s (by simp [h.state]))

theorem refuse_bad_stuffing (i : Values Input) (s : CoreState) (q : Quiet i) (h : Live s 2)
    (bit : Bool) (raw : s (.base .stage2) = (if bit then 1 else 2))
    (ones : (s .ones).toNat ≤ 6) (count : (s .consumed).toNat ≤ 97)
    (invalid : sampleOnTick (getCapture s) bit = none) :
    let n : CoreState := circuit.step i s
    n .mode = 0 ∧ n (.base .phase) = 6 ∧ n (.base .enabled) = 0 ∧ n (.base .rxCount) = 0 := by
  have model := sampled_decoder i s bit q h.busy (h.active (by decide))
    (eval_wireK i s bit raw) (eval_clocked_body i s bit raw h.state) ones count
  have rejected : (both symbol (both stuffed decoded)).eval i s = 1#1 := by
    by_cases flag : (both symbol (both stuffed decoded)).eval i s = 1#1
    · exact flag
    · have branches : (both symbol (both stuffed decoded)).eval i s ≠ (1 : BitVec 1) := flag
      simp [invalid,branches] at model
      exact model
  simp only [both,Expr.eval] at rejected
  have bad : failed.eval i s = 1#1 := by
    cases bit <;>
      simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
        wireJ,wireK,wireSE0,wireSE1,wire,raw,h.state,rejected]
  exact failed_next i s 2 q h (by decide) bad (evaluate_not_sending i s (by simp [h.state]))

theorem refuse_bad_marker (i : Values Input) (s : CoreState) (q : Quiet i) (h : Live s 3)
    (invalid : (s (.base .stage2) = 2#2 ∧ (s .timer).toNat < 31) ∨
      (s (.base .stage2) = 0#2 ∧ 33 ≤ (s .timer).toNat) ∨
      (s (.base .stage2) ≠ 0#2 ∧ s (.base .stage2) ≠ 2#2)) :
    let n : CoreState := circuit.step i s
    n .mode = 0 ∧ n (.base .phase) = 6 ∧ n (.base .enabled) = 0 ∧ n (.base .rxCount) = 0 := by
  have bad : failed.eval i s = 1#1 := by
    rcases invalid with ⟨raw,short⟩ | ⟨raw,long⟩ | ⟨noSE0,noJ⟩
    · simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
        wireJ,wireK,wireSE0,wireSE1,wire,raw,h.state,markerWidthOK,timerLt,short]
    · have full := Nat.not_lt.mpr long
      simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
        wireJ,wireK,wireSE0,wireSE1,wire,raw,h.state,timerLt,full]
    · simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,
        wireJ,wireK,wireSE0,wireSE1,wire,h.state,noSE0,noJ]
  exact failed_next i s 3 q h (by decide) bad (evaluate_not_sending i s (by simp [h.state]))

theorem watchdog_rejects (i : Values Input) (s : CoreState) (q : Quiet i) (h : Live s code)
    (live : code ≠ 0) (notACK : code ≠ 5) (timeout : 2047 ≤ (s .age).toNat) :
    let n : CoreState := circuit.step i s
    n .mode = 0 ∧ n (.base .phase) = 6 ∧ n (.base .enabled) = 0 ∧ n (.base .rxCount) = 0 := by
  have m : s .mode ≠ 5#3 := fun e => notACK (h.state.symm.trans e)
  have day : ¬ (s .age).toNat < 2047 := Nat.not_lt.mpr timeout
  have bad : failed.eval i s = 1#1 := by
    simp [failed,late,sending,isMode,eq,both,either,lt,Expr.eval,m,day]
  exact failed_next i s code q h live bad (evaluate_not_sending i s m)

theorem wait_to_ack (i : Values Input) (s : CoreState) (q : Quiet i) (h : Live s 4)
    (early : (s .age).toNat < 2047) (remaining : 0 < (s .timer).toNat) :
    let due := (s .timer).toNat = 1
    let n : CoreState := circuit.step i s
    Live n (if due then 5 else 4) ∧ getCapture n = getCapture s ∧
    (n .timer).toNat = (if due then 304 else (s .timer).toNat-1) := by
  have pending := evaluate_not_sending i s (by simp [h.state])
  have good : failed.eval i s = 0#1 := by
    simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,h.state,early]
  have due : (s .timer).toNat < 2 ↔ (s .timer).toNat = 1 := by omega
  have nextMode : circuit.step i s .mode = (if (s .timer).toNat = 1 then 5 else 4) := by
    rw [eval_next_mode_live i s q h.busy]
    by_cases finished : (s .timer).toNat = 1
    · have soon := due.mpr finished
      simp [good,pending,waiting,receiving,marker,delaying,isMode,eq,both,either,Expr.eval,
        lt,timerLt,h.state,finished,soon]
    · have later : ¬ (s .timer).toNat < 2 := fun h => finished (due.mp h)
      have width : 2 ≤ (s .timer).toNat := Nat.le_of_not_lt later
      simp [good,pending,waiting,receiving,marker,delaying,isMode,eq,both,either,Expr.eval,
        lt,timerLt,h.state,finished,later,width]
  dsimp only
  refine ⟨live_next i s 4 _ q h (by decide) nextMode good pending,
    hold_capture i s q h (Or.inr (Or.inl rfl)),?_⟩
  rw [timer_update i s q h.busy]
  by_cases finished : (s .timer).toNat = 1
  · have soon := due.mpr finished
    simp [receiving,marker,sending,delaying,isMode,eq,both,either,Expr.eval,
      lt,timerLt,h.state,finished,soon]
  · have later : ¬ (s .timer).toNat < 2 := fun h => finished (due.mp h)
    have width : 2 ≤ (s .timer).toNat := Nat.le_of_not_lt later
    simp [receiving,marker,sending,delaying,isMode,eq,both,either,Expr.eval,
      lt,timerLt,h.state,finished,later,width]
    exact BitVec.toNat_sub_of_le (show (1#9).toNat ≤ (s .timer).toNat from by
      change 1 ≤ (s .timer).toNat
      omega)

theorem ack_tick (i : Values Input) (s : CoreState) (q : Quiet i) (h : Live s 5)
    (remaining : 1 < (s .timer).toNat) :
    Live (circuit.step i s) 5 ∧ getCapture (circuit.step i s) = getCapture s ∧
    (circuit.step i s .timer).toNat = (s .timer).toNat-1 := by
  have more : ¬ (s .timer).toNat < 2 := by omega
  have pending : sent.eval i s = 0#1 := by
    simp [sent,sending,isMode,eq,both,Expr.eval,timerLt,lt,h.state,more]
  have good : failed.eval i s = 0#1 := by
    simp [failed,late,waiting,receiving,marker,sending,isMode,eq,both,either,lt,Expr.eval,h.state]
  have nextMode : circuit.step i s .mode = 5#3 := by
    rw [eval_next_mode_live i s q h.busy]
    simp [good,pending,waiting,receiving,marker,delaying,isMode,eq,both,either,Expr.eval,h.state]
  refine ⟨live_next i s 5 5 q h (by decide) nextMode good pending,
    hold_capture i s q h (Or.inr (Or.inr rfl)),?_⟩
  rw [timer_update i s q h.busy]
  simp [receiving,marker,sending,delaying,isMode,eq,both,either,Expr.eval,h.state]
  exact BitVec.toNat_sub_of_le (show (1#9).toNat ≤ (s .timer).toNat from by
    change 1 ≤ (s .timer).toNat
    omega)

end Pinwheel.Hardware.USB
