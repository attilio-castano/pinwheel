import Pinwheel.Hardware.USB.Core
import Pinwheel.Program.StreamingReadyCompile

/-! The receiver proof is stated against the expressions emitted by the USB
    core. The legacy core remains the owner of the quad request state. -/
namespace Pinwheel.Hardware.USB
open Pinwheel.Hardware
open Pinwheel.USBOnlineFeasibility Pinwheel.USBPacketFeasibility

set_option maxRecDepth 4096
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

abbrev CoreState := Values Register

def baseState (s : CoreState) : Values (StreamingReady.Core.Register 1) :=
  fun r => s (.base r)

@[simp] theorem eval_lift (e : StreamingReady.Core.E 1 w) (i : Values Input) (s : CoreState) :
    (lift e).eval i s = e.eval i (baseState s) := by
  rw [lift, Expr.eval_bind]
  rfl

def Quiet (i : Values Input) : Prop := i .initialize = 0 ∧ i .command = 0

theorem quiet_reset (i : Values Input) (s : CoreState) (quiet : Quiet i) :
    (lift StreamingReady.Core.resetting).eval i s = 0 := by
  rw [eval_lift]
  simp [StreamingReady.Core.resetting, StreamingReady.Core.either, StreamingReady.Core.warm,
    StreamingReady.Core.both, StreamingReady.Core.cold, StreamingReady.Core.cmd, Expr.eval, quiet.1, quiet.2]

theorem no_reentry (i : Values Input) (s : CoreState) (waitingPhase : s (.base .phase) = 7) :
    entering.eval i s = 0 := by
  rw [entering, eval_lift]
  simp [StreamingReady.Core.both, StreamingReady.Core.fetching, StreamingReady.Core.isPhase,
    Expr.eval, baseState, waitingPhase]

theorem eval_next_live (i : Values Input) (s : CoreState) (r : StreamingReady.Core.Register 1 w)
    (quiet : Quiet i) (waitingPhase : s (.base .phase) = 7) (live : s .mode ≠ 0) :
    circuit.step i s (.base r) = (receivingBase r).eval i s := by
  have h₁ := quiet_reset i s quiet
  have h₂ := no_reentry i s waitingPhase
  have live' : s .mode ≠ 0#3 := live
  have enabled : active.eval i s = 1 := by simp [active, Expr.eval, live']
  simp [Circuit.step, circuit, next, nextBase, both, either, Expr.eval, h₁, h₂, enabled]

theorem eval_next_clear (i : Values Input) (s : CoreState) (initial : BitVec w) (e : E w)
    (quiet : Quiet i) (waitingPhase : s (.base .phase) = 7) :
    (clear initial e).eval i s = e.eval i s := by
  have h₁ := quiet_reset i s quiet
  have h₂ := no_reentry i s waitingPhase
  simp [clear, either, Expr.eval, h₁, h₂]

theorem capture_slot_hidden (i : Values Input) (s : CoreState) (empty : s (.base .rxCount) = 0) :
    circuit.observe i s .rxQueued = 0 ∧ circuit.observe i s .rxData = 0 ∧
    circuit.observe i s .rxBits = 0 := by
  simp [Circuit.observe, circuit, output, StreamingReady.Core.output, Expr.eval, baseState, empty]

theorem publish_after_final_ack (i : Values Input) (s : CoreState)
    (quiet : Quiet i) (phase : s (.base .phase) = 7) (mode : s .mode = 5)
    (timer : (s .timer).toNat ≤ 1) :
    let finished : CoreState := circuit.step i s
    finished (.base .phase) = 5 ∧ finished .mode = 0 ∧ finished (.base .rxCount) = 2 ∧
    finished (.base .rxProduced) = 64 ∧ finished (.base .remaining) = 0 ∧
    finished (.base (.rxWord 0)) = s (.base (.rxWord 0)) ∧
    finished (.base (.rxWord 1)) = s (.base (.rxWord 1)) := by
  have live : s .mode ≠ 0 := by simp [mode]
  have send {w : Nat} (r : StreamingReady.Core.Register 1 w) :=
    eval_next_live i s r quiet phase live
  have h₁ := quiet_reset i s quiet
  have h₂ := no_reentry i s phase
  have last : (s .timer).toNat < 2 := by omega
  simp only [send]
  simp [receivingBase, sending, waiting, receiving, marker, isMode, eq, lt, both, either, Expr.eval,
    timerLt, sent, h₂, mode, last, clocked, symbol, logicalBit, dataBit]
  simp [Circuit.step, circuit, next, nextMode, sending, isMode, eq, lt, both, either, Expr.eval,
    timerLt, sent, h₁, h₂, mode, last]

def getCapture (s : CoreState) : Capture :=
  ⟨⟨(s .level).getLsbD 0, (s .sample).toNat⟩,
    ⟨(s .previous).getLsbD 0, (s .ones).toNat,
      ⟨(s .consumed).toNat, s .header, s (.base (.rxWord 0)),
        s (.base (.rxWord 1)), s .crc⟩⟩⟩

theorem isNat (a : BitVec w) (n : Nat) (fits : n < 2^w) :
    a = BitVec.ofNat w n ↔ a.toNat = n := by
  constructor
  · intro e
    simp [e, Nat.mod_eq_of_lt fits]
  · intro e
    exact BitVec.eq_of_toNat_eq (by simpa [Nat.mod_eq_of_lt fits] using e)

theorem bitValue (a : BitVec 1) : BitVec.ofBool (a.getLsbD 0) = a := by
  rcases BitVec.eq_zero_or_eq_one a with h | h <;> rw [h] <;> rfl

theorem boolNeg (x : Bool) : ~~~(BitVec.ofBool x) = BitVec.ofBool (!x) := by cases x <;> rfl

theorem boolAnd (x y : Bool) : BitVec.ofBool x &&& BitVec.ofBool y = BitVec.ofBool (x && y) :=
  BitVec.ofBool_and_ofBool

@[simp] private theorem oneBand (x : BitVec 1) : 1#1 &&& x = x := by
  rcases BitVec.eq_zero_or_eq_one x with h | h <;> rw [h] <;> rfl

@[simp] private theorem bandOne (x : BitVec 1) : x &&& 1#1 = x := by
  rw [BitVec.and_comm,oneBand]

theorem eval_frameOK (i : Values Input) (s : CoreState) :
    frameOK.eval i s = 1 ↔ ∃ words, verifyFrame (getCapture s) = .data words := by
  have ones := isNat (s .ones) 6 (by decide)
  have count := isNat (s .consumed) 96 (by decide)
  change (s .ones = 6#3 ↔ _) at ones
  change (s .consumed = 96#7 ↔ _) at count
  by_cases h₁ : s .ones = 6#3
  · have n := ones.mp h₁
    simp [frameOK, stuffed, eq, both, Expr.eval, verifyFrame, finishSymbols, getCapture, n, h₁]
  · have n : (s .ones).toNat ≠ 6 := fun p => h₁ (ones.mpr p)
    by_cases h₂ : s .consumed = 96#7
    · have c := count.mp h₂
      simp only [frameOK, stuffed, eq, both, Expr.eval, verifyFrame, finishSymbols, getCapture,
        dataHeader, h₁, h₂, n, c]
      by_cases h₃ : s .header = wordFor 16 (header 0x4B) <;>
        by_cases h₄ : s .crc = 0xB001#16 <;> simp_all
    · have c : (s .consumed).toNat ≠ 96 := fun p => h₂ (count.mpr p)
      simp [frameOK, stuffed, eq, both, Expr.eval, verifyFrame, finishSymbols, getCapture, n, h₁, h₂, c]
      repeat (first | split | simp_all)

theorem eval_next_mode_live (i : Values Input) (s : CoreState)
    (quiet : Quiet i) (phase : s (.base .phase) = 7) :
    circuit.step i s .mode =
      (Expr.mux (either failed sent) (.lit 0)
        (.mux (both waiting wireK) (.lit 2)
          (.mux (both receiving wireSE0) (.lit 3)
            (.mux (both marker wireJ) (.lit 4)
              (.mux (both delaying (timerLt 2)) (.lit 5) (.reg .mode)))))).eval i s := by
  have h₁ := quiet_reset i s quiet
  have h₂ := no_reentry i s phase
  simp only [Circuit.step, circuit, next, nextMode, Expr.eval, h₁, h₂]
  simp

theorem eval_age_live (i : Values Input) (s : CoreState)
    (quiet : Quiet i) (phase : s (.base .phase) = 7) (live : s .mode ≠ 0#3)
    (bound : (s .age).toNat < 4095) :
    (circuit.step i s .age).toNat = (s .age).toNat + 1 := by
  change ((clear 0 (.mux active (inc (.reg .age)) (.reg .age))).eval i s).toNat = _
  rw [eval_next_clear i s _ _ quiet phase]
  simp [active, Expr.eval, live, inc]
  change ((s .age) - (-1#12)).toNat = _
  rw [BitVec.sub_neg, BitVec.toNat_add]
  change ((s .age).toNat + 1) % 4096 = _
  exact Nat.mod_eq_of_lt (by omega)

theorem eval_next_small (i : Values Input) (s : CoreState)
    (quiet : Quiet i) (phase : s (.base .phase) = 7)
    (r : Register w) (init : BitVec w) (e : E w) (body : next r = clear init e) :
    circuit.step i s r = e.eval i s := by
  change (next r).eval i s = _
  rw [body, eval_next_clear i s init e quiet phase]

theorem eval_wireK (i : Values Input) (s : CoreState) (bit : Bool)
    (raw : s (.base .stage2) = (if bit then 1 else 2)) :
    wireK.eval i s = BitVec.ofBool bit := by
  cases bit <;> simp_all [wireK, wire, eq, Expr.eval]

theorem eval_clocked_body (i : Values Input) (s : CoreState) (bit : Bool)
    (raw : s (.base .stage2) = (if bit then 1 else 2))
    (mode : s .mode = 2) :
    clocked.eval i s = 1 := by
  cases bit <;> simp_all [clocked, receiving, waiting, isMode, either, both, wireJ, wireK, wire, eq, Expr.eval]

theorem eval_transition (i : Values Input) (s : CoreState) (bit : Bool)
    (k : wireK.eval i s = BitVec.ofBool bit) :
    transition.eval i s = BitVec.ofBool (decide (bit ≠ (s .level).getLsbD 0)) := by
  simp only [transition, Expr.eval, k, boolNeg]
  rw [← bitValue (s .level)]
  cases bit <;> cases q : (s .level).getLsbD 0 <;> rfl

theorem eval_decoded (i : Values Input) (s : CoreState) (bit : Bool)
    (k : wireK.eval i s = BitVec.ofBool bit) :
    decoded.eval i s = BitVec.ofBool (bit == (s .previous).getLsbD 0) := by
  simp only [decoded, Expr.eval, k]
  rw [← bitValue (s .previous)]
  cases bit <;> cases q : (s .previous).getLsbD 0 <;> rfl

theorem evaluate_symbol (i : Values Input) (s : CoreState) (bit : Bool)
    (k : wireK.eval i s = BitVec.ofBool bit) (ticking : clocked.eval i s = 1) :
    symbol.eval i s = BitVec.ofBool
      (decide (bit = (s .level).getLsbD 0) && decide (s .sample = 0#4)) := by
  have changeLine := eval_transition i s bit k
  by_cases diff : bit ≠ (s .level).getLsbD 0 <;>
    by_cases countdown : s .sample = 0#4 <;>
    simp [symbol, both, Expr.eval, ticking, changeLine, diff, countdown]

theorem eval_result_clock (i : Values Input) (s : CoreState) (bit : Bool)
    (quiet : Quiet i) (phase : s (.base .phase) = 7)
    (k : wireK.eval i s = BitVec.ofBool bit) (ticking : clocked.eval i s = 1) :
    (getCapture (circuit.step i s)).clock = (Pinwheel.USBClockFeasibility.tick (getCapture s).clock bit).1 := by
  have levelNext := eval_next_small i s quiet phase .level 0 _ rfl
  have sampleNext := eval_next_small i s quiet phase .sample 0 _ rfl
  have changeLine := eval_transition i s bit k
  have sampleAt := evaluate_symbol i s bit k ticking
  have zero := isNat (s .sample) 0 (by decide)
  change (s .sample = 0#4 ↔ _) at zero
  unfold getCapture
  dsimp only
  rw [levelNext, sampleNext]
  by_cases diff : bit ≠ (s .level).getLsbD 0
  · have diff' : bit ≠ (s .level)[0] := diff
    simp [Pinwheel.USBClockFeasibility.tick,diff,diff',Expr.eval,ticking,k,changeLine]
  · have same : bit = (s .level).getLsbD 0 := Classical.not_not.mp diff
    by_cases zeroCount : s .sample = 0#4
    · have z := zero.mp zeroCount
      simp [Pinwheel.USBClockFeasibility.tick, Expr.eval, ticking, k, changeLine, sampleAt, diff,
        same, zeroCount, z]
    · have z : (s .sample).toNat ≠ 0 := fun p => zeroCount (zero.mpr p)
      simp [Pinwheel.USBClockFeasibility.tick,Expr.eval,ticking,k,changeLine,sampleAt,diff,same,
        zeroCount,z,dec]
      congr 1
      exact BitVec.toNat_sub_of_le (by
        change (1#4).toNat ≤ (s .sample).toNat
        change 1 ≤ (s .sample).toNat
        omega)

private theorem incNat (x : BitVec w) (bound : x.toNat+1 < 2^w)
    (word : BitVec.ofInt w (-1) = (-1 : BitVec w)) :
    (x - BitVec.ofInt w (-1)).toNat = x.toNat+1 := by
  rw [word, BitVec.sub_neg, BitVec.toNat_add]
  change (x.toNat + (1#w).toNat) % 2^w = _
  rw [BitVec.toNat_one (by cases w <;> simp_all), Nat.mod_eq_of_lt bound]

private theorem pushExact (x : BitVec (w+1)) (b : Bool) :
    x.extractLsb' 0 w ++ BitVec.ofBool b = pushBit x b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  change (BitVec.concat (x.extractLsb' 0 w) b).getLsbD i = (pushBit x b).getLsbD i
  cases i with
  | zero => cases b <;> simp [pushBit, BitVec.getLsbD_ofNat]
  | succ j =>
    have smaller : j < w := by omega
    cases b <;> simp [pushBit, BitVec.getLsbD_ofNat, smaller, inside] <;>
      exact BitVec.getLsbD_eq_getElem (by omega)

private theorem push16 (x : BitVec 16) (b : Bool) :
    x.extractLsb' 0 15 ++ BitVec.ofBool b = pushBit x b := pushExact x b

private theorem push32 (x : BitVec 32) (b : Bool) :
    x.extractLsb' 0 31 ++ BitVec.ofBool b = pushBit x b := pushExact x b

private theorem crcShiftExact (x : BitVec 16) : (0#1) ++ x.extractLsb' 1 15 = x >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  rw [BitVec.getLsbD_append,BitVec.getLsbD_ushiftRight]
  by_cases low : i < 15
  · simp only [low,if_pos,BitVec.getLsbD_extractLsb',decide_true,Bool.true_and]
  · have last : i = 15 := by omega
    subst i
    simp [BitVec.getLsbD_of_ge]

private theorem xorParts (x y : BitVec w) : (x &&& ~~~y) ||| (~~~x &&& y) = x ^^^ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,
    inside,decide_true,Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

private theorem crc16 (x : BitVec 16) (b : Bool) :
    let y := (0#1) ++ x.extractLsb' 1 15
    (if x.getLsbD 0 ≠ b then (y &&& ~~~0xA001#16) ||| (~~~y &&& 0xA001#16) else y) =
      usbCrcStep x b := by
  dsimp only
  rw [crcShiftExact, xorParts]
  unfold usbCrcStep
  by_cases different : x.getLsbD 0 ≠ b
  · rw [if_pos different,if_pos (bne_iff_ne.mpr different)]
  · have same : x.getLsbD 0 = b := Classical.not_not.mp different
    rw [if_neg different,bne_eq_false_iff_eq.mpr same]
    simp

theorem decoder_no_symbol (i : Values Input) (s : CoreState)
    (quiet : Quiet i) (phase : s (.base .phase) = 7) (live : s .mode ≠ 0)
    (noSymbol : symbol.eval i s = 0) :
    (getCapture (circuit.step i s)).decoder = (getCapture s).decoder := by
  have prev := eval_next_small i s quiet phase .previous 0 _ rfl
  have runs := eval_next_small i s quiet phase .ones 0 _ rfl
  have count := eval_next_small i s quiet phase .consumed 0 _ rfl
  have head := eval_next_small i s quiet phase .header 0 _ rfl
  have crcNext := eval_next_small i s quiet phase .crc 0xFFFF _ rfl
  have word0 := eval_next_live i s (.rxWord 0#1) quiet phase live
  have word1 := eval_next_live i s (.rxWord 1#1) quiet phase live
  simp [getCapture,prev,runs,count,head,crcNext,word0,word1,receivingBase,dataBit,logicalBit,
    both,Expr.eval,noSymbol]

theorem decoder_stuffed_symbol (i : Values Input) (s : CoreState) (bit : Bool)
    (quiet : Quiet i) (phase : s (.base .phase) = 7) (live : s .mode ≠ 0)
    (k : wireK.eval i s = BitVec.ofBool bit) (strobe : symbol.eval i s = 1)
    (stuff : s .ones = 6#3)
    (toggle : bit ≠ (s .previous).getLsbD 0) :
    ingestSymbol (getCapture s).decoder bit = some (getCapture (circuit.step i s)).decoder := by
  have prev := eval_next_small i s quiet phase .previous 0 _ rfl
  have runs := eval_next_small i s quiet phase .ones 0 _ rfl
  have count := eval_next_small i s quiet phase .consumed 0 _ rfl
  have head := eval_next_small i s quiet phase .header 0 _ rfl
  have crcNext := eval_next_small i s quiet phase .crc 0xFFFF _ rfl
  have word0 := eval_next_live i s (.rxWord 0#1) quiet phase live
  have word1 := eval_next_live i s (.rxWord 1#1) quiet phase live
  have toggle' : bit ≠ (s .previous)[0] := toggle
  simp [ingestSymbol,getCapture,prev,runs,count,head,crcNext,word0,word1,receivingBase,
    dataBit,logicalBit,both,Expr.eval,stuffed,eq,stuff,strobe,k,toggle,toggle']

theorem eval_dataBit (i : Values Input) (s : CoreState) (lo hi : BitVec 7)
    (accept : logicalBit.eval i s = 1) :
    (dataBit lo hi).eval i s = 1 ↔ lo.toNat ≤ (s .consumed).toNat ∧ (s .consumed).toNat < hi.toNat := by
  simp only [dataBit,both,Expr.eval,accept,countLt,lt,boolNeg,boolAnd]
  change 1#1 &&& BitVec.ofBool _ = 1#1 ↔ _
  rw [oneBand]
  change BitVec.ofBool _ = BitVec.ofBool true ↔ _
  simp only [BitVec.ofBool_eq_iff_eq, Bool.and_eq_true, Bool.not_eq_true, decide_eq_true_eq]
  by_cases h : (s .consumed).toNat < lo.toNat
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_lt h]
    exact Iff.of_eq (decide_eq_true_eq (p := (s .consumed).toNat < hi.toNat))

theorem eval_crc_body (i : Values Input) (s : CoreState) (b : Bool)
    (bit : decoded.eval i s = BitVec.ofBool b) :
    (Expr.mux feedback (xor crcShift (.lit 0xA001)) crcShift).eval i s =
      usbCrcStep (s .crc) b := by
  rw [← crc16 (s .crc) b]
  change (if feedback.eval i s = 1 then (xor crcShift (.lit 0xA001)).eval i s
     else crcShift.eval i s) =
      (if (s .crc).getLsbD 0 ≠ b then
        (0#1 ++ (s .crc).extractLsb' 1 15) &&& ~~~0xA001#16 |||
          ~~~(0#1 ++ (s .crc).extractLsb' 1 15) &&& 0xA001#16
       else 0#1 ++ (s .crc).extractLsb' 1 15)
  have fb : feedback.eval i s = 1 ↔ (s .crc).getLsbD 0 ≠ b := by
    have low : (s .crc).extractLsb' 0 1 = BitVec.ofBool ((s .crc).getLsbD 0) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i inside
      have zero : i = 0 := by omega
      subst i
      simp [BitVec.getLsbD_ofBool]
    simp [feedback, Expr.eval, bit, low, boolNeg, BitVec.ofBool_eq_iff_eq]
  by_cases h : (s .crc).getLsbD 0 ≠ b
  · rw [if_pos (fb.mpr h), if_pos h]
    simp only [xor, either, Expr.eval, crcShift, BitVec.not_and, BitVec.not_or, BitVec.not_not]
    rfl
  · rw [if_neg (fun p => h (fb.mp p)), if_neg h]
    rfl

theorem decoder_logical_symbol (i : Values Input) (s : CoreState) (bit : Bool)
    (quiet : Quiet i) (phase : s (.base .phase) = 7) (live : s .mode ≠ 0)
    (k : wireK.eval i s = BitVec.ofBool bit) (strobe : symbol.eval i s = 1)
    (ones : (s .ones).toNat ≤ 6) (count : (s .consumed).toNat ≤ 97)
    (ordinary : s .ones ≠ 6#3) :
    ingestSymbol (getCapture s).decoder bit = some (getCapture (circuit.step i s)).decoder := by
  let b := bit == (s .previous).getLsbD 0
  let p := (s .consumed).toNat
  have decodedBit : decoded.eval i s = BitVec.ofBool b := eval_decoded i s bit k
  have stuffFlag : stuffed.eval i s = 0 := by simp [stuffed,eq,Expr.eval,ordinary]
  have logical : logicalBit.eval i s = 1 := by simp [logicalBit,both,Expr.eval,strobe,stuffFlag]
  have notSix : (s .ones).toNat ≠ 6 := fun e => ordinary ((isNat (s .ones) 6 (by decide)).mpr e)
  have prevNext := eval_next_small i s quiet phase .previous 0 _ rfl
  have onesNext := eval_next_small i s quiet phase .ones 0 _ rfl
  have countNext := eval_next_small i s quiet phase .consumed 0 _ rfl
  have headerNext := eval_next_small i s quiet phase .header 0 _ rfl
  have crcNext := eval_next_small i s quiet phase .crc 0xFFFF _ rfl
  have word0 := eval_next_live i s (.rxWord 0#1) quiet phase live
  have word1 := eval_next_live i s (.rxWord 1#1) quiet phase live
  have range0 : (dataBit 16#7 48#7).eval i s = 1#1 ↔ 16 ≤ p ∧ p < 48 :=
    eval_dataBit i s _ _ logical
  have range1 : (dataBit 48#7 80#7).eval i s = 1#1 ↔ 48 ≤ p ∧ p < 80 :=
    eval_dataBit i s _ _ logical
  have rangeCRC : (dataBit 16#7 96#7).eval i s = 1#1 ↔ 16 ≤ p ∧ p < 96 :=
    eval_dataBit i s _ _ logical
  have runs : (circuit.step i s .ones).toNat = (if b then (s .ones).toNat+1 else 0) := by
    rw [onesNext]
    cases h : b <;> simp [Expr.eval,both,strobe,stuffFlag,decodedBit,h,inc] <;> omega
  have total : (circuit.step i s .consumed).toNat = min 97 (p+1) := by
    rw [countNext]
    by_cases short : p < 97
    · simp [Expr.eval,both,logical,countLt,lt,inc,p,short] <;> omega
    · have endCount : p = 97 := by omega
      simp [Expr.eval,both,logical,countLt,lt,p,short,endCount]
  have head : circuit.step i s .header =
      (if p < 16 then pushBit (s .header) b else s .header) := by
    rw [headerNext]
    simp [Expr.eval,both,logical,countLt,lt,p,decodedBit,push16]
  have low : circuit.step i s (.base (.rxWord 0#1)) =
      (if 16 ≤ p ∧ p < 48 then pushBit (s (.base (.rxWord 0#1))) b
        else s (.base (.rxWord 0#1))) := by
    rw [word0]
    simp only [receivingBase,if_pos (rfl : (0#1) = 0)]
    simp [Expr.eval,range0,p,shiftPayload,decodedBit,push32]
  have high : circuit.step i s (.base (.rxWord 1#1)) =
      (if 48 ≤ p ∧ p < 80 then pushBit (s (.base (.rxWord 1#1))) b
        else s (.base (.rxWord 1#1))) := by
    rw [word1]
    simp only [receivingBase,if_neg (by decide : (1#1) ≠ 0)]
    simp [Expr.eval,range1,p,shiftPayload,decodedBit,push32]
  have crc : circuit.step i s .crc =
      (if 16 ≤ p ∧ p < 96 then usbCrcStep (s .crc) b else s .crc) := by
    rw [crcNext]
    change (if (dataBit 16#7 96#7).eval i s = 1#1 then _ else _) = _
    simp only [rangeCRC]
    split
    · exact eval_crc_body i s b decodedBit
    · rfl
  simp [getCapture, ingestSymbol, ingestLogical, notSix, prevNext, Expr.eval, k, strobe,
    runs, total, head, low, high, crc, b, p]

private theorem sampled_symbol (i : Values Input) (s : CoreState) (bit : Bool)
    (k : wireK.eval i s = BitVec.ofBool bit) (ticking : clocked.eval i s = 1) :
    (Pinwheel.USBClockFeasibility.tick (getCapture s).clock bit).2 =
      if symbol.eval i s = 1 then [bit] else [] := by
  have sampleAt := evaluate_symbol i s bit k ticking
  have zero := isNat (s .sample) 0 (by decide)
  change s .sample = 0#4 ↔ _ at zero
  rw [sampleAt]
  simp only [Pinwheel.USBClockFeasibility.tick, getCapture]
  by_cases diff : bit = (s .level).getLsbD 0 <;> by_cases empty : s .sample = 0#4 <;>
    simp [diff,empty,zero] at * <;> simp_all

theorem sampled_decoder (i : Values Input) (s : CoreState) (bit : Bool)
    (quiet : Quiet i) (phase : s (.base .phase) = 7) (live : s .mode ≠ 0)
    (k : wireK.eval i s = BitVec.ofBool bit) (ticking : clocked.eval i s = 1)
    (ones : (s .ones).toNat ≤ 6) (count : (s .consumed).toNat ≤ 97) :
    sampleOnTick (getCapture s) bit =
      if (both symbol (both stuffed decoded)).eval i s = 1 then none
      else some (getCapture (circuit.step i s)) := by
  let ideal := Pinwheel.USBClockFeasibility.tick (getCapture s).clock bit
  have sampleAt : ideal.2 = if symbol.eval i s = 1 then [bit] else [] :=
    sampled_symbol i s bit k ticking
  have c := eval_result_clock i s bit quiet phase k ticking
  have d := eval_decoded i s bit k
  have getPair : Capture.mk (Pinwheel.USBClockFeasibility.tick (getCapture s).clock bit).1
      (getCapture (circuit.step i s)).decoder = getCapture (circuit.step i s) := by rw [← c]
  unfold sampleOnTick
  change (ideal.2.foldlM ingestSymbol (getCapture s).decoder).map _ = _
  rw [sampleAt]
  by_cases emitSymbol : symbol.eval i s = 1#1
  · by_cases stuff : s .ones = 6#3
    · have atSix : (s .ones).toNat = 6 := (isNat (s .ones) 6 (by decide)).mp stuff
      by_cases same : bit = (s .previous).getLsbD 0
      · have same' : bit = (s .previous)[0] := same
        simp [emitSymbol,stuffed,eq,both,Expr.eval,stuff,d,same,same',getCapture,
          ingestSymbol,atSix]
      · have changed := decoder_stuffed_symbol i s bit quiet phase live k emitSymbol stuff same
        have same' : ¬ bit = (s .previous)[0] := same
        simp [emitSymbol,stuffed,eq,both,Expr.eval,stuff,d,same,same',changed,getPair]
    · have parsed := decoder_logical_symbol i s bit quiet phase live k emitSymbol ones count stuff
      simp [emitSymbol,stuffed,eq,both,Expr.eval,stuff,d,parsed,getPair]
  · have zero : symbol.eval i s = 0#1 := by
      exact (BitVec.eq_zero_or_eq_one _).resolve_right emitSymbol
    have unchanged := decoder_no_symbol i s quiet phase live zero
    simp [emitSymbol,zero,both,Expr.eval,← unchanged,getPair]

theorem capture_not_clocked (i : Values Input) (s : CoreState)
    (quiet : Quiet i) (phase : s (.base .phase) = 7) (live : s .mode ≠ 0)
    (stopped : clocked.eval i s = 0#1) :
    getCapture (circuit.step i s) = getCapture s := by
  have levelNext := eval_next_small i s quiet phase .level 0 _ rfl
  have countdown := eval_next_small i s quiet phase .sample 0 _ rfl
  have noStrobe : symbol.eval i s = 0 := by simp [symbol,both,Expr.eval,stopped]
  have unchanged := decoder_no_symbol i s quiet phase live noStrobe
  have clock : (getCapture (circuit.step i s)).clock = (getCapture s).clock := by
    simp [getCapture,levelNext,countdown,Expr.eval,stopped]
  generalize getCapture (circuit.step i s) = a at *
  generalize getCapture s = b at *
  cases a
  cases b
  simp_all

theorem live_publication (i : Values Input) (s : CoreState)
    (quiet : Quiet i) (phase : s (.base .phase) = 7) (live : s .mode ≠ 0) :
    let n : CoreState := circuit.step i s
    n (.base .enabled) = 0 ∧ n (.base .levels) = 0 ∧
    n (.base .phase) = (if sent.eval i s = 1 then 5 else if failed.eval i s = 1 then 6 else 7) ∧
    n (.base .rxCount) = (if sent.eval i s = 1 then 2 else s (.base .rxCount)) ∧
    n (.base .rxProduced) = (if sent.eval i s = 1 then 64 else s (.base .rxProduced)) ∧
    n (.base .remaining) = (if sent.eval i s = 1 then 0 else s (.base .remaining)) := by
  have step {w : Nat} (r : StreamingReady.Core.Register 1 w) :=
    eval_next_live i s r quiet phase live
  have entry := no_reentry i s phase
  simp [step,receivingBase,Expr.eval,entry]

theorem timer_update (i : Values Input) (s : CoreState)
    (quiet : Quiet i) (phase : s (.base .phase) = 7) :
    circuit.step i s .timer =
      (if (both receiving wireSE0).eval i s = 1 then 1
       else if (both marker wireJ).eval i s = 1 then 46
       else if (both marker wireSE0).eval i s = 1 then (s .timer) - BitVec.ofInt 9 (-1)
       else if (both delaying (timerLt 2)).eval i s = 1 then 304
       else if (either delaying sending).eval i s = 1 then (s .timer) - 1
       else s .timer) := by
  rw [eval_next_small i s quiet phase .timer 0 _ rfl]
  dsimp only [Expr.eval, inc, dec]

end Pinwheel.Hardware.USB
