import Pinwheel.Hardware.StreamingReady.SourceRefinement
import Pinwheel.Program.StreamingReadyFields

namespace Pinwheel.Hardware.StreamingReady.SourceRefinement
open Pinwheel.Hardware Pinwheel.Program.StreamingReady
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

private theorem conditional_add (b : Bool) (x y : BitVec w) :
    (if b then x+y else x) = x + (if b then y else 0) := by
  cases b <;> simp

private theorem clock_countdown_fetch (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (no : NoAdmission s i) (phase : s.phase = .fetch) :
    (Core.circuit a).step (inputs i) (values image s) .countdown = (engine p s).countdown := by
  simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.enteringCell,
    Core.both,Core.either,Expr.eval,cleared_zero image s i ha hi no,
    fetching_eval image s i hi,reserving_eval image s i ha hi,
    guardedLowEnd_eval image s i hi,capture_eval image s i hi,
    standaloneSuccess_eval image s i hi,waitDecrement_eval image s i hi,
    values,phase,State.captures,Core.isPhase,BitVec.ofNat_eq_ofNat]
  cases fetched : p.fetch s.pc.toNat with
  | none =>
    have bad := entryBad_of_none image s i fetched
    simp [bad,engine,phase,fetched,State.stop,Phase.code,Bool.beq_eq_decide_eq]
  | some instruction =>
    have word := (fetch_some image s i instruction fetched).1
    have bad := entryBad_of_fetch image s i instruction fetched
    simp only [bad,entryTerminal_of_word image s i instruction word,
      entrySkip_of_word image s i instruction word,entryWait_of_word image s i instruction word,
      entryGuardCountdown_of_word image s i instruction word]
    cases instruction <;> by_cases remaining : s.remaining = 0#16 <;>
      simp [engine,phase,fetched,remaining,Instruction.isStream,Instruction.guard,State.stop,Phase.code,Bool.beq_eq_decide_eq]

private theorem clock_countdown (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (no : NoAdmission s i) :
    (Core.circuit a).step (inputs i) (values image s) .countdown = (engine p s).countdown := by
  cases phase : s.phase
  case fetch => exact clock_countdown_fetch image s i ha hi no phase
  all_goals simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.enteringCell,
    Core.both,Core.either,Expr.eval,cleared_zero image s i ha hi no,
    fetching_eval image s i hi,reserving_eval image s i ha hi,
    guardedLowEnd_eval image s i hi,capture_eval image s i hi,guardCountdown_eval,
    standaloneSuccess_eval image s i hi,waitDecrement_eval image s i hi,
    values,Core.isPhase,Core.field,(encode_fields s.current).lowDuration,(encode_fields s.current).highDuration,
    and_bool,inv_bool,BitVec.ofNat_eq_ofNat]
  all_goals cases credit : s.canReserve <;> cases ready : s.waitReady <;>
    cases stream : s.current.isStream <;> cases guarded : s.current.hasHighGuard <;>
    cases limit : s.current.guard.limit <;> by_cases count : s.countdown = 0#8 <;>
    simp [phase,engine,count,credit,ready,stream,guarded,limit,WaitLimit.expires,WaitLimit.poll,WaitLimit.budget,budget_nonzero,
      State.enterHigh,State.captureData,State.timeoutFault,Phase.code,BitVec.ofNat_eq_ofNat,
      State.captures,Bool.beq_eq_decide_eq]

theorem clock_step (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (no : NoAdmission s i) (r : Core.Register a w) :
    (Core.circuit a).step (inputs i) (values image s) r = values image (clock p i s) r := by
  cases r
  case txWord k => exact clock_txWord image s i ha hi hs no k
  case txBits k => exact clock_txBits image s i ha hi hs no k
  case rxWord k => exact clock_rxWord image s i ha hi hs no k
  case rxBits k => exact clock_rxBits image s i ha hi hs no k
  case txHead => exact clock_txHead image s i ha hi no
  case txTail => exact clock_txTail image s i ha hi hs no
  case rxHead => exact clock_rxHead image s i ha hi no
  case rxTail => exact clock_rxTail image s i ha hi hs no
  case txCount => exact clock_txCount image s i ha hi hs no
  case rxCount => exact clock_rxCount image s i ha hi hs no
  case txAccepted => exact clock_txAccepted image s i ha hi hs no
  case rxPopped => exact clock_rxPopped image s i ha hi no
  case levels => exact clock_levels image s i ha hi no
  case enabled => exact clock_enabled image s i ha hi no
  case countdown => exact clock_countdown image s i ha hi no
  all_goals simp only [Core.circuit,Circuit.step,Core.next,Core.nextRaw,Core.cold,
    Core.enteringCell,Core.advancing,Core.both,Core.either,Core.field,Expr.eval,
    starting_zero image s i hi no,releasing_zero image s i ha hi no,
    resetting_eval image s i hi,cleared_zero image s i ha hi no,
    writing_eval image s i hi,committing_eval image s i hi,
    fetching_eval image s i hi,reserving_eval image s i ha hi,
    takingTX_eval image s i ha hi,transmit_eval,capture_eval image s i hi,capturingRX_eval image s i hi,
    guardedLowEnd_eval image s i hi,standaloneSuccess_eval image s i hi,
    waitFault_eval image s i hi,waitDecrement_eval image s i hi,guardCountdown_eval,
    emittingRX_eval image s i hi,highEnd_eval image s i hi,repeating_eval,stream_eval,
    txSource_eval,txSourceBits_eval image s i hs,assembled_eval,nextBit_eval,inc_eval,
    values,inputs,hi.1,clock,(encode_fields s.current).lowDuration,(encode_fields s.current).highDuration,
    and_bool,inv_bool,shift_zero,chunk_decrement,BitVec.ofNat_eq_ofNat]
  all_goals try simp only [engine_total,(engine_frame p s).2.2.2.2.1,
    (engine_frame p s).2.2.2.2.2.1]
  all_goals cases phase : s.phase <;>
    simp [phase,engine,Bool.beq_eq_decide_eq,State.stop,State.enterHigh,State.captureData,State.timeoutFault,Phase.code,BitVec.ofNat_eq_ofNat,
      Core.isPhase,Expr.eval,values,State.captures,State.timedOut]
  all_goals first
    | (have fetchPhase : s.phase = .fetch := phase
       cases fetch : p.fetch s.pc.toNat with
       | none =>
         have bad := entryBad_of_none image s i fetch
         simp [bad]
       | some instruction =>
         have word := (fetch_some image s i instruction fetch).1
         have bad := entryBad_of_fetch image s i instruction fetch
         try simp only [bad,entryTerminal_of_word image s i instruction word,
           entrySkip_of_word image s i instruction word,entryFault_of_word image s i instruction word,
           entryWait_of_word image s i instruction word,entryGuardCountdown_of_word image s i instruction word,word]
         all_goals cases instruction <;> by_cases remaining : s.remaining = 0#16 <;>
           simp [remaining,Instruction.isStream,Bool.beq_eq_decide_eq,BitVec.ofNat_eq_ofNat])
    | (cases credit : s.canReserve <;> by_cases count : s.countdown = 0#8 <;>
       cases stream : s.current.isStream <;> cases transmit : s.current.cell.transmit <;>
       by_cases repeating : 1 < s.remaining.toNat <;>
       try simp [count,repeating,phase,BitVec.ofNat_eq_ofNat])
  all_goals try (cases guarded : s.current.hasHighGuard <;> simp [guarded])
  all_goals try (cases ready : s.waitReady <;> cases limit : s.current.guard.limit <;>
    simp [ready,limit,WaitLimit.expires,WaitLimit.poll,WaitLimit.budget,budget_nonzero,Phase.code])
  all_goals try (by_cases count : s.countdown = 0#8 <;> simp [count])
  all_goals try (cases emits : s.emittingCapture <;>
    simp_all [State.enginePush,State.timedOut,WaitLimit.expires,WaitLimit.poll,Bool.beq_eq_decide_eq])
  all_goals try (first | exact chunk_decrement _ | exact conditional_add _ _ _)
  done


/-- Every register agrees for every installed source state satisfying the independently
preserved structural bounds, and every non-loader/non-reset sampled input. -/
theorem step_correct (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) (r : Core.Register a w) :
    (Core.circuit a).step (inputs i) (values image s) r = values image (step p i s) r := by
  have warm : (i.command == 15) = false := by
    simpa only [Bool.beq_eq_decide_eq] using (decide_eq_false hi.2.1)
  by_cases start : (i.command == 3 && s.canStart i) = true
  · simpa only [step,hi.1,warm,start,Bool.false_eq_true,ite_false,ite_true] using
      start_step image s i ha hi start r
  · have notstart : (i.command == 3 && s.canStart i) = false := by
      cases h : (i.command == 3 && s.canStart i) <;> simp_all
    by_cases release : (i.command == 4 && s.canRelease i) = true
    · simpa only [step,hi.1,warm,notstart,release,Bool.false_eq_true,ite_false,ite_true] using
        release_step image s i ha hi release r
    · have notrelease : (i.command == 4 && s.canRelease i) = false := by
        cases h : (i.command == 4 && s.canRelease i) <;> simp_all
      simpa only [step,hi.1,warm,notstart,notrelease,Bool.false_eq_true,ite_false] using
        clock_step image s i ha hi hs ⟨notstart,notrelease⟩ r

theorem step_values (image : Image p) (s : State a) (i : Input) (ha : a ≤ 3)
    (hi : RuntimeInput i) (hs : s.Structural) :
    @Circuit.step _ _ _ (Core.circuit a) (inputs i) (values image s) =
      @values p a image (step p i s) := by
  funext w r
  exact step_correct image s i ha hi hs r

/-- The ordinary actual expression circuit clocks once for every sampled input. -/
def runCircuit (registers : Values (Core.Register a)) (samples : List Input) : Values (Core.Register a) :=
  samples.foldl (α := Values (Core.Register a))
    (fun r i => @Circuit.step _ _ _ (Core.circuit a) (inputs i) r) registers

theorem run_correct (image : Image p) (s : State a) (samples : List Input) (ha : a ≤ 3)
    (hi : ∀ i ∈ samples, RuntimeInput i) (hs : s.Structural) :
    @runCircuit a (values image s) samples = @values p a image (run p s samples) := by
  induction samples generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have runtime : RuntimeInput i := hi i (by simp)
    have tail : ∀ j ∈ rest, RuntimeInput j := by
      intro j member
      exact hi j (by simp [member])
    change @runCircuit a (@Circuit.step _ _ _ (Core.circuit a) (inputs i) (values image s)) rest =
      @values p a image (run p (step p i s) rest)
    rw [step_values image s i ha runtime hs]
    exact ih (step p i s) tail (step_structural p s i hs)

end Pinwheel.Hardware.StreamingReady.SourceRefinement
