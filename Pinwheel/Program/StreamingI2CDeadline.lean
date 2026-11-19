import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingReadyTiming
import Pinwheel.Program.StreamingI2CRead

/-! The standard I²C image samples SCL through two stages before each
WAIT poll. A raw rising edge and a qualified SDA capture have different cuts. -/
namespace Pinwheel.Program.StreamingI2CDeadline
open Pinwheel.Program.StreamingReady

abbrev program : Program := (i2cImage .standard).program
abbrev streamRow : Instruction :=
  .stream (i2cCell .standard) (some (i2cGuard .standard 1 1))

structure WaitEntry (s : State a) : Prop where
  phase : s.phase = .waiting
  current : s.current = streamRow
  countdown : s.countdown = 30#8
  openDrain : s.pins.levels = 0#3
  release : s.pins.enabled[0] = false
  firstLow : s.samplerFirst[0] = false
  secondLow : s.samplerSecond[0] = false

/-- The target stretches SCL through the first `stretch` raw-input clocks.
SDA can stay low or be released independently during the wait. -/
def target (stretch : Nat) (sda : Pinwheel.I2C.Drive) (k : Nat) : Pinwheel.I2C.Pins :=
  ⟨if k < stretch then .low else .release,sda⟩

/-- The peer plan determines raw pads. The host may issue any ordinary service clocks. -/
structure Stimulus (s : State a) (stretch : Nat) (sda : Pinwheel.I2C.Drive)
    (inputs : List Input) : Prop where
  ordinary : ∀ i ∈ inputs, i.Runtime
  resolved : ∀ k (inside : k < inputs.length),
    inputs[k].rawInputs = StreamingI2CRead.resolvedRaw s.pins (target stretch sda k)

theorem Stimulus.scl {s : State a} {stretch sda inputs}
    (h : Stimulus s stretch sda inputs) (released : s.pins.enabled[0] = false)
    (k : Nat) (inside : k < inputs.length) :
    inputs[k].rawInputs[0] = decide (stretch ≤ k) := by
  rw [h.resolved k inside]
  change (StreamingI2CRead.resolvedRaw s.pins (target stretch sda k)).getLsbD 0 = _
  rw [StreamingI2CRead.resolvedRaw_scl]
  change (!s.pins.enabled[0] && (target stretch sda k).scl == .release) = _
  rw [released]
  by_cases early : k < stretch
  · simp [target,early,Nat.not_le.mpr early]
  · simp [target,early,Nat.le_of_not_gt early]

private theorem run_append (p : Program) (s : State a) (before after : List Input) :
    run p s (before ++ after) = run p (run p s before) after := by
  simp only [run,List.foldl_append]

private theorem cut_after_two (p : Program) (s : State a) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, i.Runtime) (k : Nat) (inside : k + 2 ≤ inputs.length) :
    (run p s (inputs.take (k + 2))).samplerSecond = (inputs[k]'(by omega)).rawInputs := by
  rw [List.take_succ_eq_append_getElem (show k + 1 < inputs.length by omega),
    List.take_succ_eq_append_getElem (show k < inputs.length by omega),List.append_assoc]
  exact (run_two_samples p s (inputs.take k) (inputs[k]'(by omega)) (inputs[k+1]'(by omega))
    (ordinary _ (List.getElem_mem _)) (ordinary _ (List.getElem_mem _))).2

private theorem matches_scl (raw : BitVec 2) :
    (i2cGuard .standard 1 1).matches raw = raw[0] := by
  decide +revert +kernel

private theorem low_cut (s : State a) (h : WaitEntry s) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, i.Runtime) (stretch n : Nat)
    (inside : n ≤ inputs.length) (before : n < stretch + 2)
    (low : ∀ k (hk : k < inputs.length), k < stretch → inputs[k].rawInputs[0] = false) :
    (run program s (inputs.take n)).samplerSecond[0] = false := by
  cases n with
  | zero => exact h.secondLow
  | succ n =>
    cases n with
    | zero =>
      have bound : 0 < inputs.length := by omega
      rw [List.take_succ_eq_append_getElem bound]
      exact (congrArg (fun v : BitVec 2 => v[0])
        (step_samples program s inputs[0] (ordinary _ (List.getElem_mem bound))).2).trans h.firstLow
    | succ k =>
      rw [cut_after_two program s inputs ordinary k inside]
      exact low k (by omega) (by omega)

private theorem miss_append (p : Program) (s : State a) (xs : List Input) (last : Input)
    (missed : MissHistory p s xs) (ordinary : last.Runtime)
    (miss : (run p s xs).waitReady = false) :
    MissHistory p s (xs ++ [last]) := by
  induction xs generalizing s with
  | nil => exact ⟨ordinary,miss,True.intro⟩
  | cons i xs ih => exact ⟨missed.1,missed.2.1,ih (step p i s) missed.2.2 miss⟩

private theorem trace_append (p : Program) (s : State a) (trace : BitTrace) (before after : List Input) :
    traceRun p s trace (before ++ after) =
      traceRun p (run p s before) (traceRun p s trace before) after := by
  induction before generalizing s trace with
  | nil => rfl
  | cons i xs ih => exact ih (step p i s) (trace.step s i)

private theorem trace_wait_edge (s : State a) (trace : BitTrace) (i : Input)
    (waiting : s.phase = .waiting) (runtime : i.Runtime) :
    (trace.step s i).captured = trace.captured ++ s.rxEvent := by
  simp [BitTrace.step,runtime.1,(show i.command ≠ 15#4 from runtime.2),
    State.canStart, State.canRelease, waiting, Phase.retained, BitTrace.clock]

private theorem stream_limit (s : State a) (row : s.current = streamRow) :
    s.current.guard.limit = .misses 30 := by
  rw [row]
  rfl

private theorem scl_misses (s : State a) (h : WaitEntry s) (trace : BitTrace)
    (inputs : List Input) (ordinary : ∀ i ∈ inputs, i.Runtime)
    (stretch : Nat)
    (low : ∀ k (hk : k < inputs.length), k < stretch → inputs[k].rawInputs[0] = false)
    (n : Nat) (inside : n ≤ inputs.length) (budget : n ≤ 30) (delayed : n ≤ stretch + 2) :
    MissHistory program s (inputs.take n) ∧
      (traceRun program s trace (inputs.take n)).captured = trace.captured := by
  induction n with
  | zero => exact ⟨True.intro,rfl⟩
  | succ n ih =>
    obtain ⟨prior,captured⟩ := ih (by omega) (by omega) (by omega)
    let cut := run program s (inputs.take n)
    have within : (inputs.take n).length ≤ s.countdown.toNat := by
      rw [h.countdown,List.length_take]
      simp only [BitVec.toNat_ofNat]
      omega
    obtain ⟨waiting,_,_,_,current⟩ := bounded_wait_prefix program s (inputs.take n) 30
      h.phase (stream_limit s h.current) prior within
    have sample := low_cut s h inputs ordinary stretch n (by omega) (by omega) low
    have miss : cut.waitReady = false := by
      change (run program s (inputs.take n)).waitReady = false
      rw [State.waitReady,current,h.current]
      exact (matches_scl _).trans sample
    have index : n < inputs.length := by omega
    have runtime := ordinary inputs[n] (List.getElem_mem index)
    rw [List.take_succ_eq_append_getElem index]
    refine ⟨miss_append program s _ _ prior runtime miss,?_⟩
    rw [trace_append]
    change ((traceRun program s trace (inputs.take n)).step cut (inputs[n])).captured = _
    rw [trace_wait_edge cut _ _ waiting runtime,captured]
    rw [State.rxEvent]
    simp [State.captures,show cut.phase = .waiting from waiting,miss]

structure WaitingPrefix (s cut : State a) (trace cutTrace : BitTrace) (n : Nat) : Prop where
  phase : cut.phase = .waiting
  countdown : cut.countdown.toNat = 30 - n
  pins : cut.pins = s.pins
  remaining : cut.remaining = s.remaining
  current : cut.current = streamRow
  captured : cutTrace.captured = trace.captured

/-- Before the aperture reaches the released SCL, every poll misses and
holds the pad pose and the capture prefix. -/
theorem waiting_prefix (s : State a) (entry : WaitEntry s) (trace : BitTrace)
    (stretch : Nat) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (stimulus : Stimulus s stretch sda inputs) (n : Nat)
    (inside : n ≤ inputs.length) (budget : n ≤ 30) (delayed : n ≤ stretch + 2) :
    WaitingPrefix s (run program s (inputs.take n)) trace
      (traceRun program s trace (inputs.take n)) n := by
  have low (k : Nat) (hk : k < inputs.length) (early : k < stretch) :
      inputs[k].rawInputs[0] = false := by
    simp [stimulus.scl entry.release k hk,Nat.not_le.mpr early]
  obtain ⟨misses,captured⟩ := scl_misses s entry trace inputs stimulus.ordinary stretch low n inside budget delayed
  have len : (inputs.take n).length = n := by simp [List.length_take,Nat.min_eq_left inside]
  obtain ⟨phase,count,pins,remaining,current⟩ :=
    bounded_wait_prefix program s (inputs.take n) 30 entry.phase (stream_limit s entry.current) misses
      (by simpa [len,entry.countdown] using budget)
  exact ⟨phase,by simpa [entry.countdown,len] using count,pins,remaining,
    current.trans entry.current,captured⟩

theorem Stimulus.resolved_at_cut {s : State a} {stretch sda inputs}
    (stimulus : Stimulus s stretch sda inputs) (entry : WaitEntry s)
    (n : Nat) (inside : n < inputs.length) (budget : n ≤ 30) (delayed : n ≤ stretch + 2) :
    inputs[n].rawInputs = StreamingI2CRead.resolvedRaw
      (run program s (inputs.take n)).pins (target stretch sda n) := by
  rw [(waiting_prefix s entry {} stretch sda inputs stimulus n (Nat.le_of_lt inside) budget delayed).pins]
  exact stimulus.resolved n inside

/-- Construct the stimulus from a peer connected to the actual evolving
controller pads. Each prior miss made the original pad pose remain valid. -/
theorem Stimulus.of_runtime_resolved (s : State a) (entry : WaitEntry s)
    (stretch : Nat) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, i.Runtime)
    (raw : ∀ k (inside : k < inputs.length), inputs[k].rawInputs = StreamingI2CRead.resolvedRaw
      (run program s (inputs.take k)).pins (target stretch sda k))
    (budget : inputs.length ≤ 31) (delayed : inputs.length ≤ stretch + 3) :
    Stimulus s stretch sda inputs := by
  have take (n : Nat) (inside : n ≤ inputs.length) : Stimulus s stretch sda (inputs.take n) := by
    induction n with
    | zero => constructor <;> simp
    | succ n ih =>
      have earlier : n ≤ inputs.length := by omega
      have prior := ih earlier
      have len : (inputs.take n).length = n := by simp [List.length_take,Nat.min_eq_left earlier]
      have held := (waiting_prefix s entry {} stretch sda (inputs.take n) prior n
        (by simp [len]) (by omega) (by omega)).pins
      rw [List.take_of_length_le (by simp [len])] at held
      constructor
      · exact fun i hin => ordinary i (List.mem_of_mem_take hin)
      · intro k hk
        have sourceBound : k < inputs.length := by simp only [List.length_take] at hk; omega
        simp only [List.getElem_take]
        by_cases early : k < n
        · rw [List.getElem_take' sourceBound early]
          exact prior.resolved k (by omega)
        · have border : k = n := by simp only [List.length_take] at hk; omega
          subst k
          exact (raw n sourceBound).trans (congrArg
            (fun pins => StreamingI2CRead.resolvedRaw pins (target stretch sda n)) held)
  simpa only [List.take_length] using take inputs.length (Nat.le_refl _)

structure CaptureResult (s final : State a) (trace finalTrace : BitTrace) (bit : Bool) : Prop where
  phase : final.phase = .high
  pins : final.pins = s.pins
  remaining : final.remaining = s.remaining
  current : final.current = streamRow
  captured : finalTrace.captured = trace.captured ++ [bit]

/-- The first raw SCL rise at clock `stretch` reaches the aperture two clocks
later. Clock 30 is the last permitted poll and still captures exactly once. -/
theorem stretch_success (s : State a) (entry : WaitEntry s) (trace : BitTrace)
    (stretch : Nat) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (stimulus : Stimulus s stretch sda inputs) (timely : stretch ≤ 28)
    (length : inputs.length = stretch + 3) :
    CaptureResult s (run program s inputs) trace (traceRun program s trace inputs)
      (StreamingI2CRead.resolvedRaw s.pins (target stretch sda stretch))[1] := by
  have index : stretch + 2 < inputs.length := by omega
  let cut := run program s (inputs.take (stretch + 2))
  let i := inputs[stretch + 2]
  have pre := waiting_prefix s entry trace stretch sda inputs stimulus (stretch + 2)
    (by omega) (by omega) (by omega)
  have aperture : cut.samplerSecond = inputs[stretch].rawInputs :=
    cut_after_two program s inputs stimulus.ordinary stretch (by omega)
  have cutRow : cut.current = streamRow := pre.current
  have waiting : cut.phase = .waiting := pre.phase
  have scl := stimulus.scl entry.release stretch (by omega)
  simp only [Nat.le_refl,decide_true] at scl
  have ready : cut.waitReady = true := by
    rw [State.waitReady,pre.current]
    change (i2cGuard .standard 1 1).matches cut.samplerSecond = true
    rw [matches_scl,aperture,scl]
  have runtime := stimulus.ordinary i (List.getElem_mem index)
  have advanced := step_wait_ready program cut i runtime pre.phase ready
  have decomposition : inputs.take (stretch + 2) ++ [i] = inputs := by
    unfold i
    rw [← List.take_succ_eq_append_getElem index,List.take_of_length_le (by omega)]
  have physical : run program s inputs = step program i cut := by
    rw [← decomposition,run_append]
    rfl
  have event : cut.rxEvent = [(StreamingI2CRead.resolvedRaw s.pins (target stretch sda stretch))[1]] := by
    rw [State.rxEvent]
    have capture : cut.captures = true := by
      simp [State.captures,waiting,cutRow,ready,streamRow,Instruction.isStream,
        Instruction.cell,i2cCell]
    have port : cut.current.cell.rxInput.val = 1 := by rw [cutRow]; rfl
    rw [capture,if_pos rfl,← BitVec.getLsbD_eq_getElem cut.current.cell.rxInput.isLt,
      port,aperture,stimulus.resolved stretch (by omega)]
    rfl
  constructor
  · rw [physical]
    simpa [cutRow,streamRow,Instruction.isStream] using advanced.1
  · rw [physical,advanced.2.1,pre.pins]
  · rw [physical,advanced.2.2.1,pre.remaining]
  · rw [physical,advanced.2.2.2,pre.current]
  · rw [← decomposition,trace_append]
    change ((traceRun program s trace (inputs.take (stretch + 2))).step cut i).captured = _
    rw [trace_wait_edge cut _ i pre.phase runtime,pre.captured,event]

structure TimeoutResult (s final : State a) (trace finalTrace : BitTrace) : Prop where
  phase : final.phase = .fault
  pins : final.pins = ⟨0,0⟩
  remaining : final.remaining = s.remaining
  partialFlushed : final.rxUsed = 0#6
  captured : finalTrace.captured = trace.captured
  recoverable : trace.captured = finalTrace.exported ++ finalTrace.rxQueued.flatMap Streaming.Chunk.rxBits
  samplerHigh : final.samplerSecond[0] = true

/-- Releasing SCL one clock after the last legal aperture still raises the
wire in time for the second sampler to update on the fault edge. The same
edge tested the earlier LOW and retains exactly the already captured prefix. -/
theorem one_late (s : State a) (entry : WaitEntry s) (trace : BitTrace)
    (sda : Pinwheel.I2C.Drive) (inputs : List Input) (stimulus : Stimulus s 29 sda inputs)
    (length : inputs.length = 31) (related : trace.Related s) (structural : s.Structural) :
    TimeoutResult s (run program s inputs) trace (traceRun program s trace inputs) := by
  have index : 30 < inputs.length := by omega
  let cut := run program s (inputs.take 30)
  let i := inputs[30]
  have pre := waiting_prefix s entry trace 29 sda inputs stimulus 30 (by omega) (by decide) (by decide)
  have waiting : cut.phase = .waiting := pre.phase
  have row : cut.current = streamRow := pre.current
  have zero : cut.countdown = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    simpa using pre.countdown
  have aperture : cut.samplerSecond = inputs[28].rawInputs :=
    cut_after_two program s inputs stimulus.ordinary 28 (by omega)
  have miss : cut.waitReady = false := by
    rw [State.waitReady,row]
    change (i2cGuard .standard 1 1).matches cut.samplerSecond = false
    rw [matches_scl,aperture,stimulus.scl entry.release 28 (by omega)]
    rfl
  have runtime := stimulus.ordinary i (List.getElem_mem index)
  have decomposition : inputs.take 30 ++ [i] = inputs := by
    unfold i
    rw [← List.take_succ_eq_append_getElem index,List.take_of_length_le (by omega)]
  have physical : run program s inputs = step program i cut := by
    rw [← decomposition,run_append]
    rfl
  have timedOut : cut.timedOut = true := by
    simp [State.timedOut,waiting,miss,zero,stream_limit cut row,WaitLimit.expires]
  have busy : cut.phase.busy = true := by rw [waiting]; rfl
  have actual := step_busy_eq_clock program cut i runtime busy
  have noCapture := timedOut_captures_false cut timedOut
  have captured : (traceRun program s trace inputs).captured = trace.captured := by
    rw [← decomposition,trace_append]
    change ((traceRun program s trace (inputs.take 30)).step cut i).captured = _
    rw [trace_wait_edge cut _ i waiting runtime,pre.captured]
    simp [State.rxEvent,noCapture]
  have fields : (run program s inputs).phase = .fault ∧ (run program s inputs).pins = ⟨0,0⟩ ∧
      (run program s inputs).remaining = s.remaining ∧ (run program s inputs).rxUsed = 0#6 := by
    rw [physical,actual,clock,engine_timedOut program cut timedOut]
    exact ⟨rfl,rfl,pre.remaining,rfl⟩
  have custody := traceRun_related program s trace inputs related structural
  have empty : (run program s inputs).pendingRx = [] := by simp [State.pendingRx,fields.2.2.2]
  have recoverable := custody.rxOrder
  rw [captured,empty,List.append_nil] at recoverable
  have seen : (run program s inputs).samplerSecond = inputs[29].rawInputs := by
    have lastSample := cut_after_two program s inputs stimulus.ordinary 29 (by omega)
    simpa [List.take_of_length_le (show inputs.length ≤ 31 by omega)] using lastSample
  refine ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2,captured,recoverable,?_⟩
  rw [seen,stimulus.scl entry.release 29 (by omega)]
  rfl

private theorem release_high_pins (s : State a) (row : s.current = streamRow) :
    s.highPins.levels = 0#3 ∧ s.highPins.enabled[0] = false := by
  unfold State.highPins
  rw [row]
  cases last : s.lastCell <;> cases bit : s.cellBit <;> exact ⟨rfl,rfl⟩

/-- The transition out of ordinary LOW releases SCL. The raw clock at this
transition still sees the old LOW drive, as did the preceding raw clock. -/
theorem enter_wait (s : State a) (i : Input) (runtime : i.Runtime)
    (low : s.phase = .low) (count : s.countdown = 0#8) (row : s.current = streamRow)
    (priorLow : s.samplerFirst[0] = false) (rawLow : i.rawInputs[0] = false) :
    WaitEntry (step program i s) := by
  have busy : s.phase.busy = true := by rw [low]; rfl
  have moved : engine program s = {s with phase := .waiting, countdown := 30#8, pins := s.highPins} := by
    rw [engine,low]
    have guarded : s.current.hasHighGuard = true := by rw [row]; rfl
    have budget : s.current.guard.limit.initialCountdown = 30#8 := by rw [row]; rfl
    rw [count,guarded,budget]
    rfl
  rw [step_busy_eq_clock program s i runtime busy,clock,moved]
  have pins := release_high_pins s row
  exact ⟨rfl,row,rfl,pins.1,pins.2,rawLow,priorLow⟩

/-- A full four-clock LOW interval primes both samplers, independently of
their older contents and of the peer's SDA or stretch choice. -/
theorem enter_wait_from_low (s : State a) (inputs : List Input)
    (phase : s.phase = .low) (countdown : s.countdown = 3#8)
    (row : s.current = streamRow) (sclDrive : s.pins.enabled[0] = true)
    (length : inputs.length = 4) (ordinary : ∀ i ∈ inputs, i.Runtime)
    (resolved : ∀ k (inside : k < inputs.length), ∃ peer : Pinwheel.I2C.Pins,
      inputs[k].rawInputs = StreamingI2CRead.resolvedRaw s.pins peer) :
    WaitEntry (run program s inputs) := by
  have sampledLow (k : Nat) (inside : k < inputs.length) : inputs[k].rawInputs[0] = false := by
    obtain ⟨peer,raw⟩ := resolved k inside
    rw [raw]
    change (StreamingI2CRead.resolvedRaw s.pins peer).getLsbD 0 = _
    rw [StreamingI2CRead.resolvedRaw_scl]
    change (!s.pins.enabled[0] && peer.scl == .release) = _
    rw [sclDrive]
    rfl
  let cut := run program s (inputs.take 3)
  have ordinaryTake : ∀ i ∈ inputs.take 3, i.Runtime := fun i hi => ordinary i (List.mem_of_mem_take hi)
  have inlineLength : (inputs.take 3).length = 3 := by simp [length]
  have ⟨stillLow,left,_,_,current⟩ := low_prefix program s (inputs.take 3) phase ordinaryTake
    (by simp [inlineLength,countdown])
  have terminal : cut.countdown = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    simpa [cut,inlineLength,countdown] using left
  have priorLow : cut.samplerFirst[0] = false := by
    unfold cut
    rw [List.take_succ_eq_append_getElem (show 2 < inputs.length by omega),run_append]
    change (step program inputs[2] (run program s (inputs.take 2))).samplerFirst[0] = _
    exact (congrArg (fun v : BitVec 2 => v[0])
      (step_samples program (run program s (inputs.take 2)) inputs[2]
        (ordinary _ (List.getElem_mem _))).1).trans (sampledLow 2 (by omega))
  have decompose : inputs.take 3 ++ [inputs[3]] = inputs := by
    rw [← List.take_succ_eq_append_getElem (show 3 < inputs.length by omega),List.take_of_length_le (by omega)]
  rw [← decompose,run_append]
  exact enter_wait cut inputs[3] (ordinary _ (List.getElem_mem _)) stillLow terminal
    (current.trans row) priorLow (sampledLow 3 (by omega))

end Pinwheel.Program.StreamingI2CDeadline
