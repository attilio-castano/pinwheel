import Pinwheel.Program.StreamingReadyCompile
import Pinwheel.Program.StreamingReadyGuardedCell
import Pinwheel.Program.StreamingI2CRead

/-! The sampled-ready I²C image polls SCL through a two-stage sampler.
An SDA capture uses the first raw sample at which SCL was high. -/
namespace Pinwheel.Program.StreamingI2CDeadline
open Pinwheel.Program.StreamingReady

abbrev programFor (profile : I2cProfile) : Program := (i2cImage profile).program
abbrev streamRowFor (profile : I2cProfile) : Instruction :=
  .stream (i2cCell profile) (some (i2cGuard profile 1 1))

abbrev program : Program := programFor .standard
abbrev streamRow : Instruction := streamRowFor .standard

structure WaitEntry (s : State a)
    (profile : I2cProfile := .standard) : Prop where
  phase : s.phase = .waiting
  current : s.current = streamRowFor profile
  countdown : s.countdown = BitVec.ofNat 8 profile.budgetMinusOne.val
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

private theorem matches_scl (profile : I2cProfile) (raw : BitVec 2) :
    (i2cGuard profile 1 1).matches raw = raw[0] := by
  change (i2cGuard .standard 1 1).matches raw = raw[0]
  decide +revert +kernel

private theorem low_cut (profile : I2cProfile) (s : State a) (h : WaitEntry s profile) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, i.Runtime) (stretch n : Nat)
    (inside : n ≤ inputs.length) (before : n < stretch + 2)
    (low : ∀ k (hk : k < inputs.length), k < stretch → inputs[k].rawInputs[0] = false) :
    (run (programFor profile) s (inputs.take n)).samplerSecond[0] = false := by
  cases n with
  | zero => exact h.secondLow
  | succ n =>
    cases n with
    | zero =>
      have bound : 0 < inputs.length := by omega
      rw [List.take_succ_eq_append_getElem bound]
      exact (congrArg (fun v : BitVec 2 => v[0])
        (step_samples (programFor profile) s inputs[0] (ordinary _ (List.getElem_mem bound))).2).trans h.firstLow
    | succ k =>
      rw [cut_after_two (programFor profile) s inputs ordinary k inside]
      exact low k (by omega) (by omega)

private theorem miss_append (p : Program) (s : State a) (xs : List Input) (last : Input)
    (missed : MissHistory p s xs) (ordinary : last.Runtime)
    (miss : (run p s xs).waitReady = false) :
    MissHistory p s (xs ++ [last]) := by
  induction xs generalizing s with
  | nil => exact ⟨ordinary,miss,True.intro⟩
  | cons i xs ih => exact ⟨missed.1,missed.2.1,ih (step p i s) missed.2.2 miss⟩

private theorem stream_limit (profile : I2cProfile) (s : State a) (row : s.current = streamRowFor profile) :
    s.current.guard.limit = .misses profile.budgetMinusOne := by
  rw [row]
  rfl

private theorem countdown_toNat (s : State a) (profile : I2cProfile)
    (entry : WaitEntry s profile) : s.countdown.toNat = profile.budgetMinusOne.val := by
  rw [entry.countdown, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.lt_trans profile.budgetMinusOne.isLt (by decide)

private theorem Stimulus.misses {profile : I2cProfile} {s : State a} {stretch sda inputs}
    (stimulus : Stimulus s stretch sda inputs) (entry : WaitEntry s profile)
    (n : Nat) (inside : n ≤ inputs.length) (budget : n ≤ profile.budgetMinusOne.val)
    (delayed : n ≤ stretch + 2) :
    MissHistory (programFor profile) s (inputs.take n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have prior := ih (by omega) (by omega) (by omega)
    have within : (inputs.take n).length ≤ s.countdown.toNat := by
      rw [countdown_toNat s profile entry,List.length_take]
      omega
    have held := bounded_wait_prefix (programFor profile) s (inputs.take n) profile.budgetMinusOne
      entry.phase (stream_limit profile s entry.current) prior within
    have low (k : Nat) (hk : k < inputs.length) (early : k < stretch) :
        inputs[k].rawInputs[0] = false := by
      simp [stimulus.scl entry.release k hk,Nat.not_le.mpr early]
    have sample := low_cut profile s entry inputs stimulus.ordinary stretch n (by omega) (by omega) low
    have miss : (run (programFor profile) s (inputs.take n)).waitReady = false := by
      rw [State.waitReady,held.2.2.2.2,entry.current]
      exact (matches_scl profile _).trans sample
    have index : n < inputs.length := by omega
    rw [List.take_succ_eq_append_getElem index]
    exact miss_append (programFor profile) s _ _ prior (stimulus.ordinary _ (List.getElem_mem index)) miss

structure WaitingPrefix (s cut : State a) (trace cutTrace : BitTrace) (n : Nat)
    (profile : I2cProfile := .standard) : Prop where
  phase : cut.phase = .waiting
  countdown : cut.countdown.toNat = profile.budgetMinusOne.val - n
  pins : cut.pins = s.pins
  remaining : cut.remaining = s.remaining
  current : cut.current = streamRowFor profile
  captured : cutTrace.captured = trace.captured

/-- Before the aperture reaches the released SCL, every poll misses and
holds the pad pose and the capture prefix. -/
theorem waiting_prefix_for (profile : I2cProfile) (s : State a) (entry : WaitEntry s profile) (trace : BitTrace)
    (stretch : Nat) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (stimulus : Stimulus s stretch sda inputs) (n : Nat)
    (inside : n ≤ inputs.length) (budget : n ≤ profile.budgetMinusOne.val) (delayed : n ≤ stretch + 2) :
    WaitingPrefix s (run (programFor profile) s (inputs.take n)) trace
      (traceRun (programFor profile) s trace (inputs.take n)) n profile := by
  have len : (inputs.take n).length = n := by simp [List.length_take,Nat.min_eq_left inside]
  have result := GuardedCell.waiting_prefix (programFor profile) s trace (inputs.take n) profile.budgetMinusOne
    entry.phase (stream_limit profile s entry.current) (stimulus.misses entry n inside budget delayed)
    (by simpa only [len,countdown_toNat s profile entry] using budget)
  exact ⟨result.phase,by simpa only [countdown_toNat s profile entry,len] using result.countdown,
    result.pins,result.remaining,result.current.trans entry.current,result.captured⟩

theorem Stimulus.resolved_at_cut_for (profile : I2cProfile) {s : State a} {stretch sda inputs}
    (stimulus : Stimulus s stretch sda inputs) (entry : WaitEntry s profile)
    (n : Nat) (inside : n < inputs.length) (budget : n ≤ profile.budgetMinusOne.val) (delayed : n ≤ stretch + 2) :
    inputs[n].rawInputs = StreamingI2CRead.resolvedRaw
      (run (programFor profile) s (inputs.take n)).pins (target stretch sda n) := by
  rw [(waiting_prefix_for profile s entry {} stretch sda inputs stimulus n (Nat.le_of_lt inside) budget delayed).pins]
  exact stimulus.resolved n inside

/-- Construct the stimulus from a peer connected to the actual evolving
controller pads. Each prior miss made the original pad pose remain valid. -/
theorem Stimulus.of_runtime_resolved_for (profile : I2cProfile) (s : State a) (entry : WaitEntry s profile)
    (stretch : Nat) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, i.Runtime)
    (raw : ∀ k (inside : k < inputs.length), inputs[k].rawInputs = StreamingI2CRead.resolvedRaw
      (run (programFor profile) s (inputs.take k)).pins (target stretch sda k))
    (budget : inputs.length ≤ profile.budgetMinusOne.val + 1) (delayed : inputs.length ≤ stretch + 3) :
    Stimulus s stretch sda inputs := by
  have take (n : Nat) (inside : n ≤ inputs.length) : Stimulus s stretch sda (inputs.take n) := by
    induction n with
    | zero => constructor <;> simp
    | succ n ih =>
      have earlier : n ≤ inputs.length := by omega
      have prior := ih earlier
      have len : (inputs.take n).length = n := by simp [List.length_take,Nat.min_eq_left earlier]
      have held := (waiting_prefix_for profile s entry {} stretch sda (inputs.take n) prior n
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

structure CaptureResult (s final : State a) (trace finalTrace : BitTrace) (bit : Bool)
    (profile : I2cProfile := .standard) : Prop where
  phase : final.phase = .high
  pins : final.pins = s.pins
  remaining : final.remaining = s.remaining
  current : final.current = streamRowFor profile
  captured : finalTrace.captured = trace.captured ++ [bit]

/-- The raw SCL rise at clock `stretch` reaches the aperture two clocks later.
A ready sample at the last poll still captures one SDA bit. -/
theorem stretch_success_for (profile : I2cProfile) (s : State a) (entry : WaitEntry s profile) (trace : BitTrace)
    (stretch : Nat) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (stimulus : Stimulus s stretch sda inputs) (timely : stretch + 2 ≤ profile.budgetMinusOne.val)
    (length : inputs.length = stretch + 3) :
    CaptureResult s (run (programFor profile) s inputs) trace (traceRun (programFor profile) s trace inputs)
      (StreamingI2CRead.resolvedRaw s.pins (target stretch sda stretch))[1] profile := by
  have index : stretch + 2 < inputs.length := by omega
  let misses := inputs.take (stretch + 2)
  let cut := run (programFor profile) s misses
  let last := inputs[stretch + 2]
  have history := stimulus.misses entry (stretch + 2) (by omega) timely (Nat.le_refl _)
  have within : misses.length ≤ s.countdown.toNat := by
    simp only [misses,List.length_take,countdown_toNat s profile entry]
    omega
  have limit := stream_limit profile s entry.current
  have poll := GuardedCell.bounded_poll (programFor profile) s trace misses last profile.budgetMinusOne
    entry.phase limit history within (stimulus.ordinary last (List.getElem_mem index))
  have held := bounded_wait_prefix (programFor profile) s misses profile.budgetMinusOne
    entry.phase limit history within
  have aperture : cut.samplerSecond = inputs[stretch].rawInputs :=
    cut_after_two (programFor profile) s inputs stimulus.ordinary stretch (by omega)
  have ready : cut.waitReady = true := by
    change (run (programFor profile) s misses).waitReady = true
    rw [State.waitReady,held.2.2.2.2,entry.current]
    change (i2cGuard profile 1 1).matches cut.samplerSecond = true
    rw [matches_scl profile,aperture,stimulus.scl entry.release stretch (by omega)]
    exact decide_eq_true_eq.mpr (Nat.le_refl _)
  have result := poll.capture ready (by rw [entry.current]; rfl) (by rw [entry.current]; rfl)
  have decomposition : misses ++ [last] = inputs := by
    unfold misses last
    rw [← List.take_succ_eq_append_getElem index,List.take_of_length_le (by omega)]
  rw [decomposition] at result
  have bit : cut.samplerSecond[s.current.cell.rxInput.val] =
      (StreamingI2CRead.resolvedRaw s.pins (target stretch sda stretch))[1] := by
    have port : s.current.cell.rxInput.val = 1 := by rw [entry.current]; rfl
    rw [← BitVec.getLsbD_eq_getElem s.current.cell.rxInput.isLt,
      port,aperture,stimulus.resolved stretch (by omega)]
    rfl
  rw [bit] at result
  exact ⟨result.phase,result.pins,result.remaining,result.current.trans entry.current,result.captured⟩

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
theorem one_late_for (profile : I2cProfile) (s : State a) (entry : WaitEntry s profile) (trace : BitTrace)
    (sda : Pinwheel.I2C.Drive) (inputs : List Input) (minimum : 2 ≤ profile.budgetMinusOne.val)
    (stimulus : Stimulus s (profile.budgetMinusOne.val - 1) sda inputs)
    (length : inputs.length = profile.budgetMinusOne.val + 1) (related : trace.Related s) (structural : s.Structural) :
    TimeoutResult s (run (programFor profile) s inputs) trace (traceRun (programFor profile) s trace inputs) := by
  let poll := profile.budgetMinusOne.val
  have pollMin : 2 ≤ poll := minimum
  have index : poll < inputs.length := by omega
  let misses := inputs.take poll
  let cut := run (programFor profile) s misses
  let last := inputs[poll]
  have history := stimulus.misses entry poll (by omega) (Nat.le_refl _) (by omega)
  have deadline : misses.length = s.countdown.toNat := by
    simp only [misses,List.length_take,countdown_toNat s profile entry]
    omega
  have limit := stream_limit profile s entry.current
  have outcome := GuardedCell.bounded_poll (programFor profile) s trace misses last profile.budgetMinusOne
    entry.phase limit history (Nat.le_of_eq deadline) (stimulus.ordinary last (List.getElem_mem index))
  have held := bounded_wait_prefix (programFor profile) s misses profile.budgetMinusOne
    entry.phase limit history (Nat.le_of_eq deadline)
  have aperture : cut.samplerSecond = inputs[poll - 2].rawInputs := by
    have sample := cut_after_two (programFor profile) s inputs stimulus.ordinary (poll - 2) (by omega)
    simpa only [Nat.sub_add_cancel pollMin] using sample
  have miss : cut.waitReady = false := by
    change (run (programFor profile) s misses).waitReady = false
    rw [State.waitReady,held.2.2.2.2,entry.current]
    change (i2cGuard profile 1 1).matches cut.samplerSecond = false
    rw [matches_scl profile,aperture,stimulus.scl entry.release (poll - 2) (by omega)]
    exact decide_eq_false (by omega)
  have timeout := outcome.timeout miss deadline
  have decomposition : misses ++ [last] = inputs := by
    unfold misses last
    rw [← List.take_succ_eq_append_getElem index,List.take_of_length_le (by omega)]
  rw [decomposition] at timeout
  have seen : (run (programFor profile) s inputs).samplerSecond = inputs[poll - 1].rawInputs := by
    have lastSample := cut_after_two (programFor profile) s inputs stimulus.ordinary (poll - 1) (by omega)
    have cutLength : (poll - 1) + 2 = inputs.length := by omega
    simpa only [cutLength,List.take_length] using lastSample
  refine ⟨timeout.phase,timeout.pins,timeout.remaining,timeout.partialFlushed,timeout.captured,
    timeout.recoverable related structural,?_⟩
  rw [seen,stimulus.scl entry.release (poll - 1) (by omega)]
  exact decide_eq_true_eq.mpr (by omega)

private theorem release_high_pins (profile : I2cProfile) (s : State a) (row : s.current = streamRowFor profile) :
    s.highPins.levels = 0#3 ∧ s.highPins.enabled[0] = false := by
  unfold State.highPins
  rw [row]
  cases s.lastCell <;> cases s.cellBit <;>
    simp [Instruction.isStream,Instruction.cell,Streaming.Cell.dataPins,Streaming.Cell.basePins,i2cCell]

/-- The transition out of ordinary LOW releases SCL. The raw clock at this
transition still sees the old LOW drive, as did the preceding raw clock. -/
theorem enter_wait_for (profile : I2cProfile) (s : State a) (i : Input) (runtime : i.Runtime)
    (low : s.phase = .low) (count : s.countdown = 0#8) (row : s.current = streamRowFor profile)
    (priorLow : s.samplerFirst[0] = false) (rawLow : i.rawInputs[0] = false) :
    WaitEntry (step (programFor profile) i s) profile := by
  have busy : s.phase.busy = true := by rw [low]; rfl
  have moved : engine (programFor profile) s =
      {s with phase := .waiting, countdown := BitVec.ofNat 8 profile.budgetMinusOne.val, pins := s.highPins} := by
    rw [engine,low]
    have guarded : s.current.hasHighGuard = true := by rw [row]; rfl
    have budget : s.current.guard.limit.initialCountdown = BitVec.ofNat 8 profile.budgetMinusOne.val := by rw [row]; rfl
    rw [count,guarded,budget]
    rfl
  rw [step_busy_eq_clock (programFor profile) s i runtime busy,clock,moved]
  have pins := release_high_pins profile s row
  exact ⟨rfl,row,rfl,pins.1,pins.2,rawLow,priorLow⟩

/-- A full four-clock LOW interval primes both samplers, independently of
their older contents and of the peer's SDA or stretch choice. -/
theorem enter_wait_from_low_for (profile : I2cProfile) (s : State a) (inputs : List Input)
    (phase : s.phase = .low) (countdown : s.countdown = 3#8)
    (row : s.current = streamRowFor profile) (sclDrive : s.pins.enabled[0] = true)
    (length : inputs.length = 4) (ordinary : ∀ i ∈ inputs, i.Runtime)
    (resolved : ∀ k (inside : k < inputs.length), ∃ peer : Pinwheel.I2C.Pins,
      inputs[k].rawInputs = StreamingI2CRead.resolvedRaw s.pins peer) :
    WaitEntry (run (programFor profile) s inputs) profile := by
  have sampledLow (k : Nat) (inside : k < inputs.length) : inputs[k].rawInputs[0] = false := by
    obtain ⟨peer,raw⟩ := resolved k inside
    rw [raw]
    change (StreamingI2CRead.resolvedRaw s.pins peer).getLsbD 0 = _
    rw [StreamingI2CRead.resolvedRaw_scl]
    change (!s.pins.enabled[0] && peer.scl == .release) = _
    rw [sclDrive]
    rfl
  let cut := run (programFor profile) s (inputs.take 3)
  have ordinaryTake : ∀ i ∈ inputs.take 3, i.Runtime := fun i hi => ordinary i (List.mem_of_mem_take hi)
  have inlineLength : (inputs.take 3).length = 3 := by simp [length]
  have ⟨stillLow,left,_,_,current⟩ := low_prefix (programFor profile) s (inputs.take 3) phase ordinaryTake
    (by simp [inlineLength,countdown])
  have terminal : cut.countdown = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    simpa [cut,inlineLength,countdown] using left
  have priorLow : cut.samplerFirst[0] = false := by
    unfold cut
    rw [List.take_succ_eq_append_getElem (show 2 < inputs.length by omega),run_append]
    change (step (programFor profile) inputs[2] (run (programFor profile) s (inputs.take 2))).samplerFirst[0] = _
    exact (congrArg (fun v : BitVec 2 => v[0])
      (step_samples (programFor profile) (run (programFor profile) s (inputs.take 2)) inputs[2]
        (ordinary _ (List.getElem_mem _))).1).trans (sampledLow 2 (by omega))
  have decompose : inputs.take 3 ++ [inputs[3]] = inputs := by
    rw [← List.take_succ_eq_append_getElem (show 3 < inputs.length by omega),List.take_of_length_le (by omega)]
  rw [← decompose,run_append]
  exact enter_wait_for profile cut inputs[3] (ordinary _ (List.getElem_mem _)) stillLow terminal
    (current.trans row) priorLow (sampledLow 3 (by omega))

theorem waiting_prefix (s : State a) (entry : WaitEntry s) (trace : BitTrace)
    (stretch : Nat) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (stimulus : Stimulus s stretch sda inputs) (n : Nat)
    (inside : n ≤ inputs.length) (budget : n ≤ 30) (delayed : n ≤ stretch + 2) :
    WaitingPrefix s (run program s (inputs.take n)) trace
      (traceRun program s trace (inputs.take n)) n :=
  waiting_prefix_for .standard s entry trace stretch sda inputs stimulus n inside budget delayed

theorem Stimulus.resolved_at_cut {s : State a} {stretch sda inputs}
    (stimulus : Stimulus s stretch sda inputs) (entry : WaitEntry s)
    (n : Nat) (inside : n < inputs.length) (budget : n ≤ 30) (delayed : n ≤ stretch + 2) :
    inputs[n].rawInputs = StreamingI2CRead.resolvedRaw
      (run program s (inputs.take n)).pins (target stretch sda n) :=
  Stimulus.resolved_at_cut_for .standard stimulus entry n inside budget delayed

theorem Stimulus.of_runtime_resolved (s : State a) (entry : WaitEntry s)
    (stretch : Nat) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (ordinary : ∀ i ∈ inputs, i.Runtime)
    (raw : ∀ k (inside : k < inputs.length), inputs[k].rawInputs = StreamingI2CRead.resolvedRaw
      (run program s (inputs.take k)).pins (target stretch sda k))
    (budget : inputs.length ≤ 31) (delayed : inputs.length ≤ stretch + 3) :
    Stimulus s stretch sda inputs :=
  Stimulus.of_runtime_resolved_for .standard s entry stretch sda inputs ordinary raw budget delayed

theorem stretch_success (s : State a) (entry : WaitEntry s) (trace : BitTrace)
    (stretch : Nat) (sda : Pinwheel.I2C.Drive) (inputs : List Input)
    (stimulus : Stimulus s stretch sda inputs) (timely : stretch ≤ 28)
    (length : inputs.length = stretch + 3) :
    CaptureResult s (run program s inputs) trace (traceRun program s trace inputs)
      (StreamingI2CRead.resolvedRaw s.pins (target stretch sda stretch))[1] :=
  stretch_success_for .standard s entry trace stretch sda inputs stimulus (by change stretch + 2 ≤ 30; omega) length

theorem one_late (s : State a) (entry : WaitEntry s) (trace : BitTrace)
    (sda : Pinwheel.I2C.Drive) (inputs : List Input) (stimulus : Stimulus s 29 sda inputs)
    (length : inputs.length = 31) (related : trace.Related s) (structural : s.Structural) :
    TimeoutResult s (run program s inputs) trace (traceRun program s trace inputs) :=
  one_late_for .standard s entry trace sda inputs (by decide) stimulus length related structural

theorem enter_wait (s : State a) (i : Input) (runtime : i.Runtime)
    (low : s.phase = .low) (count : s.countdown = 0#8) (row : s.current = streamRow)
    (priorLow : s.samplerFirst[0] = false) (rawLow : i.rawInputs[0] = false) :
    WaitEntry (step program i s) :=
  enter_wait_for .standard s i runtime low count row priorLow rawLow

theorem enter_wait_from_low (s : State a) (inputs : List Input)
    (phase : s.phase = .low) (countdown : s.countdown = 3#8)
    (row : s.current = streamRow) (sclDrive : s.pins.enabled[0] = true)
    (length : inputs.length = 4) (ordinary : ∀ i ∈ inputs, i.Runtime)
    (resolved : ∀ k (inside : k < inputs.length), ∃ peer : Pinwheel.I2C.Pins,
      inputs[k].rawInputs = StreamingI2CRead.resolvedRaw s.pins peer) :
    WaitEntry (run program s inputs) :=
  enter_wait_from_low_for .standard s inputs phase countdown row sclDrive length ordinary resolved

end Pinwheel.Program.StreamingI2CDeadline
