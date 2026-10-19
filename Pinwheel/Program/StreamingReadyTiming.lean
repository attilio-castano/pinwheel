import Pinwheel.Program.StreamingReadyEventualService

namespace Pinwheel.Program.StreamingReady

/-- A timed HIGH tick cannot be held up by queue or guard service. -/
theorem step_high_wait (p : Program) (s : State a) (i : Input) (runtime : i.Runtime)
    (high : s.phase = .high) (nonzero : s.countdown ≠ 0#8) :
    (step p i s).phase = .high ∧ (step p i s).countdown = s.countdown-1#8 ∧
      (step p i s).pins = s.pins ∧ (step p i s).remaining = s.remaining := by
  rw [step_busy_eq_clock p s i runtime (by simp [high,Phase.busy])]
  simp [clock,engine,high,nonzero]

theorem step_high_terminal (p : Program) (s : State a) (i : Input) (runtime : i.Runtime)
    (high : s.phase = .high) (zero : s.countdown = 0#8) :
    (step p i s).phase = (if s.current.isStream && s.remaining.toNat>1 then .boundary else .fetch) := by
  rw [step_busy_eq_clock p s i runtime (by simp [high,Phase.busy])]
  simp [clock,engine,high,zero]

theorem step_low_wait (p : Program) (s : State a) (i : Input) (runtime : i.Runtime)
    (low : s.phase = .low) (nonzero : s.countdown ≠ 0#8) :
    (step p i s).phase = .low ∧ (step p i s).countdown = s.countdown-1#8 ∧
      (step p i s).pins = s.pins ∧ (step p i s).remaining = s.remaining ∧
      (step p i s).current = s.current := by
  rw [step_busy_eq_clock p s i runtime (by simp [low,Phase.busy])]
  simp [clock,engine,low,nonzero]

/-- LOW releases HIGH exactly once, before a sampled-ready wait can capture. -/
theorem step_low_terminal (p : Program) (s : State a) (i : Input) (runtime : i.Runtime)
    (low : s.phase = .low) (zero : s.countdown = 0#8) :
    (step p i s).phase = (if s.current.hasHighGuard then .waiting else .high) ∧
      (step p i s).pins = s.highPins ∧
      (step p i s).remaining = s.remaining := by
  rw [step_busy_eq_clock p s i runtime (by simp [low,Phase.busy])]
  cases guarded : s.current.hasHighGuard
  all_goals simp [clock,engine,low,zero,guarded,State.enterHigh,State.captureData]

/-- Readiness wins even with zero countdown, and never emits a second drive edge. -/
theorem step_wait_ready (p : Program) (s : State a) (i : Input) (runtime : i.Runtime)
    (waiting : s.phase = .waiting) (ready : s.waitReady = true) :
    (step p i s).phase = (if s.current.isStream then .high else .fetch) ∧
      (step p i s).pins = s.pins ∧ (step p i s).remaining = s.remaining ∧
      (step p i s).current = s.current := by
  rw [step_busy_eq_clock p s i runtime (by simp [waiting,Phase.busy])]
  cases stream : s.current.isStream
  all_goals simp [clock,engine,waiting,ready,stream,State.enterHigh,State.captureData]

theorem step_wait_miss (p : Program) (s : State a) (i : Input) (runtime : i.Runtime)
    (waiting : s.phase = .waiting) (ready : s.waitReady = false)
    (expired : s.current.guard.limit.expires s.countdown = false) :
    (step p i s).phase = .waiting ∧
      (step p i s).countdown = s.current.guard.limit.poll s.countdown ∧
      (step p i s).pins = s.pins ∧ (step p i s).remaining = s.remaining ∧
      (step p i s).current = s.current := by
  rw [step_busy_eq_clock p s i runtime (by simp [waiting,Phase.busy])]
  simp [clock,engine,waiting,ready,expired]

/-- Every prefix inside HIGH has its exact countdown, independent of queue service. -/
theorem high_prefix (p : Program) (s : State addrBits) (inputs : List Input)
    (high : s.phase = .high) (runtime : ∀ i ∈ inputs, i.Runtime)
    (within : inputs.length ≤ s.countdown.toNat) :
    (run p s inputs).phase = .high ∧
    (run p s inputs).countdown.toNat = s.countdown.toNat - inputs.length ∧
    (run p s inputs).pins = s.pins ∧ (run p s inputs).remaining = s.remaining := by
  induction inputs generalizing s with
  | nil => simp [run, high]
  | cons i inputs induction =>
    have ordinary : i.Runtime := runtime i (by simp)
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have nonzero : s.countdown ≠ 0#8 := by
      intro zero
      simp [zero] at positive
    have next := step_high_wait p s i ordinary high nonzero
    have subtraction : (s.countdown - 1#8).toNat = s.countdown.toNat - 1 := by
      apply BitVec.toNat_sub_of_le
      change 1 ≤ s.countdown.toNat
      omega
    obtain ⟨laterHigh, laterCount, laterPins, laterRemaining⟩ := induction (step p i s) next.1
      (fun i member => runtime i (by simp [member])) (by
        rw [next.2.1, subtraction]
        simp only [List.length_cons] at within
        omega)
    constructor
    · exact laterHigh
    constructor
    · simpa only [run, List.foldl_cons, next.2.1, subtraction, List.length_cons,
        Nat.sub_sub, Nat.add_comm] using laterCount
    exact ⟨laterPins.trans next.2.2.1, laterRemaining.trans next.2.2.2⟩

/-- HIGH lasts exactly the declared countdown plus its terminal interval. -/
theorem high_interval (p : Program) (s : State addrBits) (inputs : List Input) (last : Input)
    (high : s.phase = .high) (runtime : ∀ i ∈ inputs, i.Runtime) (lastRuntime : last.Runtime)
    (length : inputs.length = s.countdown.toNat) :
    (run p s inputs).phase = .high ∧ (run p s inputs).pins = s.pins ∧
    (step p last (run p s inputs)).phase ≠ .high := by
  obtain ⟨stillHigh, count, pins, _⟩ := high_prefix p s inputs high runtime (Nat.le_of_eq length)
  have zero : (run p s inputs).countdown = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  refine ⟨stillHigh, pins, ?_⟩
  rw [(step_high_terminal p (run p s inputs) last lastRuntime stillHigh zero)]
  split <;> decide

/-- Two ordinary edges establish the delayed sample regardless of the earlier history. -/
theorem run_two_samples (p : Program) (s : State addrBits) (earlier : List Input) (first second : Input)
    (firstRuntime : first.Runtime) (secondRuntime : second.Runtime) :
    (run p s (earlier ++ [first, second])).samplerFirst = second.rawInputs ∧
    (run p s (earlier ++ [first, second])).samplerSecond = first.rawInputs := by
  have firstSample := step_samples p (run p s earlier) first firstRuntime
  have secondSample := step_samples p (step p first (run p s earlier)) second secondRuntime
  rw [firstSample.1] at secondSample
  simpa [run, List.foldl_append] using secondSample

/-- The sampled RX value is the earlier raw input, rather than the current pin value. -/
theorem capture_after_two (p : Program) (s : State addrBits) (earlier : List Input) (first second : Input)
    (firstRuntime : first.Runtime) (secondRuntime : second.Runtime)
    (capture : (run p s (earlier ++ [first, second])).captures = true) :
    (run p s (earlier ++ [first, second])).rxEvent =
      [first.rawInputs[(run p s (earlier ++ [first, second])).current.cell.rxInput.val]] := by
  simp only [State.rxEvent, capture, ↓reduceIte, (run_two_samples p s earlier first second firstRuntime secondRuntime).2]



/-- Misses are tested on the actual pre-edge second sampler, not current raw pins. -/
def MissHistory (p : Program) (s : State a) : List Input → Prop
  | [] => True
  | i :: inputs => i.Runtime ∧ s.waitReady = false ∧ MissHistory p (step p i s) inputs

/-- A positive budget counts missed polls exactly; host service does not reset it. -/
theorem bounded_wait_prefix (p : Program) (s : State a) (inputs : List Input) (budget : Fin 255)
    (waiting : s.phase = .waiting) (limit : s.current.guard.limit = .misses budget)
    (missed : MissHistory p s inputs) (within : inputs.length ≤ s.countdown.toNat) :
    (run p s inputs).phase = .waiting ∧
      (run p s inputs).countdown.toNat = s.countdown.toNat-inputs.length ∧
      (run p s inputs).pins = s.pins ∧ (run p s inputs).remaining = s.remaining ∧
      (run p s inputs).current = s.current := by
  induction inputs generalizing s with
  | nil => simp [run,waiting]
  | cons i inputs induction =>
    rcases missed with ⟨runtime,ready,later⟩
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have nonzero : s.countdown ≠ 0#8 := by
      intro zero
      simp [zero] at positive
    have next := step_wait_miss p s i runtime waiting ready (by simp [limit,WaitLimit.expires,nonzero])
    have count : (step p i s).countdown = s.countdown-1 := by
      simpa only [limit,WaitLimit.poll] using next.2.1
    have subtraction : (s.countdown-1).toNat = s.countdown.toNat-1 := by
      apply BitVec.toNat_sub_of_le
      change 1 ≤ s.countdown.toNat
      omega
    obtain ⟨laterWait,laterCount,laterPins,laterRemaining,laterCurrent⟩ :=
      induction (step p i s) next.1 (by rw [next.2.2.2.2]; exact limit) later (by
        rw [count,subtraction]
        simp only [List.length_cons] at within
        omega)
    refine ⟨laterWait,?_,laterPins.trans next.2.2.1,
      laterRemaining.trans next.2.2.2.1,laterCurrent.trans next.2.2.2.2⟩
    simpa only [run,List.foldl_cons,count,subtraction,List.length_cons,Nat.sub_sub,Nat.add_comm] using laterCount

/-- The final missed poll faults; the same final poll would accept readiness first. -/
theorem bounded_wait_timeout (p : Program) (s : State a) (inputs : List Input) (last : Input)
    (budget : Fin 255) (waiting : s.phase = .waiting)
    (limit : s.current.guard.limit = .misses budget) (missed : MissHistory p s inputs)
    (length : inputs.length = s.countdown.toNat) (runtime : last.Runtime)
    (lastMiss : (run p s inputs).waitReady = false) :
    (run p s inputs).phase = .waiting ∧ (run p s inputs).pins = s.pins ∧
      (step p last (run p s inputs)).phase = .fault ∧
      (step p last (run p s inputs)).rxProduced = (run p s inputs).rxProduced ∧
      (step p last (run p s inputs)).rxUsed = 0 ∧
      (step p last (run p s inputs)).rxPartial = 0 := by
  obtain ⟨phase,count,pins,_,current⟩ := bounded_wait_prefix p s inputs budget waiting limit missed (Nat.le_of_eq length)
  have zero : (run p s inputs).countdown = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  refine ⟨phase,pins,?_⟩
  rw [step_busy_eq_clock p _ last runtime (by simp [phase,Phase.busy])]
  simp [clock,engine,phase,lastMiss,current,limit,WaitLimit.expires,zero,State.timeoutFault]


/-- LOW countdown and drive remain exact before release into HIGH or WAIT. -/
theorem low_prefix (p : Program) (s : State a) (inputs : List Input)
    (low : s.phase = .low) (runtime : ∀ i ∈ inputs, i.Runtime)
    (within : inputs.length ≤ s.countdown.toNat) :
    (run p s inputs).phase = .low ∧
      (run p s inputs).countdown.toNat = s.countdown.toNat-inputs.length ∧
      (run p s inputs).pins = s.pins ∧ (run p s inputs).remaining = s.remaining ∧
      (run p s inputs).current = s.current := by
  induction inputs generalizing s with
  | nil => simp [run,low]
  | cons i inputs induction =>
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have nonzero : s.countdown ≠ 0#8 := by intro zero; simp [zero] at positive
    have next := step_low_wait p s i (runtime i (by simp)) low nonzero
    have subtraction : (s.countdown-1#8).toNat = s.countdown.toNat-1 := by
      apply BitVec.toNat_sub_of_le
      change 1 ≤ s.countdown.toNat
      omega
    obtain ⟨laterLow,laterCount,laterPins,laterRemaining,laterCurrent⟩ := induction (step p i s) next.1
      (fun i member => runtime i (by simp [member])) (by
        rw [next.2.1,subtraction]
        simp only [List.length_cons] at within
        omega)
    refine ⟨laterLow,?_,laterPins.trans next.2.2.1,laterRemaining.trans next.2.2.2.1,
      laterCurrent.trans next.2.2.2.2⟩
    simpa only [run,List.foldl_cons,next.2.1,subtraction,List.length_cons,Nat.sub_sub,Nat.add_comm] using laterCount

/-- The second sampler sees a stable predicate after two ordinary clocks. -/
theorem sample_predicate_delay (p : Program) (s : State a) (inputs : List Input)
    (predicate : BitVec 2 → Prop) (long : 2 ≤ inputs.length)
    (runtime : ∀ i ∈ inputs, i.Runtime) (stable : ∀ i ∈ inputs, predicate i.rawInputs) :
    predicate (run p s inputs).samplerSecond := by
  have keep : ∀ (s : State a) (inputs : List Input), predicate s.samplerFirst → predicate s.samplerSecond →
      (∀ i ∈ inputs, i.Runtime) → (∀ i ∈ inputs, predicate i.rawInputs) →
      predicate (run p s inputs).samplerSecond := by
    intro s inputs first second runtime stable
    induction inputs generalizing s with
    | nil => exact second
    | cons i inputs induction =>
      have samples := step_samples p s i (runtime i (by simp))
      exact induction (step p i s) (by rw [samples.1]; exact stable i (by simp))
        (by rw [samples.2]; exact first) (fun i member => runtime i (by simp [member]))
        (fun i member => stable i (by simp [member]))
  cases inputs with
  | nil => simp at long
  | cons first rest =>
    cases rest with
    | nil => simp at long
    | cons second rest =>
      have firstSamples := step_samples p s first (runtime first (by simp))
      have secondSamples := step_samples p (step p first s) second (runtime second (by simp))
      exact keep (step p second (step p first s)) rest
        (by rw [secondSamples.1]; exact stable second (by simp))
        (by rw [secondSamples.2,firstSamples.1]; exact stable first (by simp))
        (fun i member => runtime i (by simp [member]))
        (fun i member => stable i (by simp [member]))

/-- Two missed polls with stable ready pins establish actual readiness next;
initial synchronizer contents are unrestricted. A budget of at least three
permits these two polls before the ready-wins final tick. -/
theorem bounded_ready_after_two (p : Program) (s : State a) (first second last : Input)
    (budget : Fin 255) (waiting : s.phase = .waiting)
    (limit : s.current.guard.limit = .misses budget)
    (missed : MissHistory p s [first,second]) (within : 2 ≤ s.countdown.toNat)
    (stableFirst : s.current.guard.matches first.rawInputs = true)
    (stableSecond : s.current.guard.matches second.rawInputs = true) (runtime : last.Runtime) :
    (run p s [first,second]).phase = .waiting ∧
      (run p s [first,second]).waitReady = true ∧
      (step p last (run p s [first,second])).phase = (if s.current.isStream then .high else .fetch) ∧
      (step p last (run p s [first,second])).pins = s.pins := by
  obtain ⟨phase,_,pins,_,current⟩ := bounded_wait_prefix p s [first,second] budget waiting limit missed (by simpa using within)
  have ordinary : ∀ i ∈ [first,second], i.Runtime := by
    rcases missed with ⟨firstRuntime,_,secondRuntime,_,_⟩
    intro i member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact firstRuntime
    · exact secondRuntime
  have sampled := sample_predicate_delay p s [first,second]
    (fun sample => s.current.guard.matches sample = true) (by simp) ordinary (by
      intro i member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact stableFirst
      · exact stableSecond)
  have ready : (run p s [first,second]).waitReady = true := by
    simpa only [State.waitReady,current] using sampled
  have accepted := step_wait_ready p _ last runtime phase ready
  exact ⟨phase,ready,by simpa only [current] using accepted.1,accepted.2.1.trans pins⟩

end Pinwheel.Program.StreamingReady
