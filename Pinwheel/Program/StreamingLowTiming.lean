import Pinwheel.Program.StreamingTiming

/-! Exact LOW timing and causal sampled capture under an explicit peer stability window. -/
namespace Pinwheel.Program.Streaming

theorem step_low_wait (p : Program) (s : State a) (i : Input)
    (runtime : i.Runtime) (low : s.phase = .low) (countdown : s.countdown ≠ 0#8) :
    (step p i s).phase = .low ∧ (step p i s).countdown = s.countdown - 1#8 ∧
      (step p i s).pins = s.pins ∧ (step p i s).current = s.current ∧
      (step p i s).remaining = s.remaining := by
  rw [step_busy_eq_clock p s i runtime (by simp [low,Phase.busy])]
  simp [clock,engine,low,countdown]

theorem low_prefix (p : Program) (s : State a) (inputs : List Input)
    (low : s.phase = .low) (runtime : ∀ i ∈ inputs, i.Runtime)
    (within : inputs.length ≤ s.countdown.toNat) :
    (run p s inputs).phase = .low ∧
      (run p s inputs).countdown.toNat = s.countdown.toNat - inputs.length ∧
      (run p s inputs).pins = s.pins ∧ (run p s inputs).current = s.current ∧
      (run p s inputs).remaining = s.remaining := by
  induction inputs generalizing s with
  | nil => simp [run,low]
  | cons i inputs induction =>
    have positive : 0 < s.countdown.toNat := by simp only [List.length_cons] at within; omega
    have nonzero : s.countdown ≠ 0#8 := by
      intro zero
      simp [zero] at positive
    have next := step_low_wait p s i (runtime i (by simp)) low nonzero
    have subtraction : (s.countdown - 1#8).toNat = s.countdown.toNat - 1 := by
      apply BitVec.toNat_sub_of_le
      change 1 ≤ s.countdown.toNat
      omega
    obtain ⟨laterLow,laterCount,laterPins,laterCurrent,laterRemaining⟩ := induction (step p i s) next.1
      (fun i member => runtime i (by simp [member])) (by
        rw [next.2.1,subtraction]
        simp only [List.length_cons] at within
        omega)
    refine ⟨laterLow,?_,laterPins.trans next.2.2.1,laterCurrent.trans next.2.2.2.1,
      laterRemaining.trans next.2.2.2.2⟩
    simpa only [run,List.foldl_cons,next.2.1,subtraction,List.length_cons,
      Nat.sub_sub,Nat.add_comm] using laterCount

/-- The programmed countdown expires without any queue-dependent HIGH delay. -/
theorem low_interval (p : Program) (s : State a) (inputs : List Input) (last : Input)
    (low : s.phase = .low) (runtime : ∀ i ∈ inputs, i.Runtime) (lastRuntime : last.Runtime)
    (length : inputs.length = s.countdown.toNat) :
    (run p s inputs).phase = .low ∧ (run p s inputs).countdown = 0#8 ∧
      (run p s inputs).pins = s.pins ∧ (run p s inputs).current = s.current ∧
      (step p last (run p s inputs)).phase = .high := by
  obtain ⟨stillLow,count,pins,current,_⟩ := low_prefix p s inputs low runtime (Nat.le_of_eq length)
  have zero : (run p s inputs).countdown = 0#8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  refine ⟨stillLow,zero,pins,current,?_⟩
  rw [step_busy_eq_clock p _ last lastRuntime (by simp [stillLow,Phase.busy])]
  simp [clock,engine,stillLow,zero]

private theorem stable_samples_run (p : Program) (s : State a) (inputs : List Input)
    (channel : Fin 2) (expected : Bool)
    (first : s.samplerFirst[channel.val] = expected) (second : s.samplerSecond[channel.val] = expected)
    (runtime : ∀ i ∈ inputs, i.Runtime) (stable : ∀ i ∈ inputs, i.rawInputs[channel.val] = expected) :
    (run p s inputs).samplerFirst[channel.val] = expected ∧
      (run p s inputs).samplerSecond[channel.val] = expected := by
  induction inputs generalizing s with
  | nil => exact ⟨first,second⟩
  | cons i inputs induction =>
    have samples := step_samples p s i (runtime i (by simp))
    exact induction (step p i s) (by rw [samples.1]; exact stable i (by simp))
      (by rw [samples.2]; exact first) (fun i member => runtime i (by simp [member]))
      (fun i member => stable i (by simp [member]))

theorem stable_sample_delay (p : Program) (s : State a) (inputs : List Input)
    (channel : Fin 2) (expected : Bool) (long : 2 ≤ inputs.length)
    (runtime : ∀ i ∈ inputs, i.Runtime) (stable : ∀ i ∈ inputs, i.rawInputs[channel.val] = expected) :
    (run p s inputs).samplerSecond[channel.val] = expected := by
  cases inputs with
  | nil => simp at long
  | cons first rest =>
    cases rest with
    | nil => simp at long
    | cons second rest =>
      have firstSamples := step_samples p s first (runtime first (by simp))
      have secondSamples := step_samples p (step p first s) second (runtime second (by simp))
      exact (stable_samples_run p (step p second (step p first s)) rest channel expected
        (by rw [secondSamples.1]; exact stable second (by simp))
        (by rw [secondSamples.2,firstSamples.1]; exact stable first (by simp))
        (fun i member => runtime i (by simp [member]))
        (fun i member => stable i (by simp [member]))).2

/-- A half-period of at least three leaves two LOW wait samples after reservation.
Peer stability is explicit; initial synchronizer contents are unrestricted. -/
theorem low_capture_stable (p : Program) (s : State a) (waits : List Input) (last : Input)
    (expected : Bool) (low : s.phase = .low) (stream : s.current.isStream = true)
    (receive : s.current.cell.receive = true) (long : 2 ≤ s.countdown.toNat)
    (runtime : ∀ i ∈ waits, i.Runtime) (lastRuntime : last.Runtime)
    (length : waits.length = s.countdown.toNat)
    (stable : ∀ i ∈ waits, i.rawInputs[s.current.cell.rxInput.val] = expected) :
    (run p s waits).captures = true ∧ (run p s waits).rxEvent = [expected] ∧
      (step p last (run p s waits)).phase = .high := by
  obtain ⟨stillLow,zero,_,current,high⟩ := low_interval p s waits last low runtime lastRuntime length
  have sampled := stable_sample_delay p s waits s.current.cell.rxInput expected (by omega) runtime stable
  have captures : (run p s waits).captures = true := by
    simp [State.captures,stillLow,zero,current,stream,receive]
  exact ⟨captures,by simp [State.rxEvent,captures,current,sampled],high⟩

end Pinwheel.Program.Streaming
