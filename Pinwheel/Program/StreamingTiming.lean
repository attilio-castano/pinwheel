import Pinwheel.Program.StreamingService

namespace Pinwheel.Program.Streaming

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
  rw [(step_high_terminal p (run p s inputs) last lastRuntime stillHigh zero).1]
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

end Pinwheel.Program.Streaming
