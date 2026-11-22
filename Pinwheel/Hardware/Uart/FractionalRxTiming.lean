import Pinwheel.Hardware.Uart.FractionalRx
import Pinwheel.UART.FractionalTiming

namespace Pinwheel.Hardware.Uart.FractionalRx.Sampler
open Pinwheel.Hardware.Timebase
open Pinwheel.UART.FractionalTiming

/-- The physical phase and half-beat count at elapsed edge `n`. -/
structure Aligned (p : Period) (n : Nat) (s : Values (Register w)) : Prop where
  numerator : (s numReg).toNat = p.numerator
  denominator : (s denReg).toNat = p.denominator
  phase : (s phaseReg).toNat = (run p n).phase
  count : (s countReg).toNat = (run p n).beats

theorem toBool_beat (p : Period) (i : Values (Input w)) (s : Values (Register w))
    (position : Aligned p n s) (active : s activeReg = 1#1) :
    beat.eval i s = BitVec.ofBool (Timebase.beat p (run p n).phase) := by
  have bounded : (s phaseReg).toNat < p.numerator := position.phase ▸ (run_conserves p n).1
  have event := (expressions_correct p (.reg phaseReg) (.reg numReg) (.reg denReg)
    i s position.numerator position.denominator bounded).1
  cases fire : Timebase.beat p (run p n).phase <;>
    simp [beat, Expr.eval, active, event, position.phase, fire]
  done

/-- An admitted START establishes the origin and latches the rate. -/
theorem aligned_start (p : Period) (i : Values (Input w)) (s : Values (Register w))
    (numerator_eq : (i numerator).toNat = p.numerator)
    (denominator_eq : (i denominator).toNat = p.denominator)
    (unreset : i reset ≠ 1#1) (inactive : s activeReg = 0#1)
    (admitted : detect.eval i s = 1#1) : Aligned p 0 ((circuit w).step i s) := by
  have zero : i reset = 0#1 := (BitVec.eq_zero_or_eq_one _).resolve_right unreset
  constructor
  · simpa [Circuit.step, circuit, Expr.eval, numReg, unreset, admitted] using numerator_eq
  · simpa [Circuit.step, circuit, Expr.eval, denReg, unreset, admitted] using denominator_eq
  · simp [Circuit.step, circuit, Expr.eval, phaseReg, zero, inactive, run]
    rfl
  · simp [Circuit.step, circuit, Expr.eval, countReg, zero, inactive, run]
  done

/-- Active edges preserve the timing relation, including the edge that takes
the final sample. START cannot change the latched period while active. -/
theorem aligned_step (p : Period) (i : Values (Input w)) (s : Values (Register w))
    (position : Aligned p n s) (unreset : i reset ≠ 1#1)
    (active : s activeReg = 1#1) (beforeWrap : (run p n).beats < 31) :
    Aligned p (n + 1) ((circuit w).step i s) := by
  have blocked : detect.eval i s = 0 := by simp [detect, Expr.eval, active]
  have event := toBool_beat p i s position active
  have bounded : (s phaseReg).toNat < p.numerator := position.phase ▸ (run_conserves p n).1
  have tickPhase := (expressions_correct p (.reg phaseReg) (.reg numReg) (.reg denReg)
    i s position.numerator position.denominator bounded).2
  constructor
  · simpa [Circuit.step, circuit, Expr.eval, numReg, unreset, blocked] using position.numerator
  · simpa [Circuit.step, circuit, Expr.eval, denReg, unreset, blocked] using position.denominator
  · have nextPhase := tickPhase.trans (congrArg (advance p) position.phase)
    simpa [Circuit.step, circuit, Expr.eval, phaseReg, active, unreset, run] using nextPhase
  · have index : (s (.at ⟨2, by simp⟩)).toNat = (run p n).beats := position.count
    cases fire : Timebase.beat p (run p n).phase
    · simpa [Circuit.step, circuit, Expr.eval, countReg, unreset, active, event, fire, run] using index
    · simp [Circuit.step, circuit, Expr.eval, countReg, unreset, active, event, fire, run, BitVec.toNat_add]
      change ((s countReg).toNat + 1) % 32 = _
      rw [position.count, Nat.mod_eq_of_lt (by omega)]
  done

theorem sample_when_center (p : Period) (i : Values (Input w)) (s : Values (Register w))
    (position : Aligned p n s) (active : s activeReg = 1#1)
    (count : (run p n).beats = 2 * symbol) :
    sample.eval i s = BitVec.ofBool (Timebase.beat p (run p n).phase) := by
  have even : (s countReg).extractLsb' 0 1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, position.count, count]
  have event := toBool_beat p i s position active
  cases fire : Timebase.beat p (run p n).phase <;>
    simp [sample, Expr.eval, even, event, fire]
  done

/-- A physical center sample lies inside the transmitter's corresponding
symbol window, provided the digital detection and baud bounds are met. -/
theorem physical_sample_window (p : Period) (i : Values (Input w)) (s : Values (Register w))
    (position : Aligned p n s) (active : s activeReg = 1#1)
    (symbol : Fin 10) (count : (run p n).beats = 2 * symbol.val)
    (sampled : sample.eval i s = 1#1) (safe : Safe p senderBit late) (delay : lag ≤ late) :
    symbol.val * senderBit ≤ lag + p.denominator * (n + 1) ∧
      lag + p.denominator * (n + 1) < (symbol.val + 1) * senderBit := by
  have tick := sample_when_center p i s position active count
  have fired : Timebase.beat p (run p n).phase = true := by
    cases h : Timebase.beat p (run p n).phase <;> simp [h, sampled] at tick ⊢
  rw [sample_at_beat p n symbol.val count fired]
  exact sample_window p senderBit late lag safe delay symbol

theorem active_start (i : Values (Input w)) (s : Values (Register w))
    (unreset : i reset ≠ 1#1) (inactive : s activeReg = 0#1)
    (admitted : detect.eval i s = 1#1) :
    (circuit w).step i s activeReg = 1#1 := by
  have stopped : beat.eval i s = 0 := by simp [beat, Expr.eval, inactive]
  simp [Circuit.step, circuit, Expr.eval, activeReg, unreset, complete, abort, sample,
    stopped, admitted]
  change 1#1 ||| s activeReg = 1#1
  rw [inactive]
  rfl
  done

private theorem beat_of_sample (p : Period) (i : Values (Input w)) (s : Values (Register w))
    (position : Aligned p n s) (active : s activeReg = 1#1) (sampled : sample.eval i s = 1#1) :
    Timebase.beat p (run p n).phase = true := by
  have physical := toBool_beat p i s position active
  cases fire : Timebase.beat p (run p n).phase <;>
    simp [sample, Expr.eval, physical, fire] at sampled ⊢
  done

theorem stays_active (p : Period) (i : Values (Input w)) (s : Values (Register w))
    (position : Aligned p n s) (active : s activeReg = 1#1) (unreset : i reset ≠ 1#1)
    (beforeStop : n + 1 < sampleEdge p 9)
    (goodStart : n + 1 = sampleEdge p 0 → i line = 0#1) :
    (circuit w).step i s activeReg = 1#1 := by
  have blocked : detect.eval i s = 0 := by simp [detect, Expr.eval, active]
  by_cases sampled : sample.eval i s = 1#1
  · have fired := beat_of_sample p i s position active sampled
    have notStop : s countReg ≠ 18#5 := by
      intro index
      have count : (run p n).beats = 2 * 9 := by rw [← position.count, index]; rfl
      have tooLate := sample_at_beat p n 9 count fired
      omega
    have noAbort : abort.eval i s = 0 := by
      by_cases first : s countReg = 0#5
      · have count : (run p n).beats = 2 * 0 := by rw [← position.count, first]; rfl
        have low := goodStart (sample_at_beat p n 0 count fired)
        simp [abort, Expr.eval, sampled, low]
      · simp [abort, Expr.eval, sampled, startCenter, first]
    simp [Circuit.step, circuit, Expr.eval, activeReg, unreset, complete, stopCenter,
      sampled, notStop, noAbort, blocked]
    exact active
  · have quiet := (BitVec.eq_zero_or_eq_one _).resolve_right sampled
    simp [Circuit.step, circuit, Expr.eval, activeReg, unreset, complete, abort,
      quiet, blocked]
    exact active
  done

def runEdges (inputs : Nat → Values (Input w)) (initial : Values (Register w)) :
    Nat → Values (Register w)
  | 0 => initial
  | n + 1 => (circuit w).step (inputs (n + 1)) (runEdges inputs initial n)

/-- From an admitted start, the physical sampler stays aligned and armed
through every edge before the stop center, provided START validates. Inputs
are indexed by the core edge after detection, with the first edge at one. -/
theorem aligned_prefix (p : Period) (inputs : Nat → Values (Input w))
    (initial : Values (Register w)) (aligned : Aligned p 0 initial)
    (active : initial activeReg = 1#1) (unreset : ∀ k, inputs k reset ≠ 1#1)
    (goodStart : inputs (sampleEdge p 0) line = 0#1) (n : Nat) (before : n < sampleEdge p 9) :
    Aligned p n (runEdges inputs initial n) ∧ (runEdges inputs initial n) activeReg = 1#1 := by
  induction n with
  | zero => exact ⟨aligned, active⟩
  | succ n ih =>
    obtain ⟨alignedNow, activeNow⟩ := ih (by omega)
    have guard : (run p n).beats < 31 := by
      have unreached : ¬19 ≤ (run p n).beats := fun h =>
        Nat.not_le_of_gt before (Nat.le_trans ((reaches_center p n 9).mp h) (Nat.le_succ n))
      omega
    exact ⟨aligned_step p _ _ alignedNow (unreset _) activeNow guard,
      stays_active p _ _ alignedNow activeNow (unreset _) before (fun eq => by simpa [eq] using goodStart)⟩

/-- Every designated center is sampled by the actual circuit once the prefix
has remained aligned. This includes the stop center on the closing edge. -/
theorem sample_at_center (p : Period) (i : Values (Input w)) (s : Values (Register w))
    (position : Aligned p n s) (active : s activeReg = 1#1)
    (edge : n + 1 = sampleEdge p symbol) :
    sample.eval i s = 1#1 := by
  obtain ⟨count, fired⟩ := at_center p n symbol edge
  simp [sample_when_center p i s position active count, fired]

/-- Each scheduled center of the active circuit is a sample and lies inside
its sender symbol. The stop sample is strictly before the next frame start
even if the sender uses zero extra idle time. -/
theorem frame_centers (p : Period) (inputs : Nat → Values (Input w))
    (initial : Values (Register w)) (aligned : Aligned p 0 initial)
    (active : initial activeReg = 1#1) (unreset : ∀ k, inputs k reset ≠ 1#1)
    (goodStart : inputs (sampleEdge p 0) line = 0#1)
    (symbol : Fin 10) (n : Nat) (edge : n + 1 = sampleEdge p symbol.val)
    (safe : Safe p senderBit late) (delay : lag ≤ late) :
    sample.eval (inputs (n + 1)) (runEdges inputs initial n) = 1#1 ∧
    symbol.val * senderBit ≤ lag + p.denominator * (n + 1) ∧
      lag + p.denominator * (n + 1) < (symbol.val + 1) * senderBit := by
  have last := (reaches_center p (sampleEdge p 9) 9).2 (Nat.le_refl _)
  have ordered : sampleEdge p symbol.val ≤ sampleEdge p 9 :=
    (reaches_center p (sampleEdge p 9) symbol.val).1 (by have := symbol.isLt; omega)
  obtain ⟨position, running⟩ :=
    aligned_prefix p inputs initial aligned active unreset goodStart n (by omega)
  have sampled := sample_at_center p (inputs (n + 1)) _ position running edge
  exact ⟨sampled, physical_sample_window p _ _ position running symbol
    (at_center p n symbol.val edge).1 sampled safe delay⟩

/-- A valid STOP both posts an arrival and leaves the sampler idle with the
previous line high. Thus a falling START can be accepted on the next edge. -/
theorem stop_rearms (p : Period) (i : Values (Input w)) (s : Values (Register w))
    (position : Aligned p n s) (active : s activeReg = 1#1) (unreset : i reset ≠ 1#1)
    (edge : n + 1 = sampleEdge p 9) (high : i line = 1#1) :
    (circuit w).observe i s (.at 3) = 1#1 ∧
      (circuit w).step i s activeReg = 0#1 ∧ (circuit w).step i s prevReg = 1#1 := by
  have sampled := sample_at_center p i s position active edge
  have index : s countReg = 18#5 := BitVec.eq_of_toNat_eq
    (position.count.trans (at_center p n 9 edge).1)
  have arrival : complete.eval i s = 1#1 := by
    simp [complete, stopCenter, Expr.eval, sampled, index]
  have noAbort : abort.eval i s = 0#1 := by
    simp [abort, startCenter, Expr.eval, index]
  refine ⟨?_, ?_, ?_⟩
  · simp [Circuit.observe, circuit, Expr.eval, unreset, arrival]
  · simp [Circuit.step, circuit, Expr.eval, activeReg, unreset, arrival, noAbort]
  · simp [Circuit.step, circuit, Expr.eval, prevReg, unreset, high]

end Pinwheel.Hardware.Uart.FractionalRx.Sampler

namespace Pinwheel.Hardware.Uart.FractionalRx

def samplerState (s : Values (Register w)) : Values (Sampler.Register w) :=
  fun r => s (sampleReg r)

def samplerDrive (i : Values (Input w)) (s : Values (Register w)) : Values (Sampler.Input w) :=
  fun p => (flatPin samplePin (samplerInput p)).eval i s

theorem sampler_step (i : Values (Input w)) (s : Values (Register w)) (r : Sampler.Register w b) :
    (circuit w).step i s (sampleReg r) = (Sampler.circuit w).step (samplerDrive i s) (samplerState s) r := by
  simp only [Circuit.step, circuit, sampleReg, samplerExpr, Expr.eval_bind, Expr.eval]
  rfl
  done

theorem sampler_observe (i : Values (Input w)) (s : Values (Register w)) (unreset : i (.at 0) ≠ 1#1) :
    (circuit w).observe i s (.at 5) = Sampler.sample.eval (samplerDrive i s) (samplerState s) := by
  have noReset : samplerDrive i s Sampler.reset ≠ 1#1 := unreset
  simp only [Circuit.observe, circuit, samplerExpr, Expr.eval_bind, Expr.eval]
  change (if samplerDrive i s Sampler.reset = 1#1 then 0 else _) = _
  rw [if_neg noReset]
  rfl
  done

end Pinwheel.Hardware.Uart.FractionalRx
