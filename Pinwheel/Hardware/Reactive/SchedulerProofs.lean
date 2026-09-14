import Pinwheel.Hardware.Reactive.Equations

namespace Pinwheel.Hardware.Reactive

theorem current_correct (i : Inputs) (s : State) (p : Execution.Port w) :
    (current p).eval i.values s.values = Execution.value i.current p := by
  simp [current, Execution.logic_correct, Expr.eval, Inputs.values]
  done

theorem successor_correct (i : Inputs) (s : State) (p : Execution.Port w) :
    (successor p).eval i.values s.values = Execution.value i.successor p := by
  simp [successor, Execution.logic_correct, Expr.eval, Inputs.values]
  done

theorem running_correct (i : Inputs) (s : State) :
    running.eval i.values s.values = BitVec.ofBool (runningValue s) := by
  by_cases hm : s.mode = 0#3 <;> by_cases hl : s.mode.toNat < 5 <;>
    simp [running, Expr.eval, State.values, runningValue, hm, hl]
  exact ((bool_one _).mpr (bne_iff_ne.mpr hm)).symm
  done

theorem terminal_correct (i : Inputs) (s : State) (k : Fin 16) :
    (terminalSlots k).eval i.values s.values = BitVec.ofBool (terminalValues i s)[k.val] := by
  rw [terminalSlots, captureSlots_correct _ _ s.samples i s (fun _ => rfl)]
  simp [current_correct, Execution.value, Execution.fieldValue, terminalValues]
  done

theorem exit_correct (i : Inputs) (s : State) (k : Fin 16) :
    (exitSlots k).eval i.values s.values = BitVec.ofBool (exitValues i s)[k.val] := by
  by_cases h : s.mode = 3#3 <;>
    simp [exitSlots, Expr.eval, terminal_correct, oldSlots, isMode, State.values, exitValues, h]
  done

theorem entrySlots_correct (i : Inputs) (s : State) (k : Fin 16) :
    (entrySlots k).eval i.values s.values = BitVec.ofBool (entryValues i s)[k.val] := by
  cases h : runningValue s <;> simp [entrySlots, Expr.eval, running_correct, exit_correct, entryValues, h]
  done

private theorem sequential_bits (mode : BitVec 3) (finish : BitVec 2) :
    ~~~(~~~(~~~BitVec.ofBool (decide (mode = 3))) &&& ~~~BitVec.ofBool (decide (finish = 0))) =
      BitVec.ofBool (mode != 3 || finish == 0) := by
  revert mode finish
  decide +kernel
  done

theorem sequential_correct (i : Inputs) (s : State) :
    sequential.eval i.values s.values = BitVec.ofBool (sequentialValue i s) := by
  simp only [sequential, Execution.bor, Expr.eval, isMode, State.values, current_correct,
    Execution.value, Execution.fieldValue, sequentialValue]
  exact sequential_bits _ _
  done

theorem target_correct (i : Inputs) (s : State) : target.eval i.values s.values = targetValue i s := by
  simp only [target, Expr.eval, running_correct, sequential_correct, current_correct,
    Execution.readTree_correct, terminal_correct, Execution.value, Execution.fieldValue, State.values]
  simp [targetValue]
  done

theorem range_correct (i : Inputs) (s : State) :
    inRange.eval i.values s.values = BitVec.ofBool (rangeValue i s) := by
  cases h : sequentialValue i s <;>
    simp [inRange, Expr.eval, sequential_correct, target_correct, State.values, Inputs.values, rangeValue, h]
  rfl
  done

private theorem guard_bits (bits : BitVec 4) (incoming : BitVec 2) :
    BitVec.ofBool (decide ((incoming &&& bits.extractLsb' 0 2) =
      (bits.extractLsb' 2 2 &&& bits.extractLsb' 0 2))) =
      BitVec.ofBool ((Execution.getCheck bits).ready incoming) := by
  revert bits incoming
  decide +kernel
  done

theorem guard_correct (i : Inputs) (s : State) : guarded.eval i.values s.values = BitVec.ofBool (guardValue i) := by
  simp only [guarded, Expr.eval, current_correct, Execution.value, Execution.fieldValue, Inputs.values, guardValue]
  exact guard_bits _ _
  done

private theorem ready_bits (bits : BitVec 4) (incoming : BitVec 2) :
    BitVec.ofBool (decide (BitVec.ofBool (incoming.getLsbD (bits.extractLsb' 0 1).toNat) = bits.extractLsb' 1 1)) =
      BitVec.ofBool (incoming.getLsbD (bits.extractLsb' 0 1).toNat == bits[1]) := by
  revert bits incoming
  decide +kernel
  done

theorem ready_correct (i : Inputs) (s : State) : ready.eval i.values s.values = BitVec.ofBool (readyValue i) := by
  simp only [ready, Expr.eval, inputBit_correct, current_correct, Execution.value, Execution.fieldValue, readyValue]
  exact ready_bits _ _
  done

private theorem kind_bits (valid : Bool) (actual expected : BitVec 3) :
    (BitVec.ofBool valid &&& BitVec.ofBool (decide (actual = expected))) = BitVec.ofBool (valid && actual == expected) := by
  revert valid actual expected
  decide +kernel
  done

theorem kind_correct (kind : BitVec 3) (i : Inputs) (s : State) :
    (currentKind kind).eval i.values s.values = BitVec.ofBool (currentKindValue kind i) := by
  simp only [currentKind, Expr.eval, current_correct, Execution.value, Execution.fieldValue, currentKindValue]
  exact kind_bits _ _ _
  done

theorem stop_correct (mode : BitVec 3) (slots : Slots) (values : Samples) (i : Inputs) (s : State)
    (hs : ∀ k, (slots k).eval i.values s.values = BitVec.ofBool values[k.val]) (r : Register w) :
    (stop mode slots r).eval i.values s.values = (stopValue mode values i).values r := by
  cases r <;> simp [stop, stopValue, Expr.eval, State.values, Inputs.values, hs]
  done

theorem entry_correct (i : Inputs) (s : State) (r : Register w) :
    (entry r).eval i.values s.values = (entryValue i s).values r := by
  simp only [entry, Expr.eval, successor_correct, Execution.value, Execution.fieldValue,
    stop_correct _ _ _ i s (entrySlots_correct i s)]
  cases hv : Execution.validValue i.successor <;> by_cases hk : (Execution.unpack i.successor).kind = 4#3 <;>
    cases r <;> simp [enterRunning, Expr.eval, successor_correct, Execution.value, Execution.fieldValue,
      target_correct, captureSlots_correct _ _ _ i s (entrySlots_correct i s),
      entryValue, enterValue, State.values, hv, hk]
  done

theorem dispatch_correct (i : Inputs) (s : State) (r : Register w) :
    (dispatch r).eval i.values s.values = (dispatchValue i s).values r := by
  cases h : rangeValue i s <;>
    simp [dispatch, Expr.eval, range_correct, entry_correct,
      stop_correct _ _ _ i s (exit_correct i s), dispatchValue, h]
  done

theorem decrement_correct (i : Inputs) (s : State) (r : Register w) :
    (decrement r).eval i.values s.values = (decrementValue s).values r := by
  cases r <;> rfl
  done

theorem progress_correct (i : Inputs) (s : State) (r : Register w) :
    (qualifiedProgress r).eval i.values s.values = (progressValue i s).values r := by
  cases r <;> simp [qualifiedProgress, progressValue, Expr.eval, State.values,
    current_correct, Execution.value, Execution.fieldValue]
  done

theorem retry_correct (i : Inputs) (s : State) (r : Register w) :
    (qualificationRetry r).eval i.values s.values = (retryValue i s).values r := by
  cases r <;> simp [qualificationRetry, retryValue, Expr.eval, State.values,
    current_correct, Execution.value, Execution.fieldValue]
  done

-- Unfolding Expr.eval also changes the propositions inside its Decidable instances.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem advance_correct (i : Inputs) (s : State) (r : Register w) :
    (advance r).eval i.values s.values = (advanceValue i s).values r := by
  cases r <;> simp only [advance, Expr.eval, isMode, State.values, kind_correct, guard_correct, ready_correct,
    dispatch_correct, decrement_correct, progress_correct, retry_correct,
    stop_correct _ oldSlots s.samples i s (fun _ => rfl)]
  all_goals simp only [BitVec.ofBool_and_ofBool, bool_one]
  all_goals unfold advanceValue
  all_goals repeat' (first | rfl | (split <;> try simp_all))
  done

theorem next_correct (i : Inputs) (s : State) (r : Register w) :
    (circuit.next r).eval i.values s.values = (stepValue i s).values r := by
  simp only [circuit, Expr.eval, running_correct, advance_correct, entry_correct,
    stop_correct _ zeroSlots (Vector.replicate 16 false) i s (fun _ => by simp [zeroSlots, Expr.eval])]
  cases hr : i.reset <;> cases hs : i.start <;> cases hb : runningValue s <;>
    simp [stepValue, hold, Expr.eval, Inputs.values, hr, hs, hb]
  done

theorem tick_correct (i : Inputs) (s : State) : tick i s = stepValue i s := by
  have h : (fun (w : Nat) (r : Register w) => circuit.step i.values s.values r) =
      (fun (w : Nat) (r : Register w) => (stepValue i s).values r) :=
    funext (fun _ => funext (fun r => next_correct i s r))
  exact (congrArg (fun (f : (w : Nat) → Register w → BitVec w) => fromValues (fun {w} => f w)) h).trans
    (from_values (stepValue i s))
  done

end Pinwheel.Hardware.Reactive
