import Pinwheel.Hardware.Reactive.SchedulerProofs

namespace Pinwheel.Hardware.Reactive

private theorem valid_encoded (op : Execution.Operation) : Execution.validValue (Execution.encode op) = true := by
  rw [Execution.valid_decode, Execution.decode_encode]
  rfl
  done

private theorem no_capture : Execution.getCapture (0#6) = none := rfl

theorem enter_encoded (p : Program) (address : BitVec 8) (slots : Samples) (i : Inputs)
    (hi : i.idle = p.idle) :
    enterValue (Execution.encode (p.fetch address.toFin)) address slots i =
      embed (Engine.Reactive.enter p address.toFin slots i.incoming) := by
  simp only [enterValue, valid_encoded, ↓reduceIte]
  cases h : p.fetch address.toFin with
  | checked a =>
    cases a with
    | mk action guard terminal finish =>
      cases finish <;> simp [Execution.encode, Execution.unpack_pack,
        Execution.fields, Execution.finishFields, Execution.actionFields, Execution.capture_roundtrip,
        Engine.Reactive.enter, h, embed]
  | _ => simp [Execution.encode, Execution.unpack_pack, Execution.fields,
      Execution.actionFields, no_capture, Execution.capture_roundtrip, Engine.Reactive.capture,
      Engine.Reactive.enter, Engine.Reactive.stop, h, embed, stopValue, stopMode, hi]
  done

theorem fed_entry (p : Program) (s : State) (reset start : Bool) (incoming : BitVec 2) :
    entryValue (feed p s reset start incoming) s =
      embed (Engine.Reactive.enter p (targetValue (feed p s reset start incoming) s).toFin
        (entryValues (feed p s reset start incoming) s) incoming) := by
  exact enter_encoded p _ _ _ rfl
  done

theorem successor_address (pc : Fin 256) (h : pc.val + 1 < 256) :
    BitVec.ofFin pc - 255#8 = BitVec.ofFin (⟨pc.val + 1, h⟩ : Fin 256) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega
  done

theorem dispatch_sequential (p : Program) (s : State) (reset start : Bool) (incoming : BitVec 2)
    (hb : runningValue s = true) (hm : s.mode ≠ 3#3) :
    dispatchValue (feed p s reset start incoming) s =
      embed (Engine.Reactive.next p s.pc.toFin s.samples incoming) := by
  simp only [dispatchValue, fed_entry]
  simp [rangeValue, sequentialValue, targetValue, entryValues, exitValues, feed, hb, hm]
  by_cases hp : s.pc.toNat < p.last.val
  · have bound : s.pc.toNat + 1 < 256 := by have := p.last.isLt; omega
    have hs : s.pc.toFin - 255 = (⟨s.pc.toNat + 1, bound⟩ : Fin 256) :=
      congrArg BitVec.toFin (successor_address s.pc.toFin bound)
    simp [Engine.Reactive.next, hp, hs]
  · simp [Engine.Reactive.next, hp, stopValue, Engine.Reactive.stop, embed, stopMode]
  done

theorem dispatch_checked (p : Program) (s : State) (reset start : Bool) (incoming : BitVec 2)
    (a : Engine.Reactive.Checked 255 15) (hm : s.mode = 3#3) (ha : p.fetch s.pc.toFin = .checked a) :
    dispatchValue (feed p s reset start incoming) s =
      embed (Engine.Reactive.dispatch p s.pc.toFin a.finish
        (Engine.Reactive.capture s.samples a.terminalCapture incoming) incoming) := by
  simp only [dispatchValue, fed_entry]
  cases hf : a.finish <;>
    simp [rangeValue, targetValue, sequentialValue, entryValues, exitValues, terminalValues,
      feed, runningValue, hm, ha, Execution.encode, Execution.unpack_pack, Execution.fields,
      Execution.finishFields, Execution.actionFields, hf, Execution.capture_roundtrip,
      Engine.Reactive.dispatch]
  all_goals simp only [stopValue]
  case sequential =>
    by_cases hp : s.pc.toNat < p.last.val
    · have bound : s.pc.toNat + 1 < 256 := by have := p.last.isLt; omega
      have hs : s.pc.toFin - 255 = (⟨s.pc.toNat + 1, bound⟩ : Fin 256) :=
        congrArg BitVec.toFin (successor_address s.pc.toFin bound)
      simp [Engine.Reactive.next, hp, hs]
    · simp [Engine.Reactive.next, hp, Engine.Reactive.stop, embed, stopMode]
  all_goals unfold Engine.Reactive.jump
  all_goals repeat' (first | rfl | (split <;> simp_all [Engine.Reactive.stop, embed, stopMode]))
  done

theorem predecessor_counter (n : Fin 256) (h : 0 < n.val) :
    BitVec.ofFin n - 1#8 = BitVec.ofFin (⟨n.val - 1, by omega⟩ : Fin 256) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega
  done

theorem advance_active (p : Program) (pc remaining : Fin 256) (pins : Engine.Reactive.Pins)
    (slots : Samples) (reset start : Bool) (incoming : BitVec 2) :
    let m : Model := ⟨.active pc remaining, pins, slots⟩
    advanceValue (feed p (embed m) reset start incoming) (embed m) =
      embed (Engine.Reactive.advance p m incoming) := by
  dsimp only
  have hd := dispatch_sequential p (embed ⟨.active pc remaining, pins, slots⟩) reset start incoming rfl (by simp [embed])
  simp only [advanceValue, hd]
  by_cases hr : 0 < remaining.val <;>
    simp [Engine.Reactive.advance, embed, decrementValue, predecessor_counter, hr, ← BitVec.toNat_inj, Nat.eq_zero_of_not_pos, Nat.ne_of_gt]
  done

theorem advance_checked (p : Program) (pc remaining : Fin 256) (pins : Engine.Reactive.Pins)
    (slots : Samples) (reset start : Bool) (incoming : BitVec 2) :
    let m : Model := ⟨.checked pc remaining, pins, slots⟩
    advanceValue (feed p (embed m) reset start incoming) (embed m) =
      embed (Engine.Reactive.advance p m incoming) := by
  dsimp only
  cases ha : p.fetch pc
  case checked a =>
    have hd := dispatch_checked p (embed ⟨.checked pc remaining, pins, slots⟩) reset start incoming a rfl ha
    simp only [advanceValue, hd]
    simp only [currentKindValue, feed, embed, ha, valid_encoded]
    cases hf : a.finish <;> cases hg : a.guard.ready incoming <;> by_cases hr : 0 < remaining.val <;>
      simp [Execution.encode, Execution.unpack_pack, Execution.fields, Execution.finishFields,
        Execution.actionFields, hf, guardValue, Execution.check_roundtrip, ha,
        Engine.Reactive.advance, hg, hr, Engine.Reactive.stop, stopValue, stopMode,
        decrementValue, predecessor_counter, ← BitVec.toNat_inj, Nat.eq_zero_of_not_pos, Nat.ne_of_gt]
    done
  all_goals simp [advanceValue, currentKindValue, feed, embed, ha, Engine.Reactive.advance,
    Execution.encode, Execution.unpack_pack, Execution.fields, Execution.actionFields,
    stopValue, Engine.Reactive.stop, stopMode]
  done

private theorem condition_parts : ∀ (input : Fin 2) (level : Bool),
    ((0#2 ++ BitVec.ofBool level ++ (BitVec.ofFin input : BitVec 1)).toNat % 2 = input.val) ∧
    ((0#2 ++ BitVec.ofBool level ++ (BitVec.ofFin input : BitVec 1))[1] = level) := by
  decide +kernel
  done

theorem advance_waiting (p : Program) (pc remaining : Fin 256) (pins : Engine.Reactive.Pins)
    (slots : Samples) (reset start : Bool) (incoming : BitVec 2) :
    let m : Model := ⟨.waiting pc remaining, pins, slots⟩
    advanceValue (feed p (embed m) reset start incoming) (embed m) =
      embed (Engine.Reactive.advance p m incoming) := by
  dsimp only
  have hd := dispatch_sequential p (embed ⟨.waiting pc remaining, pins, slots⟩) reset start incoming rfl (by simp [embed])
  cases ha : p.fetch pc
  all_goals simp only [advanceValue, hd]
  all_goals simp only [currentKindValue, feed, embed, ha, valid_encoded]
  case wait w =>
    cases hg : w.condition.ready incoming <;> by_cases hr : 0 < remaining.val <;>
      simp [ha, Engine.Reactive.advance, hg, hr, Execution.encode, Execution.unpack_pack,
        Execution.fields, readyValue, stopValue, Engine.Reactive.stop, stopMode, decrementValue,
        predecessor_counter, ← BitVec.toNat_inj, Nat.eq_zero_of_not_pos, Nat.ne_of_gt]
    all_goals simp_all [(condition_parts w.condition.input w.condition.level).1,
      (condition_parts w.condition.input w.condition.level).2, Engine.Reactive.Condition.ready]
    done
  case checked a =>
    cases hf : a.finish <;> simp [ha, Engine.Reactive.advance, Execution.encode,
      Execution.unpack_pack, Execution.fields, Execution.finishFields, Execution.actionFields,
      hf, stopValue, Engine.Reactive.stop, stopMode]
  all_goals simp [ha, Engine.Reactive.advance, Execution.encode,
    Execution.unpack_pack, Execution.fields, Execution.actionFields, stopValue,
    Engine.Reactive.stop, stopMode]
  done

theorem advance_qualifying (p : Program) (pc remaining waitLeft : Fin 256) (pins : Engine.Reactive.Pins)
    (slots : Samples) (reset start : Bool) (incoming : BitVec 2) :
    let m : Model := ⟨.qualifying pc remaining waitLeft, pins, slots⟩
    advanceValue (feed p (embed m) reset start incoming) (embed m) =
      embed (Engine.Reactive.advance p m incoming) := by
  dsimp only
  have hd := dispatch_sequential p (embed ⟨.qualifying pc remaining waitLeft, pins, slots⟩) reset start incoming rfl (by simp [embed])
  cases ha : p.fetch pc <;> simp only [advanceValue, hd]
  all_goals simp only [currentKindValue, feed, embed, ha, valid_encoded]
  case qualify q =>
    cases hg : q.condition.ready incoming <;> by_cases hr : 0 < remaining.val <;> by_cases hw : 0 < waitLeft.val <;>
      simp [ha, Engine.Reactive.advance, hg, hr, hw, Execution.encode, Execution.unpack_pack,
        Execution.fields, guardValue, Execution.check_roundtrip, stopValue, Engine.Reactive.stop,
        stopMode, progressValue, retryValue, predecessor_counter, ← BitVec.toNat_inj,
        Nat.eq_zero_of_not_pos, Nat.ne_of_gt]
  case checked a =>
    cases hf : a.finish <;> simp [ha, Engine.Reactive.advance, Execution.encode,
      Execution.unpack_pack, Execution.fields, Execution.finishFields, Execution.actionFields,
      hf, stopValue, Engine.Reactive.stop, stopMode]
  all_goals simp [ha, Engine.Reactive.advance, Execution.encode,
    Execution.unpack_pack, Execution.fields, Execution.actionFields, stopValue,
    Engine.Reactive.stop, stopMode]
  done

theorem running_embed (m : Model) : runningValue (embed m) = Engine.Reactive.busy m := by
  rcases m with ⟨control, pins, slots⟩
  cases control with
  | stopped reason => cases reason <;> rfl
  | _ => rfl
  done

theorem step_refines (p : Program) (m : Model) (reset start : Bool) (incoming : BitVec 2) :
    stepValue (feed p (embed m) reset start incoming) (embed m) =
      embed (Engine.Reactive.step p m reset start incoming) := by
  simp only [stepValue, running_embed, fed_entry, Engine.Reactive.step]
  rcases m with ⟨control, pins, slots⟩
  cases control <;> simp only [Engine.Reactive.busy, advance_active, advance_waiting,
    advance_checked, advance_qualifying]
  case stopped reason =>
    cases reason <;> cases reset <;> cases start <;>
      simp [feed, targetValue, entryValues, runningValue, embed, stopMode,
        stopValue, Engine.Reactive.reset, Engine.Reactive.stop, Engine.Reactive.start]
  all_goals cases reset <;> simp [feed, stopValue, Engine.Reactive.reset, Engine.Reactive.stop, embed, stopMode]
  done

/-- Structural clock edge equals the architectural edge, including reset/start priority. -/
theorem tick_refines (p : Program) (m : Model) (reset start : Bool) (incoming : BitVec 2) :
    tick (feed p (embed m) reset start incoming) (embed m) =
      embed (Engine.Reactive.step p m reset start incoming) := by
  rw [tick_correct, step_refines]
  done

structure Request where
  reset : Bool := false
  start : Bool := false
  incoming : BitVec 2 := 0
  deriving Repr

def run (p : Program) (s : State) : List Request → State
  | [] => s
  | i :: rest => run p (tick (feed p s i.reset i.start i.incoming) s) rest

def modelRun (p : Program) (m : Model) : List Request → Model
  | [] => m
  | i :: rest => modelRun p (Engine.Reactive.step p m i.reset i.start i.incoming) rest

/-- Arbitrarily long histories, arbitrary inputs, and arbitrary typed programs. -/
theorem run_refines (p : Program) (m : Model) (requests : List Request) :
    run p (embed m) requests = embed (modelRun p m requests) := by
  induction requests generalizing m with
  | nil => rfl
  | cons i rest ih => simp only [run, modelRun, tick_refines, ih]
  done

end Pinwheel.Hardware.Reactive
