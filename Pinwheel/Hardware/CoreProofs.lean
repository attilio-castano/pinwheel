import Pinwheel.Hardware.Core

namespace Pinwheel.Hardware.Core

@[simp] theorem slot_eq (bits : BitVec 3) (slot : Fin 8) :
    bits = BitVec.ofFin slot ↔ bits.toFin = slot := by
  cases bits <;> simp

@[simp] theorem one_and_bool (b : Bool) : 1#1 &&& BitVec.ofBool b = BitVec.ofBool b := by
  cases b <;> rfl

theorem enterFields_correct (d : {w : Nat} → Decode.Port w → E w) (fields : Decode.Fields)
    (address : E 5) (clear : Bool) (i : Inputs) (s : State)
    (hd : ∀ {w} (p : Decode.Port w), (d p).eval i.values s.values = fields.values p)
    (r : Register w) :
    (enterFields d address clear r).eval i.values s.values =
      (enterValue fields (address.eval i.values s.values) clear i s).values r := by
  cases r <;> simp only [enterFields, Expr.eval, hd]
  all_goals by_cases ha : fields.kind = 1 <;> by_cases hh : fields.kind = 2 <;>
    simp_all [enterValue, Decode.Fields.instruction, Decode.Fields.values, stoppedValue, State.values,
      Inputs.values, Engine.capture]
  all_goals cases clear <;> simp [Expr.eval, State.values]
  all_goals split <;> simp_all
  cases h : fields.capture <;> simp_all
  done

theorem entry_correct (address : E 5) (clear : Bool) (i : Inputs) (s : State) (r : Register w) :
    (entry address clear r).eval i.values s.values =
      (entryValue (address.eval i.values s.values) clear i s).values r := by
  change (enterFields (Decode.logic (Store.read (fun k => .reg (.word k)) address)) address clear r).eval _ _ = _
  rw [enterFields_correct _ _ _ _ _ _ (Decode.logic_values_correct _ i.values s.values)]
  rw [Store.read_correct]
  rfl

theorem stopped_correct (reason : BitVec 2) (clear : Bool) (i : Inputs) (s : State) (r : Register w) :
    (stopped reason clear r).eval i.values s.values = (stoppedValue reason clear s).values r := by
  cases r <;> cases clear <;> simp [stopped, stoppedValue, Expr.eval, State.values]

theorem cold_correct (i : Inputs) (s : State) (r : Register w) :
    (cold r).eval i.values s.values = (coldValue s).values r := by
  cases r <;> simp [cold, coldValue, stoppedValue, Expr.eval, State.values]

theorem committed_correct (i : Inputs) (s : State) (r : Register w) :
    (committed r).eval i.values s.values = (commitValue i s).values r := by
  cases r <;> simp [committed, commitValue, stoppedValue, Expr.eval, State.values, Inputs.values]

theorem decrement_correct (i : Inputs) (s : State) (r : Register w) :
    (decrement r).eval i.values s.values = ({s with timer := Countdown.tick {} s.timer}).values r := by
  cases r <;> simp [decrement, Expr.eval_bind, timerRegisters, Expr.eval, State.values,
    Countdown.tick, Countdown.circuit, Circuit.step, Countdown.progressing, Countdown.nonzero,
    Countdown.Inputs.values, Countdown.State.values]
  all_goals rfl
  done

theorem advance_correct (i : Inputs) (s : State) (r : Register w) :
    (advance r).eval i.values s.values = (advanceValue i s).values r := by
  simp only [advance, Expr.eval, stopped_correct, entry_correct, decrement_correct]
  by_cases hz : s.timer.remaining = 0#8 <;> by_cases hp : s.pc = 31#5 <;>
    simp [State.values, advanceValue, hz, hp]
  done

theorem next_correct (i : Inputs) (s : State) (r : Register w) :
    (next r).eval i.values s.values = (stepValue i s).values r := by
  simp only [next, Expr.eval, cold_correct, stopped_correct, advance_correct, committed_correct, entry_correct]
  cases hi : i.init <;> cases hr : i.reset <;> cases hv : s.valid <;>
    cases hc : i.commit <;> cases hs : i.start <;> by_cases hb : s.status = 1#2 <;>
    simp [Inputs.values, State.values, hold, Expr.eval, stepValue, hi, hr, hv, hc, hs, hb]
  done

theorem tick_eq_stepValue (i : Inputs) (s : State) : tick i s = stepValue i s := by
  have h : (fun (w : Nat) (r : Register w) => circuit.step i.values s.values r) =
      (fun (w : Nat) (r : Register w) => (stepValue i s).values r) :=
    funext (fun _ => funext (fun r => next_correct i s r))
  change fromValues (circuit.step i.values s.values) = stepValue i s
  have hh := congrArg (fun (f : (w : Nat) → Register w → BitVec w) => fromValues (fun {w} => f w)) h
  exact hh.trans (from_values (stepValue i s))
  done

end Pinwheel.Hardware.Core
