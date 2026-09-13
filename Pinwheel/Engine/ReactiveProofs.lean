import Pinwheel.Engine.Reactive

namespace Pinwheel.Engine.Reactive

/-- A wait's readiness snapshot wins over timeout and enters the successor on this edge. -/
theorem wait_ready (p : Program) (pc : Fin 32) (w : Wait) (remaining : Fin 256)
    (pins : Pins) (slots : Samples) (inputs : Inputs)
    (hp : p.fetch pc = .wait w) (hi : w.condition.ready inputs = true) :
    advance p ⟨.waiting pc remaining, pins, slots⟩ inputs = next p pc slots inputs := by
  simp [advance, hp, hi]
  done

/-- Blocked observations preserve pin commands and all captured data. -/
theorem wait_countdown (p : Program) (pc : Fin 32) (w : Wait) (remaining : Fin 256)
    (pins : Pins) (slots : Samples) (incoming : Nat → Inputs) (n : Nat)
    (hp : p.fetch pc = .wait w) (hn : n ≤ remaining.val)
    (blocked : ∀ t, 0 < t → t ≤ n → w.condition.ready (incoming t) = false) :
    run p ⟨.waiting pc remaining, pins, slots⟩ incoming n =
      ⟨.waiting pc ⟨remaining.val - n, by omega⟩, pins, slots⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, ih (by omega) (fun t ht htn => blocked t ht (by omega))]
    simp [advance, hp, blocked (n + 1) (by omega) (by omega),
      show 0 < remaining.val - n by omega, Nat.sub_sub]
  done

/-- W consecutive blocked observations stop exactly on observation W. -/
theorem wait_timeout (p : Program) (pc : Fin 32) (w : Wait) (remaining : Fin 256)
    (pins : Pins) (slots : Samples) (incoming : Nat → Inputs)
    (hp : p.fetch pc = .wait w)
    (blocked : ∀ t, 0 < t → t ≤ remaining.val + 1 → w.condition.ready (incoming t) = false) :
    run p ⟨.waiting pc remaining, pins, slots⟩ incoming (remaining.val + 1) =
      stop p .timeout slots := by
  rw [run, wait_countdown p pc w remaining pins slots incoming remaining.val hp
    (Nat.le_refl _) (fun t ht hn => blocked t ht (by omega))]
  simp [advance, hp, blocked (remaining.val + 1) (by omega) (Nat.le_refl _)]
  done

theorem wait_boundary (p : Program) (pc : Fin 32) (w : Wait) (remaining : Fin 256)
    (pins : Pins) (slots : Samples) (incoming : Nat → Inputs) (n : Nat)
    (hp : p.fetch pc = .wait w) (hn : n ≤ remaining.val)
    (blocked : ∀ t, 0 < t → t ≤ n → w.condition.ready (incoming t) = false)
    (ready : w.condition.ready (incoming (n + 1)) = true) :
    run p ⟨.waiting pc remaining, pins, slots⟩ incoming (n + 1) =
      next p pc slots (incoming (n + 1)) := by
  rw [run, wait_countdown p pc w remaining pins slots incoming n hp hn blocked,
    wait_ready p pc w _ pins slots _ hp ready]
  done

theorem run_add (p : Program) (s : State) (incoming : Nat → Inputs) (a b : Nat) :
    run p s incoming (a + b) =
      run p (run p s incoming a) (fun n => incoming (a + n)) b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [run, Nat.add_assoc, ih]
  done

theorem countdown (p : Program) (pc : Fin 32) (remaining : Fin 256)
    (pins : Pins) (slots : Samples) (incoming : Nat → Inputs) (n : Nat)
    (h : n ≤ remaining.val) :
    run p ⟨.active pc remaining, pins, slots⟩ incoming n =
      ⟨.active pc ⟨remaining.val - n, by omega⟩, pins, slots⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, ih (by omega)]
    simp [advance, show 0 < remaining.val - n by omega, Nat.sub_sub]
  done

theorem action_boundary (p : Program) (pc : Fin 32) (a : Action) (slots : Samples)
    (incoming : Nat → Inputs) (h : p.fetch pc = .action a) :
    run p (enter p pc slots (incoming 0)) incoming a.duration =
      next p pc (capture slots a.capture (incoming 0)) (incoming a.duration) := by
  simp only [enter, h, Action.duration, run]
  rw [countdown p pc a.durationMinusOne a.pins _ incoming _ (Nat.le_refl _)]
  simp [advance]
  done

/-- A waited-for event anchors the following action's entire duration and capture edge. -/
theorem wait_then_timed (p : Program) (pc : Fin 32) (w : Wait) (a : Action)
    (remaining : Fin 256) (pins : Pins) (slots : Samples) (incoming : Nat → Inputs) (n : Nat)
    (hp : p.fetch pc = .wait w) (hn : n ≤ remaining.val)
    (succ : pc.val + 1 < 32) (ha : p.fetch ⟨pc.val + 1, succ⟩ = .action a)
    (blocked : ∀ t, 0 < t → t ≤ n → w.condition.ready (incoming t) = false)
    (ready : w.condition.ready (incoming (n + 1)) = true) :
    run p ⟨.waiting pc remaining, pins, slots⟩ incoming (n + 1 + a.duration) =
      next p ⟨pc.val + 1, succ⟩ (capture slots a.capture (incoming (n + 1)))
        (incoming (n + 1 + a.duration)) := by
  rw [run_add, wait_boundary p pc w remaining pins slots incoming n hp hn blocked ready]
  simpa only [next, succ, dite_true, Nat.add_zero] using
    action_boundary p ⟨pc.val + 1, succ⟩ a slots (fun t => incoming (n + 1 + t)) ha
  done

theorem wait_entry (p : Program) (pc : Fin 32) (w : Wait) (slots : Samples) (inputs : Inputs)
    (h : p.fetch pc = .wait w) :
    enter p pc slots inputs = ⟨.waiting pc w.budgetMinusOne, w.pins, slots⟩ := by
  simp [enter, h]
  done

theorem reset_priority (p : Program) (s : State) (startRequested : Bool) (inputs : Inputs) :
    step p s true startRequested inputs = reset p := rfl

theorem busy_ignores_start (p : Program) (s : State) (startRequested : Bool) (inputs : Inputs)
    (h : busy s = true) : step p s false startRequested inputs = advance p s inputs := by
  simp [step, h]
  done

theorem load_busy (m : Machine) (p : Program) (h : busy m.state = true) :
    load m p = (m, false) := by
  simp [load, h]
  done

theorem load_stopped (m : Machine) (p : Program) (h : busy m.state = false) :
    load m p = (⟨p, reset p⟩, true) := by
  simp [load, h]
  done

theorem stop_uses_idle (p : Program) (reason : Stop) (slots : Samples) :
    (stop p reason slots).pins = p.idle := rfl

theorem openDrain_never_high (pullLow : Levels) :
    (Pins.openDrain pullLow).enabled &&& (Pins.openDrain pullLow).levels = 0 := by
  simp [Pins.openDrain]
  done

end Pinwheel.Engine.Reactive
