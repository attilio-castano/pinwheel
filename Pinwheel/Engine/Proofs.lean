import Pinwheel.Engine.Step

namespace Pinwheel.Engine

/-- Execution composes at an exact clock boundary; the input history shifts with time. -/
theorem run_add (p : Program) (s : State) (incoming : Nat → Bool) (a b : Nat) :
    run p s incoming (a + b) =
      run p (run p s incoming a) (fun n => incoming (a + n)) b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [run, Nat.add_assoc, ih]

/-- Before an action's boundary, only the finite timer changes. -/
theorem countdown (p : Program) (pc : Fin 32) (remaining : Fin 256)
    (levels : Levels) (slots : Samples) (incoming : Nat → Bool) (n : Nat)
    (h : n ≤ remaining.val) :
    run p ⟨.active pc remaining, levels, slots⟩ incoming n =
      ⟨.active pc ⟨remaining.val - n, by omega⟩, levels, slots⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, ih (by omega)]
    simp [advance, show 0 < remaining.val - n by omega, Nat.sub_sub]

/-- The next instruction enters exactly after the current action's duration. -/
theorem action_boundary (p : Program) (pc : Fin 32) (a : Action) (slots : Samples)
    (incoming : Nat → Bool) (h : p.fetch pc = .action a) :
    run p (enter p pc slots (incoming 0)) incoming a.duration =
      next p pc (capture slots a.capture (incoming 0)) (incoming a.duration) := by
  simp only [enter, h, Action.duration, run]
  rw [countdown p pc a.durationMinusOne a.levels _ incoming _ (Nat.le_refl _)]
  simp [advance]

theorem capture_slot (slots : Samples) (destination : Option (Fin 8)) (input : Bool)
    (slot : Fin 8) :
    (capture slots destination input)[slot.val] =
      if destination = some slot then input else slots[slot.val] := by
  simp [capture]

theorem reset_priority (p : Program) (s : State) (startRequested input : Bool) :
    step p s true startRequested input = reset p := rfl

theorem busy_ignores_start (p : Program) (s : State) (startRequested input : Bool)
    (h : busy s = true) : step p s false startRequested input = advance p s input := by
  simp [step, h]

theorem load_busy (m : Machine) (p : Program) (h : busy m.state = true) :
    load m p = (m, false) := by simp [load, h]

theorem load_stopped (m : Machine) (p : Program) (h : busy m.state = false) :
    load m p = (⟨p, reset p⟩, true) := by simp [load, h]

theorem halt_entry (p : Program) (pc : Fin 32) (slots : Samples) (input : Bool)
    (h : p.fetch pc = .halt) : enter p pc slots input = ⟨.stopped .completed, p.idle, slots⟩ := by
  simp [enter, h]

theorem exhausted_program (p : Program) (slots : Samples) (input : Bool) :
    next p 31 slots input = ⟨.stopped .fault, p.idle, slots⟩ := rfl

theorem stopped_retains (p : Program) (reason : Stop) (levels : Levels) (slots : Samples)
    (input : Bool) :
    advance p ⟨.stopped reason, levels, slots⟩ input = ⟨.stopped reason, levels, slots⟩ := rfl

theorem next_entry (p : Program) (pc : Fin 32) (slots : Samples) (input : Bool)
    (h : pc.val + 1 < 32) : next p pc slots input = enter p ⟨pc.val + 1, h⟩ slots input := by
  simp [next, h]

/-- Two adjacent actions occupy exactly the sum of their durations, even when different. -/
theorem two_action_boundary (p : Program) (pc : Fin 32) (a b : Action) (slots : Samples)
    (incoming : Nat → Bool) (hp : pc.val + 1 < 32)
    (ha : p.fetch pc = .action a) (hb : p.fetch ⟨pc.val + 1, hp⟩ = .action b) :
    run p (enter p pc slots (incoming 0)) incoming (a.duration + b.duration) =
      next p ⟨pc.val + 1, hp⟩
        (capture (capture slots a.capture (incoming 0)) b.capture (incoming a.duration))
        (incoming (a.duration + b.duration)) := by
  rw [run_add, action_boundary p pc a slots incoming ha, next_entry p pc _ _ hp]
  simpa only [Nat.add_zero] using
    action_boundary p ⟨pc.val + 1, hp⟩ b (capture slots a.capture (incoming 0))
      (fun n => incoming (a.duration + n)) hb

end Pinwheel.Engine
