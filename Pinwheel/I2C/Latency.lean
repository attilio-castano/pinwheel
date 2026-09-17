import Pinwheel.Latency
import Pinwheel.I2C.Proofs
import Pinwheel.I2C.RegisterRead

/-! The I2C write controller behind an input pipeline. Unlike UART and SPI, this
controller checks the bus right after changing its own drive, so a delayed view
shows it its own earlier command. The consequences are proved here for every
target. The first led to a revision of `step` itself: bus-free time after STOP is
now qualified, as it already was before START. -/
namespace Pinwheel.I2C

/-- While it prepares and holds STOP the controller itself keeps SDA low. -/
theorem stop_holds_data_low (s : State) (target : Pins)
    (h : s.phase = .stopLow ∨ s.phase = .stopRise ∨ s.phase = .stopHigh) :
    (resolve (pins s) target).sda = false := by
  rcases h with h | h | h <;> simp [pins, h, resolve, resolveLine]

/-- While it holds the clock low the controller itself keeps SCL low. -/
theorem low_phases_hold_clock_low (s : State) (target : Pins)
    (h : s.phase = .setup ∨ s.phase = .fall ∨ s.phase = .stopLow) :
    (resolve (pins s) target).scl = false := by
  rcases h with h | h | h <;> simp [pins, h, resolve, resolveLine]

/-- The bus-free transition specified before input latency was considered: any
observation without both lines high is a bus fault. Kept to record the hazard. -/
def guardedStopFree (s : State) (bus : Bus) : State :=
  if !(bus.scl && bus.sda) then finish s .busFault
  else if s.remaining.val == 0 then finish s s.outcome else count s

/-- **Echo hazard of the guarded transition.** An observation that is still from
the controller's own STOP preparation shows SDA low, whatever the target does, so
the guarded transition reports a bus fault. Behind `d ≥ 1` input registers the
first observation consumed in `stopFree` is such an observation. -/
theorem guarded_stop_echo_faults (s earlier : State) (target : Pins)
    (stale : earlier.phase = .stopLow ∨ earlier.phase = .stopRise ∨ earlier.phase = .stopHigh) :
    result (guardedStopFree s (resolve (pins earlier) target)) = some .busFault := by
  have low := stop_holds_data_low earlier target stale
  simp [guardedStopFree, low, finish, result, busy]

/-- **The qualified transition waits the echo out.** `step` now treats bus-free
time after STOP as it treats it before START: a blocked observation restarts the
interval and spends wait budget. -/
theorem stop_echo_is_waited_out (cfg : Config) (s earlier : State) (target : Pins)
    (now : s.phase = .stopFree)
    (stale : earlier.phase = .stopLow ∨ earlier.phase = .stopRise ∨ earlier.phase = .stopHigh) :
    step cfg s (resolve (pins earlier) target) = blocked cfg s := by
  have low := stop_holds_data_low earlier target stale
  simp [step, now, low]

/-- A full bus-free interval still completes with the transaction's outcome. -/
theorem stop_completes (cfg : Config) (s : State) (now : s.phase = .stopFree)
    (last : s.remaining.val = 0) : result (step cfg s ⟨true, true⟩) = some s.outcome := by
  simp [step, now, last, finish, result, busy]

/-- **Wait-budget hazard.** After releasing SCL the controller counts every
observation in which SCL still reads low as blocking. Observations from its own
clock-low phases are of that kind, so each clock rise spends one unit of the wait
budget per register of input latency before any target stretches at all; so does
the bus-free interval after STOP (`stop_echo_is_waited_out`). -/
theorem stale_clock_observation_blocks (cfg : Config) (s earlier : State) (target : Pins)
    (now : s.phase = .rise ∨ s.phase = .stopRise)
    (stale : earlier.phase = .setup ∨ earlier.phase = .fall ∨ earlier.phase = .stopLow) :
    step cfg s (resolve (pins earlier) target) = blocked cfg s := by
  have low := low_phases_hold_clock_low earlier target stale
  rcases now with now | now <;> simp [step, now, low]

/-- **Premature-high hazard.** If the latency exceeds the time the controller held
SCL low, the first observation consumed in `rise` predates that low phase and
reads high, so the high timer starts at once (`released_clock_starts_timer`).
The controller's own low phase then arrives as an observation in `high`, where a
low clock is a bus fault. The clock-low time must therefore cover the latency. -/
theorem stale_low_in_high_faults (cfg : Config) (s earlier : State) (target : Pins)
    (now : s.phase = .high ∨ s.phase = .stopHigh ∨ s.phase = .startHold)
    (stale : earlier.phase = .setup ∨ earlier.phase = .fall ∨ earlier.phase = .stopLow) :
    result (step cfg s (resolve (pins earlier) target)) = some .busFault := by
  have low := low_phases_hold_clock_low earlier target stale
  rcases now with now | now | now <;> simp [step, now, low, finish, result, busy]

/-- With a wait budget no larger than the latency, the first clock rise times out
on the controller's own echo: `waitLeft + 1` stale observations suffice. -/
theorem echo_exhausts_wait (cfg : Config) (s : State) (sda : Nat → Bool)
    (rising : s.phase = .rise) (fresh : s.remaining = cfg.phaseMinusOne) :
    result (run cfg s (fun t => ⟨false, sda t⟩) (s.waitLeft.val + 1)) = some .timeout :=
  stretch_timeout_exact cfg s sda rising fresh

/-! Multi-step closed forms: what the wait budget buys behind the pipeline. -/

/-- Runs compose: the later part sees the history shifted by the earlier part's length. -/
theorem run_add (cfg : Config) (s : State) (incoming : Nat → Bus) (a b : Nat) :
    run cfg s incoming (a + b) = run cfg (run cfg s incoming a) (fun t => incoming (a + t)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show step cfg (run cfg s incoming (a + b)) (incoming (a + b + 1)) = _
    rw [ih]
    rfl

/-- Observations that block a fresh waiting phase change nothing but the budget, as long as
the budget covers them. `stale_clock_observation_blocks` and `stop_echo_is_waited_out`
show that the controller's own echo is such an observation. -/
theorem blocked_prefix (cfg : Config) (s : State) (incoming : Nat → Bus) (n : Nat)
    (ht : s.remaining = cfg.phaseMinusOne) (hn : n ≤ s.waitLeft.val)
    (blocks : ∀ (u : State) (t : Nat), u.phase = s.phase → 1 ≤ t → t ≤ n →
      step cfg u (incoming t) = blocked cfg u) :
    run cfg s incoming n =
      {s with remaining := cfg.phaseMinusOne, waitLeft := ⟨s.waitLeft.val - n, by omega⟩} := by
  induction n with
  | zero => simp [run, ← ht]
  | succ n ih =>
    rw [run, ih (by omega) (fun u t hu h1 h2 => blocks u t hu h1 (by omega)),
      blocks {s with remaining := cfg.phaseMinusOne, waitLeft := ⟨s.waitLeft.val - n, by omega⟩}
        (n + 1) rfl (by omega) (Nat.le_refl _)]
    simp [blocked, show 0 < s.waitLeft.val - n by omega, Nat.sub_sub]

/-- **A clock rise behind an input pipeline.** `d` observations that still show the clock
low — the controller's own echo behind `d` input registers, a stretching target, or both —
are waited out when the budget covers them; the first high observation then starts a full
high period. Without the budget the same prefix is `echo_exhausts_wait`. -/
theorem rise_behind_pipeline (cfg : Config) (s : State) (incoming : Nat → Bus) (d : Nat)
    (hp : s.phase = .rise) (ht : s.remaining = cfg.phaseMinusOne) (hd : d ≤ s.waitLeft.val)
    (echo : ∀ t, 1 ≤ t → t ≤ d → (incoming t).scl = false)
    (ready : (incoming (d + 1)).scl = true) :
    run cfg s incoming (d + 1) = move cfg s .high := by
  rw [run, blocked_prefix cfg s incoming d ht hd
    (fun u t hu h1 h2 => by simp [step, hu.trans hp, echo t h1 h2])]
  simp [step, hp, ready, move]

/-- Free observations count the bus-free interval down without touching the outcome. -/
theorem stop_free_countdown (cfg : Config) (s : State) (incoming : Nat → Bus) (n : Nat)
    (hp : s.phase = .stopFree) (hn : n ≤ s.remaining.val)
    (free : ∀ t, 1 ≤ t → t ≤ n → incoming t = ⟨true, true⟩) :
    (run cfg s incoming n).phase = .stopFree ∧
      (run cfg s incoming n).remaining.val = s.remaining.val - n ∧
      (run cfg s incoming n).outcome = s.outcome := by
  induction n with
  | zero => simp [run, hp]
  | succ n ih =>
    obtain ⟨p, r, o⟩ := ih (by omega) (fun t h1 h2 => free t h1 (by omega))
    have obs := free (n + 1) (by omega) (Nat.le_refl _)
    have positive : (run cfg s incoming n).remaining.val ≠ 0 := by omega
    rw [run, step, p, obs]
    simp only [Bool.and_self, if_true, beq_iff_eq, positive, if_false, count]
    refine ⟨p, ?_, o⟩
    show (run cfg s incoming n).remaining.val - 1 = s.remaining.val - (n + 1)
    omega

/-- **STOP completes behind an input pipeline.** From a fresh bus-free hold, `d` blocked
observations — the controller's own STOP echo behind `d` input registers
(`stop_holds_data_low`), or anything else — followed by `phaseCycles` free observations
report the transaction's outcome, provided the wait budget covers the blocked ones. -/
theorem stop_completes_behind_pipeline (cfg : Config) (s : State) (incoming : Nat → Bus) (d : Nat)
    (hp : s.phase = .stopFree) (ht : s.remaining = cfg.phaseMinusOne) (hd : d ≤ s.waitLeft.val)
    (echo : ∀ t, 1 ≤ t → t ≤ d → ((incoming t).scl && (incoming t).sda) = false)
    (free : ∀ t, d < t → t ≤ d + cfg.phaseCycles → incoming t = ⟨true, true⟩) :
    result (run cfg s incoming (d + cfg.phaseCycles)) = some s.outcome := by
  -- The echo leaves a fresh interval; the free observations then count it down.
  let waited : State :=
    {s with remaining := cfg.phaseMinusOne, waitLeft := ⟨s.waitLeft.val - d, by omega⟩}
  have waitedOut : run cfg s incoming d = waited :=
    blocked_prefix cfg s incoming d ht hd
      (fun u t hu h1 h2 => by simp [step, hu.trans hp, echo t h1 h2])
  obtain ⟨p, r, o⟩ := stop_free_countdown cfg waited (fun t => incoming (d + t))
    cfg.phaseMinusOne.val hp (Nat.le_refl _)
    (fun t _ h2 => free (d + t) (by omega) (by simp only [Config.phaseCycles]; omega))
  have last := free (d + cfg.phaseCycles) (by simp only [Config.phaseCycles]; omega) (Nat.le_refl _)
  have split : d + cfg.phaseCycles = d + cfg.phaseMinusOne.val + 1 := by
    simp only [Config.phaseCycles]; omega
  have zero : (run cfg waited (fun t => incoming (d + t)) cfg.phaseMinusOne.val).remaining.val = 0 := by
    simpa [waited] using r
  rw [split, run, run_add, waitedOut, ← split, last, step, p]
  simp [zero, finish, result, busy, o, waited]

end Pinwheel.I2C

namespace Pinwheel.I2C.RegisterRead

/-- The register-read controller holds SDA low through its STOP preparation too. -/
theorem stop_holds_data_low (r : Request) (phase : Phase) (target : Pins)
    (h : phase = .stopLow ∨ phase = .stopRise ∨ phase = .stopHigh) :
    (resolve (pins r phase) target).sda = false := by
  rcases h with h | h | h <;> simp [pins, h, resolve, resolveLine]

/-- Its qualified bus-free interval waits that echo out as well. -/
theorem stop_echo_is_waited_out (cfg : Config) (r : Request) (s : State) (earlier : Phase)
    (target : Pins) (now : s.phase = .stopFree)
    (stale : earlier = .stopLow ∨ earlier = .stopRise ∨ earlier = .stopHigh) :
    step cfg s (resolve (pins r earlier) target) = blocked cfg s := by
  have low := stop_holds_data_low r earlier target stale
  simp [step, now, low]

theorem run_add (cfg : Config) (s : State) (incoming : Nat → Bus) (a b : Nat) :
    run cfg s incoming (a + b) = run cfg (run cfg s incoming a) (fun t => incoming (a + t)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show step cfg (run cfg s incoming (a + b)) (incoming (a + b + 1)) = _
    rw [ih]
    rfl

theorem blocked_prefix (cfg : Config) (s : State) (incoming : Nat → Bus) (n : Nat)
    (ht : s.remaining = cfg.phaseMinusOne) (hn : n ≤ s.waitLeft.val)
    (blocks : ∀ (u : State) (t : Nat), u.phase = s.phase → 1 ≤ t → t ≤ n →
      step cfg u (incoming t) = blocked cfg u) :
    run cfg s incoming n =
      {s with remaining := cfg.phaseMinusOne, waitLeft := ⟨s.waitLeft.val - n, by omega⟩} := by
  induction n with
  | zero => simp [run, ← ht]
  | succ n ih =>
    rw [run, ih (by omega) (fun u t hu h1 h2 => blocks u t hu h1 (by omega)),
      blocks {s with remaining := cfg.phaseMinusOne, waitLeft := ⟨s.waitLeft.val - n, by omega⟩}
        (n + 1) rfl (by omega) (Nat.le_refl _)]
    simp [blocked, show 0 < s.waitLeft.val - n by omega, Nat.sub_sub]

theorem stop_free_countdown (cfg : Config) (s : State) (incoming : Nat → Bus) (n : Nat)
    (hp : s.phase = .stopFree) (hn : n ≤ s.remaining.val)
    (free : ∀ t, 1 ≤ t → t ≤ n → incoming t = ⟨true, true⟩) :
    (run cfg s incoming n).phase = .stopFree ∧
      (run cfg s incoming n).remaining.val = s.remaining.val - n ∧
      (run cfg s incoming n).samples = s.samples := by
  induction n with
  | zero => simp [run, hp]
  | succ n ih =>
    obtain ⟨p, r, o⟩ := ih (by omega) (fun t h1 h2 => free t h1 (by omega))
    have obs := free (n + 1) (by omega) (Nat.le_refl _)
    have positive : (run cfg s incoming n).remaining.val ≠ 0 := by omega
    rw [run, step, p, obs]
    simp only [Bool.and_self, if_true, beq_iff_eq, positive, if_false, count]
    refine ⟨p, ?_, o⟩
    show (run cfg s incoming n).remaining.val - 1 = s.remaining.val - (n + 1)
    omega

/-- The register read completes its STOP behind an input pipeline in the same way. -/
theorem stop_completes_behind_pipeline (cfg : Config) (s : State) (incoming : Nat → Bus) (d : Nat)
    (hp : s.phase = .stopFree) (ht : s.remaining = cfg.phaseMinusOne) (hd : d ≤ s.waitLeft.val)
    (echo : ∀ t, 1 ≤ t → t ≤ d → ((incoming t).scl && (incoming t).sda) = false)
    (free : ∀ t, d < t → t ≤ d + cfg.phaseCycles → incoming t = ⟨true, true⟩) :
    result (run cfg s incoming (d + cfg.phaseCycles)) = some (outcome s.samples) := by
  let waited : State :=
    {s with remaining := cfg.phaseMinusOne, waitLeft := ⟨s.waitLeft.val - d, by omega⟩}
  have waitedOut : run cfg s incoming d = waited :=
    blocked_prefix cfg s incoming d ht hd
      (fun u t hu h1 h2 => by simp [step, hu.trans hp, echo t h1 h2])
  obtain ⟨p, r, o⟩ := stop_free_countdown cfg waited (fun t => incoming (d + t))
    cfg.phaseMinusOne.val hp (Nat.le_refl _)
    (fun t _ h2 => free (d + t) (by omega) (by simp only [Config.phaseCycles]; omega))
  have last := free (d + cfg.phaseCycles) (by simp only [Config.phaseCycles]; omega) (Nat.le_refl _)
  have split : d + cfg.phaseCycles = d + cfg.phaseMinusOne.val + 1 := by
    simp only [Config.phaseCycles]; omega
  have zero : (run cfg waited (fun t => incoming (d + t)) cfg.phaseMinusOne.val).remaining.val = 0 := by
    simpa [waited] using r
  rw [split, run, run_add, waitedOut, ← split, last, step, p]
  simp [zero, move, result, o, waited]

end Pinwheel.I2C.RegisterRead
