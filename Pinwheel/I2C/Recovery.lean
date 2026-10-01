import Pinwheel.I2C.Spec

/-! Standalone release-only bus clear, following the nine-clock intervention in
NXP UM10204 rev. 7, §3.1.16. SDA is always released. The controller issues all nine
clock-release attempts even if SDA was already high, then captures SDA on the
terminal edge of the ninth guarded high interval. A high sample must additionally
pass a qualified both-high interval; a low sample finishes `stillStuck`.

There is no controller-generated STOP or automatic transaction retry. Persistent
SCL blocking consumes a finite wait budget. Qualification restarts its budget on
high observations, so arbitrary intermittent histories have no total-time bound.
Observed physical SCL edges require separate target/sampler assumptions: the
universal bound here concerns controller release attempts, not target transitions.
Hardware reset/power recovery for SCL stuck low or unsuccessful SDA recovery is an
external device/board obligation. -/
namespace Pinwheel.I2C.Recovery

inductive Outcome where
  | recovered | stillStuck | timeout | busFault
  deriving DecidableEq, Repr

inductive Phase where
  | clockFree
  | low (pulse : Fin 9)
  | rise (pulse : Fin 9)
  | high (pulse : Fin 9)
  | released | finished | timeout | fault
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  remaining : Fin 256
  waitLeft : Fin 256
  samples : Vector Bool 16
  deriving DecidableEq, Repr

def initial (cfg : Config) : State :=
  ⟨.clockFree, cfg.phaseMinusOne, cfg.waitMinusOne, Vector.replicate 16 false⟩

def pins : Phase → Pins
  | .low _ => ⟨.low, .release⟩
  | _ => {}

def move (cfg : Config) (s : State) (phase : Phase) : State :=
  {s with phase, remaining := cfg.phaseMinusOne, waitLeft := cfg.waitMinusOne}

def count (s : State) : State :=
  {s with remaining := ⟨s.remaining.val - 1, by omega⟩}

def finish (s : State) (phase : Phase) : State :=
  {s with phase, remaining := 0, waitLeft := 0}

def blocked (cfg : Config) (s : State) : State :=
  if h : 0 < s.waitLeft.val then
    {s with remaining := cfg.phaseMinusOne, waitLeft := ⟨s.waitLeft.val - 1, by omega⟩}
  else finish s .timeout

def qualify (cfg : Config) (s : State) (ready : Bool) (next : Phase) : State :=
  if ready then
    if s.remaining.val == 0 then move cfg s next
    else {count s with waitLeft := cfg.waitMinusOne}
  else blocked cfg s

def afterHigh (pulse : Fin 9) (sda : Bool) : Phase :=
  if h : pulse.val + 1 < 9 then .low ⟨pulse.val + 1, h⟩
  else if sda then .released else .finished

def step (cfg : Config) (s : State) (bus : Bus) : State :=
  match s.phase with
  | .finished | .timeout | .fault => s
  | .clockFree => qualify cfg s bus.scl (.low 0)
  | .low pulse =>
      if s.remaining.val == 0 then move cfg s (.rise pulse) else count s
  | .rise pulse => if bus.scl then move cfg s (.high pulse) else blocked cfg s
  | .high pulse =>
      if !bus.scl then finish s .fault
      else if s.remaining.val == 0 then
        let samples := if pulse.val == 8 then s.samples.set 0 bus.sda else s.samples
        move cfg {s with samples} (afterHigh pulse bus.sda)
      else count s
  | .released => qualify cfg s (bus.scl && bus.sda) .finished

def outcome (samples : Vector Bool 16) : Outcome :=
  if samples[0] then .recovered else .stillStuck

def result (s : State) : Option Outcome :=
  match s.phase with
  | .finished => some (outcome s.samples)
  | .timeout => some .timeout
  | .fault => some .busFault
  | _ => none

def run (cfg : Config) (s : State) (incoming : Nat → Bus) : Nat → State
  | 0 => s
  | n + 1 => step cfg (run cfg s incoming n) (incoming (n + 1))

/-- A monotone upper bound on release attempts already issued. Terminal states
retain the unused allowance; they cannot issue further attempts. -/
def allowance : Phase → Nat
  | .clockFree => 0
  | .low pulse => pulse.val
  | .rise pulse | .high pulse => pulse.val + 1
  | _ => 9

def releaseAttempt (before after : Phase) : Nat :=
  if (pins before).scl == .low && (pins after).scl == .release then 1 else 0

def attempts (cfg : Config) (incoming : Nat → Bus) : Nat → Nat
  | 0 => 0
  | n + 1 => attempts cfg incoming n + releaseAttempt
      (run cfg (initial cfg) incoming n).phase
      (run cfg (initial cfg) incoming (n + 1)).phase

theorem allowance_bound (phase : Phase) : allowance phase ≤ 9 := by
  cases phase <;> simp [allowance] <;> omega
  done

theorem allowance_afterHigh (pulse : Fin 9) (sda : Bool) :
    allowance (afterHigh pulse sda) = pulse.val + 1 := by
  by_cases h : pulse.val + 1 < 9 <;> cases sda <;> simp [afterHigh, h, allowance] <;> omega
  done

theorem step_allowance (cfg : Config) (s : State) (bus : Bus) :
    releaseAttempt s.phase (step cfg s bus).phase + allowance s.phase ≤
      allowance (step cfg s bus).phase := by
  cases hp : s.phase <;>
    by_cases hr : s.remaining.val = 0 <;> by_cases hw : 0 < s.waitLeft.val <;>
    cases hb : bus.scl <;> cases hd : bus.sda <;>
    simp_all [step, qualify, blocked, finish, count, move, releaseAttempt, pins]
  all_goals try simp only [allowance_afterHigh]
  all_goals simp [allowance] <;> omega
  done

theorem attempts_allowance (cfg : Config) (incoming : Nat → Bus) (n : Nat) :
    attempts cfg incoming n ≤ allowance (run cfg (initial cfg) incoming n).phase := by
  induction n with
  | zero => simp [attempts, run]
  | succ n ih =>
    have h := step_allowance cfg (run cfg (initial cfg) incoming n) (incoming (n + 1))
    simp only [attempts, run]
    omega
    done

/-- For every sampled history, at most nine controller SCL release attempts.
This is not a bound on edges independently generated by an external driver. -/
theorem attempts_bound (cfg : Config) (incoming : Nat → Bus) (n : Nat) :
    attempts cfg incoming n ≤ 9 :=
  Nat.le_trans (attempts_allowance cfg incoming n) (allowance_bound _)

theorem sda_released (phase : Phase) : (pins phase).sda = .release := by
  cases phase <;> rfl
  done

end Pinwheel.I2C.Recovery
