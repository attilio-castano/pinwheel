import Pinwheel.SPI.Spec

/-! Bounded MSB-first SPI transactions: all four modes, one or two bytes,
with chip select held across every bit and a final idle-clock half-period. -/
namespace Pinwheel.SPI.Transaction

structure Mode where
  cpol : Bool := false
  cpha : Bool := false
  deriving DecidableEq, Repr

structure Config where
  mode : Mode
  halfMinusOne : Fin 256
  bytesMinusOne : Fin 2
  deriving DecidableEq, Repr

def Config.halfCycles (cfg : Config) : Nat := cfg.halfMinusOne.val + 1
def Config.bits (cfg : Config) : Nat := 8 * (cfg.bytesMinusOne.val + 1)
def Config.phases (cfg : Config) : Nat := 2 * cfg.bits + 1
def Config.transferCycles (cfg : Config) : Nat := cfg.phases * cfg.halfCycles

def idlePins (cfg : Config) : SPI.Pins := ⟨true, cfg.mode.cpol, false⟩

/-- Independent wire contract, indexed by elapsed system-clock intervals.
The low eight bits hold a one-byte payload; a two-byte payload uses all sixteen. -/
def expectedPins (cfg : Config) (payload : BitVec 16) (cycle : Nat) : SPI.Pins :=
  if cycle < cfg.transferCycles then
    let edge := cycle / cfg.halfCycles
    ⟨false, cfg.mode.cpol != decide (edge % 2 = 1),
      payload.getLsbD (cfg.bits - 1 - ((edge - if cfg.mode.cpha then 1 else 0) / 2))⟩
  else idlePins cfg

def samplePhase (cfg : Config) (slot : Fin 16) : Nat :=
  2 * slot.val + if cfg.mode.cpha then 2 else 1

def sampleTime (cfg : Config) (slot : Fin 16) : Nat := samplePhase cfg slot * cfg.halfCycles

def expectedSamples (cfg : Config) (incoming : Nat → Bool) (cycle : Nat) : Vector Bool 16 :=
  Vector.ofFn fun slot =>
    if slot.val < cfg.bits ∧ sampleTime cfg slot ≤ cycle then incoming (sampleTime cfg slot) else false

inductive Control (cfg : Config) where
  | idle
  | active (phase : Fin cfg.phases) (tick : Fin cfg.halfCycles)
  deriving DecidableEq, Repr

def controlBusy {cfg : Config} : Control cfg → Bool
  | .idle => false
  | .active .. => true

def initialControl (cfg : Config) : Control cfg := .active ⟨0, by
  simp [Config.phases]⟩ ⟨0, Nat.zero_lt_succ _⟩

def advanceControl {cfg : Config} : Control cfg → Control cfg
  | .idle => .idle
  | .active phase tick =>
    if ht : tick.val + 1 < cfg.halfCycles then .active phase ⟨tick.val + 1, ht⟩
    else if hp : phase.val + 1 < cfg.phases then
      .active ⟨phase.val + 1, hp⟩ ⟨0, Nat.zero_lt_succ _⟩
    else .idle

def captureAt {cfg : Config} (control : Control cfg) (slot : Fin 16) : Bool :=
  match control with
  | .idle => false
  | .active phase tick => decide
      (slot.val < cfg.bits ∧ phase.val + 1 = samplePhase cfg slot ∧ tick.val + 1 = cfg.halfCycles)

structure State (cfg : Config) where
  control : Control cfg
  tx : BitVec 16
  samples : Vector Bool 16
  deriving DecidableEq, Repr

def initial (cfg : Config) (payload : BitVec 16) : State cfg :=
  ⟨initialControl cfg, payload, Vector.replicate 16 false⟩

/-- Stateful controller pin selection does not call the elapsed-time contract. -/
def pins {cfg : Config} (state : State cfg) : SPI.Pins :=
  match state.control with
  | .idle => ⟨true, cfg.mode.cpol, false⟩
  | .active phase _ =>
    ⟨false, cfg.mode.cpol != decide (phase.val % 2 = 1),
      state.tx.getLsbD (cfg.bits - 1 - ((phase.val - if cfg.mode.cpha then 1 else 0) / 2))⟩

def advance {cfg : Config} (state : State cfg) (miso : Bool) : State cfg :=
  ⟨advanceControl state.control, state.tx,
    Vector.ofFn fun slot => if captureAt state.control slot then miso else state.samples[slot]⟩

def run (cfg : Config) (payload : BitVec 16) (incoming : Nat → Bool) : Nat → State cfg
  | 0 => initial cfg payload
  | cycle + 1 => advance (run cfg payload incoming cycle) (incoming (cycle + 1))

def ControlRep (cfg : Config) (cycle : Nat) (control : Control cfg) : Prop :=
  if cycle < cfg.transferCycles then ∃ phase tick, control = .active phase tick ∧
    cycle = phase.val * cfg.halfCycles + tick.val else control = .idle

theorem bits_bounds (cfg : Config) : 8 ≤ cfg.bits ∧ cfg.bits ≤ 16 := by
  unfold Config.bits
  omega

theorem phases_bound (cfg : Config) : cfg.phases ≤ 33 := by
  have := bits_bounds cfg
  unfold Config.phases
  omega

theorem control_advances (cfg : Config) (cycle : Nat) (control : Control cfg)
    (h : ControlRep cfg cycle control) : ControlRep cfg (cycle + 1) (advanceControl control) := by
  have phase_bound (phase : Fin cfg.phases) :
      (phase.val + 1) * cfg.halfCycles ≤ cfg.transferCycles :=
    Nat.mul_le_mul_right cfg.halfCycles phase.isLt
  have next_phase_bound (phase : Fin cfg.phases) (hp : phase.val + 1 < cfg.phases) :
      (phase.val + 2) * cfg.halfCycles ≤ cfg.transferCycles :=
    Nat.mul_le_mul_right cfg.halfCycles hp
  grind [ControlRep, advanceControl, Config.transferCycles]
  done

theorem control_initial (cfg : Config) : ControlRep cfg 0 (initialControl cfg) := by
  have positive : 0 < cfg.transferCycles :=
    Nat.mul_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
  simp [ControlRep, positive, initialControl]
  exact ⟨⟨0, Nat.zero_lt_succ _⟩, ⟨0, Nat.zero_lt_succ _⟩, ⟨⟨rfl, rfl⟩, by simp⟩⟩
  done

theorem run_control (cfg : Config) (payload : BitVec 16) (incoming : Nat → Bool) (cycle : Nat) :
    ControlRep cfg cycle (run cfg payload incoming cycle).control :=
  Nat.recOn cycle (control_initial cfg)
    (fun n ih => control_advances cfg n (run cfg payload incoming n).control ih)

theorem run_tx (cfg : Config) (payload : BitVec 16) (incoming : Nat → Bool) (cycle : Nat) :
    (run cfg payload incoming cycle).tx = payload := Nat.recOn cycle rfl (fun _ ih => ih)

theorem capture_correct (cfg : Config) (cycle : Nat) (control : Control cfg)
    (h : ControlRep cfg cycle control) (slot : Fin 16) :
    captureAt control slot = true ↔ slot.val < cfg.bits ∧ cycle + 1 = sampleTime cfg slot := by
  by_cases hs : slot.val < cfg.bits
  · have bound : samplePhase cfg slot ≤ cfg.phases := by grind [samplePhase, Config.phases]
    have sample_bound : sampleTime cfg slot ≤ cfg.transferCycles :=
      Nat.mul_le_mul_right cfg.halfCycles bound
    have below (phase : Fin cfg.phases) (hp : phase.val + 1 < samplePhase cfg slot) :
        (phase.val + 2) * cfg.halfCycles ≤ sampleTime cfg slot :=
      Nat.mul_le_mul_right cfg.halfCycles hp
    have above (phase : Fin cfg.phases) (hp : samplePhase cfg slot < phase.val + 1) :
        sampleTime cfg slot ≤ phase.val * cfg.halfCycles :=
      Nat.mul_le_mul_right cfg.halfCycles (by omega)
    grind [ControlRep, captureAt, sampleTime, Config.transferCycles, Config.halfCycles]
    done
  · cases control
    all_goals simp [captureAt, hs]
    done

theorem sample_positive (cfg : Config) (slot : Fin 16) : 0 < sampleTime cfg slot :=
  Nat.mul_pos (by grind [samplePhase]) (Nat.zero_lt_succ _)

theorem run_samples (cfg : Config) (payload : BitVec 16) (incoming : Nat → Bool) (cycle : Nat) :
    (run cfg payload incoming cycle).samples = expectedSamples cfg incoming cycle := by
  induction cycle with
  | zero =>
    ext i hi
    simp [run, initial, expectedSamples, Nat.ne_of_gt (sample_positive cfg ⟨i, hi⟩)]
    done
  | succ n ih =>
    ext i hi
    simp [run, advance, ih, expectedSamples]
    have he := capture_correct cfg n _ (run_control cfg payload incoming n) ⟨i, hi⟩
    grind
    done

theorem phase_quotient (cfg : Config) (phase : Fin cfg.phases) (tick : Fin cfg.halfCycles) :
    (phase.val * cfg.halfCycles + tick.val) / cfg.halfCycles = phase.val := by
  simpa only [Nat.add_comm (phase.val * cfg.halfCycles) tick.val,
    Nat.div_eq_of_lt tick.isLt, Nat.zero_add] using
    Nat.add_mul_div_right tick.val phase.val (show 0 < cfg.halfCycles from Nat.zero_lt_succ _)

theorem waveform_correct (cfg : Config) (payload : BitVec 16) (incoming : Nat → Bool) (cycle : Nat) :
    pins (run cfg payload incoming cycle) = expectedPins cfg payload cycle := by
  have hc := run_control cfg payload incoming cycle
  have ht := run_tx cfg payload incoming cycle
  grind [ControlRep, expectedPins, pins, phase_quotient, idlePins]
  done

theorem busy_exact (cfg : Config) (payload : BitVec 16) (incoming : Nat → Bool) (cycle : Nat) :
    controlBusy (run cfg payload incoming cycle).control = decide (cycle < cfg.transferCycles) := by
  grind [run_control, ControlRep, controlBusy]
  done

def completeSamples (cfg : Config) (incoming : Nat → Bool) : Vector Bool 16 :=
  Vector.ofFn fun slot => if slot.val < cfg.bits then incoming (sampleTime cfg slot) else false

theorem sample_within (cfg : Config) (slot : Fin 16) (h : slot.val < cfg.bits) :
    sampleTime cfg slot ≤ cfg.transferCycles :=
  Nat.mul_le_mul_right cfg.halfCycles (by grind [samplePhase, Config.phases])

theorem samples_complete (cfg : Config) (payload : BitVec 16) (incoming : Nat → Bool)
    (cycle : Nat) (h : cfg.transferCycles ≤ cycle) :
    (run cfg payload incoming cycle).samples = completeSamples cfg incoming := by
  rw [run_samples]
  ext i hi
  grind [expectedSamples, completeSamples, sample_within]
  done

end Pinwheel.SPI.Transaction
