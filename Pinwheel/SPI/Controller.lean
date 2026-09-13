import Pinwheel.SPI.Spec

/-! Finite mode-0 SPI control, sampled receive storage, and refinement proofs. -/

namespace Pinwheel.SPI

/-- Seventeen timed phases: eight low/high pairs, then a chip-select hold phase. -/
inductive Control (cfg : Config) where
  | idle
  | active (phase : Fin 17) (tick : Fin cfg.halfCycles)
  deriving DecidableEq, Repr

def controlBusy {cfg : Config} : Control cfg → Bool
  | .idle => false
  | .active .. => true

def initialControl (cfg : Config) : Control cfg := .active 0 ⟨0, Nat.zero_lt_succ _⟩

def advanceControl {cfg : Config} : Control cfg → Control cfg
  | .idle => .idle
  | .active phase tick =>
    if ht : tick.val + 1 < cfg.halfCycles then
      .active phase ⟨tick.val + 1, ht⟩
    else if hp : phase.val + 1 < 17 then
      .active ⟨phase.val + 1, hp⟩ ⟨0, Nat.zero_lt_succ _⟩
    else .idle

/-- One receive slot is enabled at the end of each low clock phase. -/
def captureAt {cfg : Config} (control : Control cfg) (bit : Fin 8) : Bool :=
  match control with
  | .idle => false
  | .active phase tick => decide (phase.val = 2 * bit.val ∧ tick.val + 1 = cfg.halfCycles)

/-- Receive slots are eight Boolean registers in wire order, not an unbounded history. -/
structure State (cfg : Config) where
  control : Control cfg
  tx : BitVec 8
  samples : Vector Bool 8
  valid : Bool
  deriving DecidableEq, Repr

structure Input where
  reset : Bool := false
  request : Option (BitVec 8) := none
  miso : Bool := false
  deriving Repr

def resetState (cfg : Config) : State cfg := ⟨.idle, 0, Vector.replicate 8 false, false⟩

def initial (cfg : Config) (byte : BitVec 8) : State cfg :=
  ⟨initialControl cfg, byte, Vector.replicate 8 false, false⟩

/-- Implementation pin selection does not call the specification's wire-frame array. -/
def pins {cfg : Config} (state : State cfg) : Pins :=
  match state.control with
  | .idle => ⟨true, false, false⟩
  | .active phase _ =>
    ⟨false, decide (phase.val % 2 = 1), state.tx.getLsbD (7 - phase.val / 2)⟩

/-- Assemble receive storage in wire order; slot zero becomes the most-significant bit. -/
def received {cfg : Config} (state : State cfg) : BitVec 8 :=
  BitVec.ofBoolListBE [state.samples[0], state.samples[1], state.samples[2], state.samples[3],
    state.samples[4], state.samples[5], state.samples[6], state.samples[7]]

def result {cfg : Config} (state : State cfg) : Option (BitVec 8) :=
  if state.valid then some (received state) else none

/-- Advance one system interval, consuming the MISO value at the destination edge. -/
def advance {cfg : Config} (state : State cfg) (miso : Bool) : State cfg :=
  let next := advanceControl state.control
  { control := next
    tx := state.tx
    samples := Vector.ofFn fun bit =>
      if captureAt state.control bit then miso else state.samples[bit]
    valid := if controlBusy state.control then !controlBusy next else state.valid }

def step {cfg : Config} (state : State cfg) (input : Input) : State cfg :=
  if input.reset then resetState cfg
  else if controlBusy state.control then advance state input.miso
  else match input.request with
    | some byte => initial cfg byte
    | none => advance state input.miso

/-- An uninterrupted transfer, with arbitrary edge-indexed incoming data. -/
def run (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool) : Nat → State cfg
  | 0 => initial cfg byte
  | n + 1 => advance (run cfg byte incoming n) (incoming (n + 1))

def ControlRep (cfg : Config) (cycle : Nat) (control : Control cfg) : Prop :=
  if cycle < cfg.transferCycles then
    ∃ phase tick, control = .active phase tick ∧
      cycle = phase.val * cfg.halfCycles + tick.val
  else control = .idle

theorem control_advances (cfg : Config) (cycle : Nat) (control : Control cfg)
    (h : ControlRep cfg cycle control) : ControlRep cfg (cycle + 1) (advanceControl control) := by
  have phase_bound (phase : Fin 17) :
      (phase.val + 1) * cfg.halfCycles ≤ cfg.transferCycles :=
    Nat.mul_le_mul_right cfg.halfCycles phase.isLt
  have next_phase_bound (phase : Fin 17) (hp : phase.val + 1 < 17) :
      (phase.val + 2) * cfg.halfCycles ≤ cfg.transferCycles :=
    Nat.mul_le_mul_right cfg.halfCycles hp
  grind [ControlRep, advanceControl, Config.transferCycles]

theorem control_initial (cfg : Config) : ControlRep cfg 0 (initialControl cfg) := by
  grind [ControlRep, initialControl, Config.transferCycles, Config.halfCycles]

theorem run_control (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    ControlRep cfg cycle (run cfg byte incoming cycle).control :=
  Nat.recOn cycle (control_initial cfg)
    (fun n ih => control_advances cfg n (run cfg byte incoming n).control ih)

theorem run_tx (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    (run cfg byte incoming cycle).tx = byte :=
  Nat.recOn cycle rfl (fun _ ih => ih)

theorem reset_dominates (cfg : Config) (state : State cfg)
    (request : Option (BitVec 8)) (miso : Bool) :
    step state ⟨true, request, miso⟩ = resetState cfg := rfl

/-- A receive slot is enabled on exactly its specified absolute sampling edge. -/
theorem capture_correct (cfg : Config) (cycle : Nat) (control : Control cfg)
    (h : ControlRep cfg cycle control) (bit : Fin 8) :
    captureAt control bit = true ↔ cycle + 1 = sampleTime cfg bit := by
  have positive : 0 < cfg.halfCycles := Nat.zero_lt_succ _
  have sample_bound : sampleTime cfg bit ≤ 15 * cfg.halfCycles :=
    Nat.mul_le_mul_right cfg.halfCycles (by omega)
  have below (phase : Fin 17) (hp : phase.val < 2 * bit.val) :
      (phase.val + 1) * cfg.halfCycles ≤ (2 * bit.val) * cfg.halfCycles :=
    Nat.mul_le_mul_right cfg.halfCycles hp
  have above (phase : Fin 17) (hp : 2 * bit.val < phase.val) :
      (2 * bit.val + 1) * cfg.halfCycles ≤ phase.val * cfg.halfCycles :=
    Nat.mul_le_mul_right cfg.halfCycles hp
  grind [ControlRep, captureAt, sampleTime, Config.transferCycles]

/-- Receive storage keeps precisely the samples whose designated edges have occurred. -/
theorem samples_advance (cfg : Config) (incoming : Nat → Bool) (cycle : Nat) (state : State cfg)
    (hc : ControlRep cfg cycle state.control)
    (hr : state.samples = expectedSamples cfg incoming cycle) :
    (advance state (incoming (cycle + 1))).samples = expectedSamples cfg incoming (cycle + 1) := by
  ext i hi
  simp [advance, hr, expectedSamples]
  have he := capture_correct cfg cycle state.control hc ⟨i, hi⟩
  grind

theorem sample_positive (cfg : Config) (bit : Fin 8) : 0 < sampleTime cfg bit :=
  Nat.mul_pos (by omega) (Nat.zero_lt_succ _)

theorem samples_initial (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool) :
    (initial cfg byte).samples = expectedSamples cfg incoming 0 := by
  ext i hi
  simp [initial, expectedSamples, Nat.ne_of_gt (sample_positive cfg ⟨i, hi⟩)]

theorem run_samples (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    (run cfg byte incoming cycle).samples = expectedSamples cfg incoming cycle :=
  Nat.recOn cycle (samples_initial cfg byte incoming)
    (fun n ih => samples_advance cfg incoming n (run cfg byte incoming n)
      (run_control cfg byte incoming n) ih)

theorem phase_quotient (cfg : Config) (phase : Fin 17) (tick : Fin cfg.halfCycles) :
    (phase.val * cfg.halfCycles + tick.val) / cfg.halfCycles = phase.val := by
  simpa only [Nat.add_comm (phase.val * cfg.halfCycles) tick.val,
    Nat.div_eq_of_lt tick.isLt, Nat.zero_add] using
    Nat.add_mul_div_right tick.val phase.val
      (show 0 < cfg.halfCycles from Nat.zero_lt_succ _)

theorem pins_phase (cfg : Config) (state : State cfg) (phase : Fin 17)
    (tick : Fin cfg.halfCycles) (h : state.control = .active phase tick) :
    pins state = (wireFrame state.tx).getD phase.val ⟨true, false, false⟩ := by
  have phases : phase.val = 0 ∨ phase.val = 1 ∨ phase.val = 2 ∨ phase.val = 3 ∨ phase.val = 4 ∨ phase.val = 5 ∨ phase.val = 6 ∨ phase.val = 7 ∨ phase.val = 8 ∨ phase.val = 9 ∨ phase.val = 10 ∨ phase.val = 11 ∨ phase.val = 12 ∨ phase.val = 13 ∨ phase.val = 14 ∨ phase.val = 15 ∨ phase.val = 16 := by omega
  rcases phases with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  all_goals simp [pins, h, wireFrame, Array.getD, hp]

theorem represented_pins (cfg : Config) (cycle : Nat) (state : State cfg)
    (h : ControlRep cfg cycle state.control) :
    pins state = expectedPins cfg state.tx cycle := by
  have after_frame (hc : cfg.transferCycles ≤ cycle) : 17 ≤ cycle / cfg.halfCycles :=
    (Nat.le_div_iff_mul_le (Nat.zero_lt_succ _)).mpr hc
  grind [ControlRep, expectedPins, pins_phase, phase_quotient, wireFrame_size, pins]

/-- All output pins match the independent wire specification at every cycle. -/
theorem waveform_correct (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    pins (run cfg byte incoming cycle) = expectedPins cfg byte cycle :=
  (represented_pins cfg cycle _ (run_control cfg byte incoming cycle)).trans
    (congrArg (fun tx => expectedPins cfg tx cycle) (run_tx cfg byte incoming cycle))

theorem busy_exact (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    controlBusy (run cfg byte incoming cycle).control = decide (cycle < cfg.transferCycles) := by
  grind [run_control, ControlRep, controlBusy]

theorem valid_advance (cfg : Config) (state : State cfg) (miso : Bool)
    (h : state.valid = !controlBusy state.control) :
    (advance state miso).valid = !controlBusy (advance state miso).control := by
  cases hc : state.control
  all_goals simp [advance, hc, controlBusy, h, advanceControl]

theorem run_valid (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    (run cfg byte incoming cycle).valid = !controlBusy (run cfg byte incoming cycle).control :=
  Nat.recOn cycle rfl (fun n ih => valid_advance cfg (run cfg byte incoming n) _ ih)

theorem all_samples_elapsed (cfg : Config) (cycle : Nat) (h : cfg.transferCycles ≤ cycle)
    (bit : Fin 8) : sampleTime cfg bit ≤ cycle :=
  Nat.le_trans (Nat.mul_le_mul_right cfg.halfCycles (by omega)) h

theorem received_complete (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat)
    (h : cfg.transferCycles ≤ cycle) :
    received (run cfg byte incoming cycle) = expectedByte cfg incoming := by
  unfold received
  rw [run_samples]
  unfold expectedByte
  congr 1
  simp only [expectedSamples, Vector.getElem_ofFn, if_pos (all_samples_elapsed cfg cycle h _)]
  simp [sampleTime]

/-- Completion is exposed only after the final low-clock hold interval. -/
theorem result_exact (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    result (run cfg byte incoming cycle) =
      if cycle < cfg.transferCycles then none else some (expectedByte cfg incoming) := by
  simp only [result, run_valid, busy_exact]
  grind [received_complete]

theorem busy_ignores_request (cfg : Config) (state : State cfg)
    (request : Option (BitVec 8)) (miso : Bool) (h : controlBusy state.control = true) :
    step state ⟨false, request, miso⟩ = advance state miso := by
  simp [step, h]

theorem idle_accepts (cfg : Config) (state : State cfg) (byte : BitVec 8) (miso : Bool)
    (h : state.control = .idle) :
    step state ⟨false, some byte, miso⟩ = initial cfg byte := by
  simp [step, h, controlBusy]

theorem idle_retains (cfg : Config) (state : State cfg) (miso : Bool)
    (h : state.control = .idle) : step state ⟨false, none, miso⟩ = state := by
  simp [step, advance, h, controlBusy, advanceControl, captureAt]
  cases state
  simp_all

/-- Every system interval within a phase has the phase's prescribed pin values. -/
theorem phase_interval (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool)
    (phase : Fin 17) (tick : Fin cfg.halfCycles) :
    pins (run cfg byte incoming (phase.val * cfg.halfCycles + tick.val)) =
      (wireFrame byte).getD phase.val ⟨true, false, false⟩ := by
  rw [waveform_correct, expectedPins, phase_quotient]

theorem sample_times_distinct (cfg : Config) (a b : Fin 8)
    (h : sampleTime cfg a = sampleTime cfg b) : a = b := by
  have factors := Nat.eq_of_mul_eq_mul_right (show 0 < cfg.halfCycles from Nat.zero_lt_succ _) h
  omega

theorem frame_mosi_pair (byte : BitVec 8) (bit : Fin 8) :
    ((wireFrame byte).getD (2 * bit.val) ⟨true, false, false⟩).mosi =
      ((wireFrame byte).getD (2 * bit.val + 1) ⟨true, false, false⟩).mosi := by
  have bits : bit.val = 0 ∨ bit.val = 1 ∨ bit.val = 2 ∨ bit.val = 3 ∨ bit.val = 4 ∨ bit.val = 5 ∨ bit.val = 6 ∨ bit.val = 7 := by omega
  rcases bits with hb | hb | hb | hb | hb | hb | hb | hb
  all_goals simp [wireFrame, Array.getD, hb]

/-- MOSI remains stable across the rising sampling edge, throughout both adjacent phases. -/
theorem mosi_stable_pair (cfg : Config) (byte : BitVec 8) (incoming : Nat → Bool)
    (bit : Fin 8) (lowTick highTick : Fin cfg.halfCycles) :
    (pins (run cfg byte incoming (2 * bit.val * cfg.halfCycles + lowTick.val))).mosi =
      (pins (run cfg byte incoming ((2 * bit.val + 1) * cfg.halfCycles + highTick.val))).mosi := by
  rw [phase_interval cfg byte incoming ⟨2 * bit.val, by omega⟩ lowTick,
    phase_interval cfg byte incoming ⟨2 * bit.val + 1, by omega⟩ highTick]
  exact frame_mosi_pair byte bit

end Pinwheel.SPI
