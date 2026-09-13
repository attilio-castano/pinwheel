import Pinwheel.Engine.Proofs
import Pinwheel.SPI.Controller

namespace Pinwheel.Compile.SPI

open Pinwheel

def encodePins (pins : SPI.Pins) : Engine.Levels :=
  BitVec.ofBoolListBE [pins.csN, pins.sclk, pins.mosi]

/-- Compute actions from bit positions, independently of the wire-frame specification. -/
def action (cfg : SPI.Config) (byte : BitVec 8) (phase : Fin 17) : Engine.Action :=
  { levels := encodePins ⟨false, decide (phase.val % 2 = 1), byte.getLsbD (7 - phase.val / 2)⟩
    durationMinusOne := cfg.halfMinusOne
    capture := if h : phase.val % 2 = 1 then some ⟨phase.val / 2, by omega⟩ else none }

def program (cfg : SPI.Config) (byte : BitVec 8) : Engine.Program :=
  { memory := Vector.ofFn fun pc =>
      if h : pc.val < 17 then .action (action cfg byte ⟨pc.val, h⟩) else .halt
    idle := 4 }

/-- Relate the previously verified controller to bounded engine execution state.
Idle denotes completed uninterrupted execution; reset is handled by the engine interface. -/
def liftState (cfg : SPI.Config) (s : SPI.State cfg) : Engine.State :=
  { control := match s.control with
      | .idle => .stopped .completed
      | .active phase tick =>
        .active ⟨phase.val, by omega⟩ ⟨cfg.halfMinusOne.val - tick.val, by omega⟩
    levels := encodePins (SPI.pins s)
    samples := s.samples }

theorem fetch_action (cfg : SPI.Config) (byte : BitVec 8) (pc : Fin 32) (h : pc.val < 17) :
    (program cfg byte).fetch pc = .action (action cfg byte ⟨pc.val, h⟩) := by
  simp [program, Engine.Program.fetch, h]

theorem fetch_halt (cfg : SPI.Config) (byte : BitVec 8) (pc : Fin 32) (h : 17 ≤ pc.val) :
    (program cfg byte).fetch pc = .halt := by
  simp [program, Engine.Program.fetch, show ¬pc.val < 17 by omega]

theorem advance_simulation (cfg : SPI.Config) (byte : BitVec 8) (s : SPI.State cfg)
    (input : Bool) (h : s.tx = byte) :
    Engine.advance (program cfg byte) (liftState cfg s) input = liftState cfg (SPI.advance s input) := by
  cases s with
  | mk control tx slots valid =>
    cases h
    cases control with
    | idle => simp [Engine.advance, liftState, SPI.advance, SPI.advanceControl, SPI.captureAt, SPI.pins]
    | active phase tick =>
      have duration : cfg.halfCycles = cfg.halfMinusOne.val + 1 := rfl
      by_cases ht : tick.val + 1 < cfg.halfCycles
      · have remaining : 0 < cfg.halfMinusOne.val - tick.val := by omega
        simp [Engine.advance, liftState, SPI.advance, SPI.advanceControl, ht, remaining,
          SPI.pins, SPI.captureAt, Nat.ne_of_lt ht, Nat.sub_sub]
      · have endTick : tick.val = cfg.halfMinusOne.val := by omega
        simp [Engine.advance, liftState, SPI.advance, SPI.advanceControl, endTick, duration]
        have phases : phase.val = 0 ∨ phase.val = 1 ∨ phase.val = 2 ∨ phase.val = 3 ∨ phase.val = 4 ∨ phase.val = 5 ∨ phase.val = 6 ∨ phase.val = 7 ∨ phase.val = 8 ∨ phase.val = 9 ∨ phase.val = 10 ∨ phase.val = 11 ∨ phase.val = 12 ∨ phase.val = 13 ∨ phase.val = 14 ∨ phase.val = 15 ∨ phase.val = 16 := by omega
        rcases phases with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
        all_goals simp [Engine.next, Engine.enter, program, Engine.Program.fetch,
          action, SPI.pins, SPI.captureAt, Engine.capture, hp, endTick, duration]
        all_goals try refine ⟨rfl, rfl, ?_⟩
        all_goals try refine ⟨rfl, ?_⟩
        all_goals grind

theorem start_simulation (cfg : SPI.Config) (byte : BitVec 8) (input : Bool) :
    Engine.start (program cfg byte) input = liftState cfg (SPI.initial cfg byte) := by
  simp [Engine.start, Engine.enter, program, Engine.Program.fetch, action,
    liftState, SPI.initial, SPI.initialControl, SPI.pins, Engine.capture]
  grind

theorem run_simulation (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    Engine.run (program cfg byte) (Engine.start (program cfg byte) (incoming 0)) incoming cycle =
      liftState cfg (SPI.run cfg byte incoming cycle) := by
  induction cycle with
  | zero => exact start_simulation cfg byte (incoming 0)
  | succ n ih =>
    rw [Engine.run, ih, advance_simulation cfg byte _ _ (SPI.run_tx cfg byte incoming n)]
    rfl

def execute (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) : Engine.State :=
  Engine.run (program cfg byte) (Engine.start (program cfg byte) (incoming 0)) incoming cycle

/-- Compiled execution matches the independent three-pin waveform specification. -/
theorem waveform_correct (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    (execute cfg byte incoming cycle).levels = encodePins (SPI.expectedPins cfg byte cycle) := by
  simp only [execute, run_simulation, liftState]
  exact congrArg encodePins (Pinwheel.SPI.waveform_correct cfg byte incoming cycle)

theorem samples_correct (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    (execute cfg byte incoming cycle).samples = SPI.expectedSamples cfg incoming cycle := by
  simp [execute, run_simulation, liftState, SPI.run_samples]

theorem busy_lift (cfg : SPI.Config) (s : SPI.State cfg) :
    Engine.busy (liftState cfg s) = SPI.controlBusy s.control := by
  cases h : s.control
  all_goals simp [Engine.busy, liftState, h, SPI.controlBusy]

theorem busy_exact (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    Engine.busy (execute cfg byte incoming cycle) = decide (cycle < cfg.transferCycles) := by
  simp [execute, run_simulation, busy_lift, Pinwheel.SPI.busy_exact]

theorem result_lift (cfg : SPI.Config) (s : SPI.State cfg) :
    Engine.result (liftState cfg s) = if SPI.controlBusy s.control then none else some s.samples := by
  cases h : s.control
  all_goals simp [Engine.result, liftState, h, SPI.controlBusy]

theorem result_exact (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    Engine.result (execute cfg byte incoming cycle) =
      if cycle < cfg.transferCycles then none else some (SPI.expectedSamples cfg incoming cycle) := by
  simp [execute, run_simulation, result_lift, Pinwheel.SPI.busy_exact, SPI.run_samples]

theorem received_correct (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat)
    (h : cfg.transferCycles ≤ cycle) :
    Engine.samplesByte (execute cfg byte incoming cycle).samples = SPI.expectedByte cfg incoming := by
  rw [execute, run_simulation]
  exact Pinwheel.SPI.received_complete cfg byte incoming cycle h

end Pinwheel.Compile.SPI
