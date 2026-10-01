import Pinwheel.SPI.Transaction
import Pinwheel.Compile.SPI
import Pinwheel.Hardware.Execution.Images

namespace Pinwheel.Compile.SPITransaction
open Engine.Reactive
abbrev Config := Pinwheel.SPI.Transaction.Config
abbrev ModelState := Pinwheel.SPI.Transaction.State

def entryCapture (cfg : Config) (phase : Nat) : Option (Capture 15) :=
  if h : 0 < phase ∧ phase ≤ 2 * cfg.bits ∧
      phase % 2 = (if cfg.mode.cpha then 0 else 1) then
    some ⟨0, ⟨(phase - if cfg.mode.cpha then 2 else 1) / 2, by
      have := SPI.Transaction.bits_bounds cfg
      split <;> omega⟩⟩
  else none

def action (cfg : Config) (payload : BitVec 16) (phase : Fin cfg.phases) : Action 15 :=
  { pins := Pins.pushPull (Compile.SPI.encodePins
      ⟨false, cfg.mode.cpol != decide (phase.val % 2 = 1),
        payload.getLsbD (cfg.bits - 1 - ((phase.val - if cfg.mode.cpha then 1 else 0) / 2))⟩)
    durationMinusOne := cfg.halfMinusOne
    capture := entryCapture cfg phase.val }

def program (cfg : Config) (payload : BitVec 16) : Hardware.Execution.Image :=
  { memory := Vector.ofFn fun pc =>
      if h : pc.val < cfg.phases then .action (action cfg payload ⟨pc.val, h⟩) else .halt
    idle := Pins.pushPull (Compile.SPI.encodePins (SPI.Transaction.idlePins cfg))
    last := ⟨cfg.phases, by have := SPI.Transaction.phases_bound cfg; omega⟩ }

def liftState (cfg : Config) (s : ModelState cfg) : Engine.Reactive.State 255 15 :=
  { control := match s.control with
      | .idle => .stopped .completed
      | .active phase tick => .active
          ⟨phase.val, by have := SPI.Transaction.phases_bound cfg; omega⟩
          ⟨cfg.halfMinusOne.val - tick.val, by omega⟩
    pins := Pins.pushPull (Compile.SPI.encodePins (SPI.Transaction.pins s))
    samples := s.samples }

theorem entry_capture_correct (cfg : Config) (phase : Nat) (slots : Vector Bool 16) (input : Inputs) :
    capture slots (entryCapture cfg phase) input = Vector.ofFn fun slot =>
      if slot.val < cfg.bits ∧ phase = SPI.Transaction.samplePhase cfg slot then input[0] else slots[slot] := by
  ext i hi
  simp only [entryCapture, capture, Engine.capture, Vector.getElem_ofFn]
  split
  all_goals split
  all_goals simp_all only [Vector.getElem_ofFn, Option.some.injEq, Fin.mk.injEq,
    SPI.Transaction.samplePhase, if_pos]
  all_goals grind
  done

theorem advance_simulation (cfg : Config) (payload : BitVec 16) (s : ModelState cfg)
    (input : Inputs) (h : s.tx = payload) :
    Engine.Reactive.advance (program cfg payload) (liftState cfg s) input =
      liftState cfg (SPI.Transaction.advance s input[0]) := by
  rcases s with ⟨control, tx, slots⟩
  cases h
  cases control with
  | idle => simp [Engine.Reactive.advance, liftState, SPI.Transaction.advance,
      SPI.Transaction.advanceControl, SPI.Transaction.captureAt, SPI.Transaction.pins]
  | active phase tick =>
    have duration : cfg.halfCycles = cfg.halfMinusOne.val + 1 := rfl
    by_cases ht : tick.val + 1 < cfg.halfCycles
    · have remaining : 0 < cfg.halfMinusOne.val - tick.val := by omega
      simp [Engine.Reactive.advance, liftState, SPI.Transaction.advance,
        SPI.Transaction.advanceControl, ht, remaining, SPI.Transaction.pins,
        SPI.Transaction.captureAt, Nat.ne_of_lt ht, Nat.sub_sub]
      done
    · have endTick : tick.val = cfg.halfMinusOne.val := by omega
      simp [Engine.Reactive.advance, liftState, SPI.Transaction.advance,
        SPI.Transaction.advanceControl, endTick, SPI.Transaction.Config.halfCycles,
        next, program, phase.isLt]
      by_cases hp : phase.val + 1 < cfg.phases
      all_goals simp [hp, enter, Program.fetch, action, SPI.Transaction.pins, stop,
        SPI.Transaction.captureAt, SPI.Transaction.Config.halfCycles, endTick,
        entry_capture_correct, SPI.Transaction.idlePins]
      ext i hi
      grind [SPI.Transaction.Config.phases, SPI.Transaction.samplePhase]
      done

theorem start_simulation (cfg : Config) (payload : BitVec 16) (input : Inputs) :
    Engine.Reactive.start (program cfg payload) input = liftState cfg (SPI.Transaction.initial cfg payload) := by
  simp [Engine.Reactive.start, enter, program, Program.fetch, action,
    entryCapture, liftState, SPI.Transaction.initial, SPI.Transaction.initialControl,
    SPI.Transaction.pins, SPI.Transaction.Config.phases, capture]
  done

theorem run_simulation (cfg : Config) (payload : BitVec 16) (incoming : Nat → Inputs) (cycle : Nat) :
    Engine.Reactive.run (program cfg payload) (Engine.Reactive.start (program cfg payload) (incoming 0)) incoming cycle =
      liftState cfg (SPI.Transaction.run cfg payload (fun t => (incoming t)[0]) cycle) := by
  induction cycle with
  | zero => exact start_simulation cfg payload (incoming 0)
  | succ n ih =>
    rw [Engine.Reactive.run, ih,
      advance_simulation cfg payload _ _ (SPI.Transaction.run_tx cfg payload _ n)]
    rfl
    done

def execute (cfg : Config) (payload : BitVec 16) (incoming : Nat → Inputs) (cycle : Nat) :
    Engine.Reactive.State 255 15 :=
  Engine.Reactive.run (program cfg payload) (Engine.Reactive.start (program cfg payload) (incoming 0)) incoming cycle

theorem waveform_correct (cfg : Config) (payload : BitVec 16) (incoming : Nat → Inputs) (cycle : Nat) :
    (execute cfg payload incoming cycle).pins =
      Pins.pushPull (Compile.SPI.encodePins (SPI.Transaction.expectedPins cfg payload cycle)) := by
  simp [execute, run_simulation, liftState, SPI.Transaction.waveform_correct]
  done

theorem samples_correct (cfg : Config) (payload : BitVec 16) (incoming : Nat → Inputs) (cycle : Nat) :
    (execute cfg payload incoming cycle).samples =
      SPI.Transaction.expectedSamples cfg (fun t => (incoming t)[0]) cycle := by
  simp [execute, run_simulation, liftState, SPI.Transaction.run_samples]
  done

theorem completed_result (cfg : Config) (payload : BitVec 16) (incoming : Nat → Inputs)
    (cycle : Nat) (h : cfg.transferCycles ≤ cycle) :
    (execute cfg payload incoming cycle).control = .stopped .completed ∧
    Engine.Reactive.busy (execute cfg payload incoming cycle) = false ∧
    Engine.Reactive.result (execute cfg payload incoming cycle) =
      some (SPI.Transaction.completeSamples cfg (fun t => (incoming t)[0])) := by
  have hc := SPI.Transaction.run_control cfg payload (fun t => (incoming t)[0]) cycle
  simp only [SPI.Transaction.ControlRep, Nat.not_lt.mpr h, if_false] at hc
  simp [execute, run_simulation, liftState, hc, busy, result,
    SPI.Transaction.samples_complete cfg payload (fun t => (incoming t)[0]) cycle h]
  done

/-- The image contains at most thirty-three timed actions and one halt. -/
theorem position_bound (cfg : Config) (payload : BitVec 16) : (program cfg payload).last.val + 1 ≤ 34 := by
  have := SPI.Transaction.phases_bound cfg
  exact Nat.add_le_add_right this 1

/-- Canonical record decoding recovers every compiled instruction, including unused halt slots. -/
theorem decoded_agrees (cfg : Config) (payload : BitVec 16) :
    Fetch.Agrees (Hardware.Execution.directStore (Hardware.Execution.imageWords (program cfg payload))
      (program cfg payload).idle (program cfg payload).last) (program cfg payload) :=
  Hardware.Execution.direct_agrees (program cfg payload)

theorem decoded_run (cfg : Config) (payload : BitVec 16) (incoming : Nat → Inputs) (cycle : Nat) :
    Fetch.run (Hardware.Execution.directStore (Hardware.Execution.imageWords (program cfg payload))
      (program cfg payload).idle (program cfg payload).last)
      (Engine.Reactive.start (program cfg payload) (incoming 0)) incoming cycle =
      liftState cfg (SPI.Transaction.run cfg payload (fun t => (incoming t)[0]) cycle) :=
  (Fetch.run_eq _ _ (decoded_agrees cfg payload) _ _ _).trans (run_simulation cfg payload incoming cycle)

end Pinwheel.Compile.SPITransaction
