import Pinwheel.Engine.Proofs
import Pinwheel.UART.Tx

namespace Pinwheel.Compile.UART

open Pinwheel

def encodePin (pin : Bool) : Engine.Levels := BitVec.ofBoolListBE [true, false, pin]

def action (cfg : UART.Config) (byte : BitVec 8) (symbol : Fin 10) : Engine.Action :=
  { levels := encodePin (if symbol.val = 0 then false
      else if symbol.val = 9 then true else byte.getLsbD (symbol.val - 1))
    durationMinusOne := cfg.durationMinusOne }

def program (cfg : UART.Config) (byte : BitVec 8) : Engine.Program :=
  { memory := Vector.ofFn fun pc =>
      if h : pc.val < 10 then .action (action cfg byte ⟨pc.val, h⟩) else .halt
    idle := 5 }

def liftState (cfg : UART.Config) (s : UART.State cfg) : Engine.State :=
  { control := match s with
      | .idle => .stopped .completed
      | .active _ symbol tick =>
        .active ⟨symbol.val, by omega⟩ ⟨cfg.durationMinusOne.val - tick.val, by omega⟩
    levels := encodePin (UART.pin s)
    samples := Vector.replicate 8 false }

def matchesByte (byte : BitVec 8) : UART.State cfg → Prop
  | .idle => True
  | .active tx _ _ => tx = byte

theorem advance_simulation (cfg : UART.Config) (byte : BitVec 8) (s : UART.State cfg)
    (input : Bool) (h : matchesByte byte s) :
    Engine.advance (program cfg byte) (liftState cfg s) input = liftState cfg (UART.advance s) := by
  cases s with
  | idle => rfl
  | active tx symbol tick =>
    change tx = byte at h
    cases h
    have duration : cfg.cycles = cfg.durationMinusOne.val + 1 := rfl
    by_cases ht : tick.val + 1 < cfg.cycles
    · have remaining : 0 < cfg.durationMinusOne.val - tick.val := by omega
      simp [Engine.advance, liftState, UART.advance, ht, remaining, UART.pin, Nat.sub_sub]

    · have endTick : tick.val = cfg.durationMinusOne.val := by omega
      simp [Engine.advance, liftState, UART.advance, endTick, duration]
      by_cases hs : symbol.val + 1 < 10
      all_goals simp [Engine.next, Engine.enter, program, Engine.Program.fetch, action,
        UART.pin, Engine.capture, hs, show symbol.val + 1 < 32 by omega]
      all_goals first | rfl | grind

theorem run_matches (cfg : UART.Config) (byte : BitVec 8) (cycle : Nat) :
    matchesByte byte (UART.run (UART.initial cfg byte) cycle) := by
  have h := UART.run_represents cfg byte cycle
  grind [UART.Represents, matchesByte]

theorem start_simulation (cfg : UART.Config) (byte : BitVec 8) (input : Bool) :
    Engine.start (program cfg byte) input = liftState cfg (UART.initial cfg byte) := by
  simp [Engine.start, Engine.enter, program, Engine.Program.fetch, action,
    liftState, UART.initial, UART.pin, Engine.capture]
  grind

theorem run_simulation (cfg : UART.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    Engine.run (program cfg byte) (Engine.start (program cfg byte) (incoming 0)) incoming cycle =
      liftState cfg (UART.run (UART.initial cfg byte) cycle) := by
  induction cycle with
  | zero => exact start_simulation cfg byte (incoming 0)
  | succ n ih =>
    rw [Engine.run, ih, advance_simulation cfg byte _ _ (run_matches cfg byte n)]
    rfl

def execute (cfg : UART.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) : Engine.State :=
  Engine.run (program cfg byte) (Engine.start (program cfg byte) (incoming 0)) incoming cycle

theorem waveform_correct (cfg : UART.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    (execute cfg byte incoming cycle).levels = encodePin (UART.expected cfg byte cycle) := by
  simp [execute, run_simulation, liftState, Pinwheel.UART.waveform_correct]

theorem samples_empty (cfg : UART.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    (execute cfg byte incoming cycle).samples = Vector.replicate 8 false := by
  simp [execute, run_simulation, liftState]

theorem busy_lift (cfg : UART.Config) (s : UART.State cfg) :
    Engine.busy (liftState cfg s) = UART.busy s := by
  cases s
  all_goals rfl

theorem busy_exact (cfg : UART.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    Engine.busy (execute cfg byte incoming cycle) = decide (cycle < cfg.frameCycles) := by
  simp [execute, run_simulation, busy_lift, Pinwheel.UART.busy_exact]

theorem result_lift (cfg : UART.Config) (s : UART.State cfg) :
    Engine.result (liftState cfg s) = if UART.busy s then none else some (Vector.replicate 8 false) := by
  cases s
  all_goals rfl

theorem result_exact (cfg : UART.Config) (byte : BitVec 8) (incoming : Nat → Bool) (cycle : Nat) :
    Engine.result (execute cfg byte incoming cycle) =
      if cycle < cfg.frameCycles then none else some (Vector.replicate 8 false) := by
  simp [execute, run_simulation, result_lift, Pinwheel.UART.busy_exact]

end Pinwheel.Compile.UART
