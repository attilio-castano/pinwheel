import Pinwheel.Engine.Reactive
import Pinwheel.Compile.UART
import Pinwheel.Compile.SPI

namespace Pinwheel.Engine.Reactive

def embedStop : Engine.Stop → Stop
  | .ready => .ready
  | .completed => .completed
  | .fault => .fault

def embedPC (pc : Fin 32) : Fin 128 := ⟨pc.val, by omega⟩

def embedControl : Engine.Control → Control
  | .stopped reason => .stopped (embedStop reason)
  | .active pc remaining => .active (embedPC pc) remaining

def embedState (s : Engine.State) : State :=
  ⟨embedControl s.control, .pushPull s.levels, s.samples⟩

def embedCapture (c : Option (Fin 8)) : Option Capture := c.map (⟨0, ·⟩)

def embedInstruction : Engine.Instruction → Instruction
  | .halt => .halt
  | .action a => .action ⟨.pushPull a.levels, a.durationMinusOne, embedCapture a.capture⟩

def embedProgram (p : Engine.Program) : Program :=
  ⟨Vector.ofFn (fun pc => if h : pc.val < 32 then embedInstruction p.memory[pc.val] else .halt),
    .pushPull p.idle, 31⟩

def embedMachine (m : Engine.Machine) : Machine := ⟨embedProgram m.program, embedState m.state⟩

theorem capture_compatibility (slots : Samples) (c : Option (Fin 8)) (inputs : Inputs) :
    capture slots (embedCapture c) inputs = Engine.capture slots c inputs[0] := by
  cases c <;> simp [capture, embedCapture, Engine.capture]
  done

theorem enter_compatibility (p : Engine.Program) (pc : Fin 32) (slots : Samples) (inputs : Inputs) :
    enter (embedProgram p) (embedPC pc) slots inputs = embedState (Engine.enter p pc slots inputs[0]) := by
  cases h : p.memory[pc.val] <;> simp [enter, embedProgram, Program.fetch, Engine.enter,
    Engine.Program.fetch, h, embedInstruction, embedState, embedControl, embedStop,
    stop, capture_compatibility, embedPC]
  done

theorem next_compatibility (p : Engine.Program) (pc : Fin 32) (slots : Samples) (inputs : Inputs) :
    next (embedProgram p) (embedPC pc) slots inputs = embedState (Engine.next p pc slots inputs[0]) := by
  simp only [next, Engine.next, show (embedPC pc).val = pc.val from rfl,
    show (embedProgram p).last.val = 31 from rfl]
  by_cases h : pc.val + 1 < 32 <;>
    simp only [show (pc.val < 31) ↔ (pc.val + 1 < 32) by omega, h, dite_true, dite_false]
  case pos => exact enter_compatibility p ⟨pc.val + 1, h⟩ slots inputs
  case neg => rfl
  done

theorem advance_compatibility (p : Engine.Program) (s : Engine.State) (inputs : Inputs) :
    advance (embedProgram p) (embedState s) inputs =
      embedState (Engine.advance p s inputs[0]) := by
  cases s with
  | mk control levels samples =>
    cases control <;> simp only [embedState, embedControl, advance, Engine.advance]
    all_goals split <;> simp_all [next_compatibility, embedState, embedControl]
  done

theorem busy_compatibility (s : Engine.State) : busy (embedState s) = Engine.busy s := by
  cases h : s.control <;> simp [busy, Engine.busy, embedState, embedControl, h]
  done

theorem result_compatibility (s : Engine.State) : result (embedState s) = Engine.result s := by
  cases h : s.control <;> simp [result, Engine.result, embedState, embedControl, h]
  case stopped reason => cases reason <;> rfl
  done

theorem reset_compatibility (p : Engine.Program) :
    reset (embedProgram p) = embedState (Engine.reset p) := rfl

theorem start_compatibility (p : Engine.Program) (inputs : Inputs) :
    start (embedProgram p) inputs = embedState (Engine.start p inputs[0]) := by
  exact enter_compatibility p 0 _ inputs

theorem step_compatibility (p : Engine.Program) (s : Engine.State)
    (resetRequested startRequested : Bool) (inputs : Inputs) :
    step (embedProgram p) (embedState s) resetRequested startRequested inputs =
      embedState (Engine.step p s resetRequested startRequested inputs[0]) := by
  cases resetRequested <;> cases startRequested <;> cases h : Engine.busy s <;>
    simp [step, Engine.step, busy_compatibility, h, reset_compatibility,
      start_compatibility, advance_compatibility]
  done

theorem run_compatibility (p : Engine.Program) (s : Engine.State)
    (incoming : Nat → Inputs) (n : Nat) :
    run (embedProgram p) (embedState s) incoming n =
      embedState (Engine.run p s (fun t => (incoming t)[0]) n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, Engine.run, ih, advance_compatibility]
  done

theorem load_compatibility (m : Engine.Machine) (p : Engine.Program) :
    load (embedMachine m) (embedProgram p) =
      (embedMachine (Engine.load m p).1, (Engine.load m p).2) := by
  cases h : Engine.busy m.state <;>
    simp [load, Engine.load, embedMachine, busy_compatibility, h, reset_compatibility]
  done

def executeLegacy (p : Engine.Program) (incoming : Nat → Inputs) (n : Nat) : State :=
  run (embedProgram p) (start (embedProgram p) (incoming 0)) incoming n

theorem execute_compatibility (p : Engine.Program) (incoming : Nat → Inputs) (n : Nat) :
    executeLegacy p incoming n =
      embedState (Engine.run p (Engine.start p (incoming 0)[0]) (fun t => (incoming t)[0]) n) := by
  simp only [executeLegacy, start_compatibility, run_compatibility]
  done

theorem uart_waveform (cfg : UART.Config) (byte : BitVec 8) (incoming : Nat → Inputs) (n : Nat) :
    (executeLegacy (Compile.UART.program cfg byte) incoming n).pins =
      Pins.pushPull (Compile.UART.encodePin (UART.expected cfg byte n)) := by
  simpa only [execute_compatibility, embedState, Compile.UART.execute] using
    congrArg Pins.pushPull (Compile.UART.waveform_correct cfg byte (fun t => (incoming t)[0]) n)
  done

theorem spi_waveform (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Inputs) (n : Nat) :
    (executeLegacy (Compile.SPI.program cfg byte) incoming n).pins =
      Pins.pushPull (Compile.SPI.encodePins (SPI.expectedPins cfg byte n)) := by
  simpa only [execute_compatibility, embedState, Compile.SPI.execute] using
    congrArg Pins.pushPull (Compile.SPI.waveform_correct cfg byte (fun t => (incoming t)[0]) n)
  done

theorem spi_samples (cfg : SPI.Config) (byte : BitVec 8) (incoming : Nat → Inputs) (n : Nat) :
    (executeLegacy (Compile.SPI.program cfg byte) incoming n).samples =
      SPI.expectedSamples cfg (fun t => (incoming t)[0]) n := by
  simpa only [execute_compatibility, embedState, Compile.SPI.execute] using
    Compile.SPI.samples_correct cfg byte (fun t => (incoming t)[0]) n
  done

end Pinwheel.Engine.Reactive
