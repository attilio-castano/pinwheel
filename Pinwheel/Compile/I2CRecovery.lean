import Pinwheel.I2C.Recovery
import Pinwheel.Compile.I2C
import Pinwheel.Hardware.Execution.Images

namespace Pinwheel.Compile.I2CRecovery
open Engine.Reactive
abbrev Config := Pinwheel.I2C.Config
abbrev ModelState := Pinwheel.I2C.Recovery.State
abbrev RecoveryProgram := Hardware.Execution.Image
abbrev RecoveryState := State 255 15
abbrev RecoveryInstruction := Instruction 255 15

def pulsePC (pulse : Fin 9) (phase : Fin 3) : Fin 256 :=
  ⟨1 + 3 * pulse.val + phase.val, by omega⟩

def pulseInstruction (cfg : Config) (pulse : Fin 9) (phase : Fin 3) : RecoveryInstruction :=
  match phase.val with
  | 0 => .action ⟨.openDrain 1, cfg.phaseMinusOne, none⟩
  | 1 => .wait ⟨{}, ⟨0, true⟩, cfg.waitMinusOne⟩
  | _ => .checked ⟨⟨{}, cfg.phaseMinusOne, none⟩, I2C.clockHigh,
      if pulse.val == 8 then some ⟨1, 0⟩ else none,
      if pulse.val == 8 then .branch 0 28 29 else .sequential⟩

def instruction (cfg : Config) (pc : Fin 256) : RecoveryInstruction :=
  if pc.val == 0 then .qualify ⟨{}, I2C.clockHigh, cfg.phaseMinusOne, cfg.waitMinusOne⟩
  else if h : pc.val < 28 then
    pulseInstruction cfg ⟨(pc.val - 1) / 3, by omega⟩ ⟨(pc.val - 1) % 3, by omega⟩
  else if pc.val == 28 then .qualify ⟨{}, I2C.bothHigh, cfg.phaseMinusOne, cfg.waitMinusOne⟩
  else .halt

def program (cfg : Config) : RecoveryProgram :=
  ⟨Vector.ofFn (instruction cfg), {}, 29⟩

def result (s : RecoveryState) : Option Pinwheel.I2C.Recovery.Outcome :=
  match s.control with
  | .stopped .completed => some (Pinwheel.I2C.Recovery.outcome s.samples)
  | .stopped .timeout => some .timeout
  | .stopped .fault => some .busFault
  | _ => none

def control (s : ModelState) : Control 255 :=
  match s.phase with
  | .clockFree => .qualifying 0 s.remaining s.waitLeft
  | .low pulse => .active (pulsePC pulse 0) s.remaining
  | .rise pulse => .waiting (pulsePC pulse 1) s.waitLeft
  | .high pulse => .checked (pulsePC pulse 2) s.remaining
  | .released => .qualifying 28 s.remaining s.waitLeft
  | .finished => .stopped .completed
  | .timeout => .stopped .timeout
  | .fault => .stopped .fault

def lift (s : ModelState) : RecoveryState :=
  ⟨control s, I2C.encodePins (Pinwheel.I2C.Recovery.pins s.phase), s.samples⟩

end Pinwheel.Compile.I2CRecovery
