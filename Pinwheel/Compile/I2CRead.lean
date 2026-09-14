import Pinwheel.I2C.RegisterRead
import Pinwheel.Compile.I2C

namespace Pinwheel.Compile.I2CRead
open Engine.Reactive

abbrev ReadProgram := Program 255 15
abbrev ReadState := State 255 15
abbrev ReadInstruction := Instruction 255 15

/-- Preserve the four-phase bit contract, inserting four repeated-START phases after byte two. -/
def bitPC (slot : Fin 36) (phase : Fin 4) : Fin 256 :=
  ⟨2 + 4 * slot.val + (if slot.val < 18 then 0 else 4) + phase.val, by split <;> omega⟩

def bitPins (r : Pinwheel.I2C.RegisterRead.Request) (slot : Fin 36) (low : Bool) : Pins :=
  I2C.encodePins ⟨if low then .low else .release,
    Pinwheel.I2C.RegisterRead.dataDrive r slot⟩

def fallFinish (slot : Fin 36) : Finish 255 15 :=
  if slot.val == 8 then .branch 8 150 38
  else if slot.val == 17 then .branch 9 150 74
  else if slot.val == 26 then .branch 10 150 114
  else .sequential

def bitInstruction (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request)
    (slot : Fin 36) (phase : Nat) : ReadInstruction :=
  match phase with
  | 0 => .action ⟨bitPins r slot true, cfg.phaseMinusOne, none⟩
  | 1 => .wait ⟨bitPins r slot false, ⟨0, true⟩, cfg.waitMinusOne⟩
  | 2 => .checked ⟨⟨bitPins r slot false, cfg.phaseMinusOne, none⟩, I2C.clockHigh,
      (Pinwheel.I2C.RegisterRead.sampleAt slot).map (⟨1, ·⟩), .sequential⟩
  | _ => .checked ⟨⟨bitPins r slot true, cfg.phaseMinusOne, none⟩, I2C.unguarded, none, fallFinish slot⟩

def instruction (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request) (pc : Fin 256) : ReadInstruction :=
  if pc.val == 0 then .qualify ⟨{}, I2C.bothHigh, cfg.phaseMinusOne, cfg.waitMinusOne⟩
  else if pc.val == 1 then .checked ⟨⟨.openDrain 2, cfg.phaseMinusOne, none⟩, I2C.clockHigh, none, .sequential⟩
  else if h : pc.val < 74 then bitInstruction cfg r ⟨(pc.val - 2) / 4, by omega⟩ ((pc.val - 2) % 4)
  else if pc.val == 74 then .action ⟨.openDrain 1, cfg.phaseMinusOne, none⟩
  else if pc.val == 75 then .wait ⟨{}, ⟨0, true⟩, cfg.waitMinusOne⟩
  else if pc.val == 76 then .checked ⟨⟨{}, cfg.phaseMinusOne, none⟩, I2C.bothHigh, none, .sequential⟩
  else if pc.val == 77 then .checked ⟨⟨.openDrain 2, cfg.phaseMinusOne, none⟩, I2C.clockHigh, none, .sequential⟩
  else if h : pc.val < 150 then bitInstruction cfg r ⟨(pc.val - 6) / 4, by omega⟩ ((pc.val - 6) % 4)
  else if pc.val == 150 then .action ⟨.openDrain 3, cfg.phaseMinusOne, none⟩
  else if pc.val == 151 then .wait ⟨.openDrain 2, ⟨0, true⟩, cfg.waitMinusOne⟩
  else if pc.val == 152 then .checked ⟨⟨.openDrain 2, cfg.phaseMinusOne, none⟩, I2C.clockHigh, none, .sequential⟩
  else if pc.val == 153 then .checked ⟨⟨{}, cfg.phaseMinusOne, none⟩, I2C.bothHigh, none, .sequential⟩
  else .halt

def program (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterRead.Request) : ReadProgram :=
  ⟨Vector.ofFn (instruction cfg r), {}, 154⟩

def result (s : ReadState) : Option Pinwheel.I2C.RegisterRead.Outcome :=
  match s.control with
  | .stopped .completed => some (Pinwheel.I2C.RegisterRead.outcome s.samples)
  | .stopped .timeout => some .timeout
  | .stopped .fault => some .busFault
  | _ => none

end Pinwheel.Compile.I2CRead
