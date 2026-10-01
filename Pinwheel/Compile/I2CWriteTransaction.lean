import Pinwheel.I2C.WriteTransaction
import Pinwheel.Compile.I2C
import Pinwheel.Hardware.Execution.Images

namespace Pinwheel.Compile.I2CWriteTransaction
open Engine.Reactive

abbrev WriteProgram := Program 255 15
abbrev WriteState := State 255 15
abbrev WriteInstruction := Instruction 255 15

def bitPC (slot : Fin 27) (phase : Fin 4) : Fin 256 :=
  ⟨2 + 4 * slot.val + phase.val, by omega⟩

def bitPins (r : Pinwheel.I2C.WriteTransaction.Request) (slot : Fin 27) (low : Bool) : Pins :=
  I2C.encodePins ⟨if low then .low else .release,
    Pinwheel.I2C.WriteTransaction.dataDrive r slot⟩

def fallFinish (r : Pinwheel.I2C.WriteTransaction.Request) (slot : Fin 27) : Finish 255 15 :=
  if slot.val == 8 then .branch 0 110 38
  else if slot.val == 17 then .branch 1 110 (if r.countMinusOne.val == 0 then 110 else 74)
  else .sequential

def bitInstruction (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (slot : Fin 27) (phase : Nat) : WriteInstruction :=
  match phase with
  | 0 => .action ⟨bitPins r slot true, cfg.phaseMinusOne, none⟩
  | 1 => .wait ⟨bitPins r slot false, ⟨0, true⟩, cfg.waitMinusOne⟩
  | 2 => .checked ⟨⟨bitPins r slot false, cfg.phaseMinusOne, none⟩, I2C.clockHigh,
      (Pinwheel.I2C.WriteTransaction.sampleAt slot).map (⟨1, ·⟩), .sequential⟩
  | _ => .checked ⟨⟨bitPins r slot true, cfg.phaseMinusOne, none⟩, I2C.unguarded, none, fallFinish r slot⟩

def instruction (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request)
    (pc : Fin 256) : WriteInstruction :=
  if pc.val == 0 then .qualify ⟨{}, I2C.bothHigh, cfg.phaseMinusOne, cfg.waitMinusOne⟩
  else if pc.val == 1 then .checked ⟨⟨.openDrain 2, cfg.phaseMinusOne, none⟩, I2C.clockHigh, none, .sequential⟩
  else if h : pc.val < 110 then bitInstruction cfg r ⟨(pc.val - 2) / 4, by omega⟩ ((pc.val - 2) % 4)
  else if pc.val == 110 then .action ⟨.openDrain 3, cfg.phaseMinusOne, none⟩
  else if pc.val == 111 then .wait ⟨.openDrain 2, ⟨0, true⟩, cfg.waitMinusOne⟩
  else if pc.val == 112 then .checked ⟨⟨.openDrain 2, cfg.phaseMinusOne, none⟩, I2C.clockHigh, none, .sequential⟩
  else if pc.val == 113 then .qualify ⟨{}, I2C.bothHigh, cfg.phaseMinusOne, cfg.waitMinusOne⟩
  else .halt

def program (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request) : WriteProgram :=
  ⟨Vector.ofFn (instruction cfg r), {}, 114⟩

def result (r : Pinwheel.I2C.WriteTransaction.Request) (s : WriteState) :
    Option Pinwheel.I2C.WriteTransaction.Outcome :=
  match s.control with
  | .stopped .completed => some (Pinwheel.I2C.WriteTransaction.outcome r s.samples)
  | .stopped .timeout => some .timeout
  | .stopped .fault => some .busFault
  | _ => none

theorem position_bound (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request) :
    (program cfg r).last.val + 1 = 115 := rfl

/-- All canonical records decode back to the compiled instructions, including unused halts. -/
theorem decoded_agrees (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.WriteTransaction.Request) :
    Fetch.Agrees (Hardware.Execution.directStore (Hardware.Execution.imageWords (program cfg r))
      (program cfg r).idle (program cfg r).last) (program cfg r) :=
  Hardware.Execution.direct_agrees (program cfg r)

end Pinwheel.Compile.I2CWriteTransaction
