import Pinwheel.I2C.RegisterReadTransaction
import Pinwheel.Compile.I2C
import Pinwheel.Hardware.Execution.Images

namespace Pinwheel.Compile.I2CReadTransaction
open Engine.Reactive

abbrev ReadProgram := Program 255 15
abbrev ReadState := State 255 15
abbrev ReadInstruction := Instruction 255 15

def bitPC (slot : Fin 45) (phase : Fin 4) : Fin 256 :=
  ⟨2 + 4 * slot.val + (if slot.val < 18 then 0 else 4) + phase.val, by split <;> omega⟩

def bitPins (r : Pinwheel.I2C.RegisterReadTransaction.Request) (slot : Fin 45) (low : Bool) : Pins :=
  I2C.encodePins ⟨if low then .low else .release,
    Pinwheel.I2C.RegisterReadTransaction.dataDrive r slot⟩

def fallFinish (r : Pinwheel.I2C.RegisterReadTransaction.Request) (slot : Fin 45) : Finish 255 15 :=
  if slot.val == 8 then .branch 0 191 38
  else if slot.val == 17 then .branch 1 191 74
  else if slot.val == 26 then .branch 2 191 114
  else if slot.val == 35 then .jump (if r.countMinusOne.val == 0 then 186 else 150)
  else .sequential

def bitInstruction (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (slot : Fin 45) (phase : Nat) : ReadInstruction :=
  match phase with
  | 0 => .action ⟨bitPins r slot true, cfg.phaseMinusOne, none⟩
  | 1 => .wait ⟨bitPins r slot false, ⟨0, true⟩, cfg.waitMinusOne⟩
  | 2 => .checked ⟨⟨bitPins r slot false, cfg.phaseMinusOne, none⟩, I2C.clockHigh,
      (Pinwheel.I2C.RegisterReadTransaction.sampleAt slot).map (⟨1, ·⟩), .sequential⟩
  | _ => .checked ⟨⟨bitPins r slot true, cfg.phaseMinusOne, none⟩, I2C.unguarded, none, fallFinish r slot⟩

def stopInstruction (cfg : Pinwheel.I2C.Config) (offset : Nat) : ReadInstruction :=
  match offset with
  | 0 => .action ⟨.openDrain 3, cfg.phaseMinusOne, none⟩
  | 1 => .wait ⟨.openDrain 2, ⟨0, true⟩, cfg.waitMinusOne⟩
  | 2 => .checked ⟨⟨.openDrain 2, cfg.phaseMinusOne, none⟩, I2C.clockHigh, none, .sequential⟩
  | _ => .qualify ⟨{}, I2C.bothHigh, cfg.phaseMinusOne, cfg.waitMinusOne⟩

def instruction (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request)
    (pc : Fin 256) : ReadInstruction :=
  if pc.val == 0 then .qualify ⟨{}, I2C.bothHigh, cfg.phaseMinusOne, cfg.waitMinusOne⟩
  else if pc.val == 1 then .checked ⟨⟨.openDrain 2, cfg.phaseMinusOne, none⟩, I2C.clockHigh, none, .sequential⟩
  else if h : pc.val < 74 then bitInstruction cfg r ⟨(pc.val - 2) / 4, by omega⟩ ((pc.val - 2) % 4)
  else if pc.val == 74 then .action ⟨.openDrain 1, cfg.phaseMinusOne, none⟩
  else if pc.val == 75 then .wait ⟨{}, ⟨0, true⟩, cfg.waitMinusOne⟩
  else if pc.val == 76 then .checked ⟨⟨{}, cfg.phaseMinusOne, none⟩, I2C.bothHigh, none, .sequential⟩
  else if pc.val == 77 then .checked ⟨⟨.openDrain 2, cfg.phaseMinusOne, none⟩, I2C.clockHigh, none, .sequential⟩
  else if h : pc.val < 186 then bitInstruction cfg r ⟨(pc.val - 6) / 4, by omega⟩ ((pc.val - 6) % 4)
  else if pc.val < 190 then stopInstruction cfg (pc.val - 186)
  else if pc.val == 190 then .halt
  else if pc.val < 195 then stopInstruction cfg (pc.val - 191)
  else if pc.val == 195 then .action ⟨{}, 0, none⟩
  else .halt

def program (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request) : ReadProgram :=
  ⟨Vector.ofFn (instruction cfg r), {}, 195⟩

def result (r : Pinwheel.I2C.RegisterReadTransaction.Request) (s : ReadState) :
    Option Pinwheel.I2C.RegisterReadTransaction.Outcome :=
  match s.control with
  | .stopped .completed => some (.success (Pinwheel.I2C.RegisterReadTransaction.received r s.samples))
  | .stopped .timeout => some .timeout
  | .stopped .fault => some .nackOrBusFault
  | _ => none

theorem position_bound (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request) :
    (program cfg r).last.val + 1 = 196 := rfl

theorem decoded_agrees (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.RegisterReadTransaction.Request) :
    Fetch.Agrees (Hardware.Execution.directStore (Hardware.Execution.imageWords (program cfg r))
      (program cfg r).idle (program cfg r).last) (program cfg r) :=
  Hardware.Execution.direct_agrees (program cfg r)

end Pinwheel.Compile.I2CReadTransaction
