import Pinwheel.Engine.Reactive
import Pinwheel.I2C.Proofs

namespace Pinwheel.Compile.I2C
open Engine.Reactive

def encodeInputs (bus : Pinwheel.I2C.Bus) : Inputs :=
  BitVec.ofNat 2 ((if bus.scl then 1 else 0) + (if bus.sda then 2 else 0))

def encodePins (pins : Pinwheel.I2C.Pins) : Pins :=
  Pins.openDrain (BitVec.ofNat 3
    ((if pins.scl == .low then 1 else 0) + (if pins.sda == .low then 2 else 0)))

def clockHigh : Check := ⟨1, 1⟩
def bothHigh : Check := ⟨3, 3⟩
def unguarded : Check := ⟨0, 0⟩

def bitPins (r : Pinwheel.I2C.Request) (slot : Fin 18) (clockLow : Bool) : Pins :=
  encodePins ⟨if clockLow then .low else .release,
    if Pinwheel.I2C.releaseData r slot then .release else .low⟩

def ackCapture (slot : Fin 18) : Option Capture :=
  if slot.val == 8 then some ⟨1, 0⟩ else if slot.val == 17 then some ⟨1, 1⟩ else none

def fallFinish (slot : Fin 18) : Finish :=
  if slot.val == 8 then .branch 0 74 38 else .sequential

def bitInstruction (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request)
    (slot : Fin 18) (phase : Nat) : Instruction :=
  match phase with
  | 0 => .action ⟨bitPins r slot true, cfg.phaseMinusOne, none⟩
  | 1 => .wait ⟨bitPins r slot false, ⟨0, true⟩, cfg.waitMinusOne⟩
  | 2 => .checked ⟨⟨bitPins r slot false, cfg.phaseMinusOne, none⟩, clockHigh, ackCapture slot, .sequential⟩
  | _ => .checked ⟨⟨bitPins r slot true, cfg.phaseMinusOne, none⟩, unguarded, none, fallFinish slot⟩

/-- 79 populated slots, including halt. Payload bits remain literals in the program. -/
def instruction (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request) (pc : Fin 128) : Instruction :=
  if pc.val == 0 then .qualify ⟨{}, bothHigh, cfg.phaseMinusOne, cfg.waitMinusOne⟩
  else if pc.val == 1 then .checked ⟨⟨.openDrain 2, cfg.phaseMinusOne, none⟩, clockHigh, none, .sequential⟩
  else if h : pc.val < 74 then
    bitInstruction cfg r ⟨(pc.val - 2) / 4, by omega⟩ ((pc.val - 2) % 4)
  else if pc.val == 74 then .action ⟨.openDrain 3, cfg.phaseMinusOne, none⟩
  else if pc.val == 75 then .wait ⟨.openDrain 2, ⟨0, true⟩, cfg.waitMinusOne⟩
  else if pc.val == 76 then .checked ⟨⟨.openDrain 2, cfg.phaseMinusOne, none⟩, clockHigh, none, .sequential⟩
  else if pc.val == 77 then .qualify ⟨{}, bothHigh, cfg.phaseMinusOne, cfg.waitMinusOne⟩
  else .halt

def program (cfg : Pinwheel.I2C.Config) (r : Pinwheel.I2C.Request) : Program :=
  ⟨Vector.ofFn (instruction cfg r), {}, 78⟩

def outcome (s : State) : Option Pinwheel.I2C.Outcome :=
  match s.control with
  | .stopped .completed => some (if s.samples[0] then .addressNack
      else if s.samples[1] then .dataNack else .success)
  | .stopped .timeout => some .timeout
  | .stopped .fault => some .busFault
  | _ => none

end Pinwheel.Compile.I2C
