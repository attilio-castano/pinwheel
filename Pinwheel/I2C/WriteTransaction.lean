import Pinwheel.I2C.Spec

/-! One or two payload bytes after a seven-bit write address. The digital reference
retains the four-phase clock contract, bounded stretching, and guarded high phases.
ACK flags are independent: destinations zero, one, and two correspond to the address
and the two payload bytes. A one-byte request never executes the third byte. -/
namespace Pinwheel.I2C.WriteTransaction

structure Request where
  address : Fin 128
  countMinusOne : Fin 2
  payload : BitVec 16
  deriving DecidableEq, Repr

def Request.payloadCount (r : Request) : Nat := r.countMinusOne.val + 1

/-- The high byte is first in a two-byte request; a one-byte request uses the low byte. -/
def payloadByte (r : Request) (index : Fin 2) : BitVec 8 :=
  if r.countMinusOne.val == 0 then r.payload.extractLsb' 0 8
  else if index.val == 0 then r.payload.extractLsb' 8 8
  else r.payload.extractLsb' 0 8

def wireByte (r : Request) (index : Fin 3) : BitVec 8 :=
  if index.val == 0 then BitVec.ofNat 8 (r.address.val * 2)
  else payloadByte r ⟨index.val - 1, by omega⟩

inductive Outcome where
  | success | addressNack | payload1Nack | payload2Nack | timeout | busFault
  deriving DecidableEq, Repr

inductive Phase where
  | free | startHold
  | setup (slot : Fin 27) | rise (slot : Fin 27) | high (slot : Fin 27) | fall (slot : Fin 27)
  | stopLow | stopRise | stopHigh | stopFree
  | finished | timeout | fault
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  remaining : Fin 256
  waitLeft : Fin 256
  samples : Vector Bool 16
  deriving DecidableEq, Repr

def initial (cfg : Config) : State :=
  ⟨.free, cfg.phaseMinusOne, cfg.waitMinusOne, Vector.replicate 16 false⟩

/-- MSB-first transmitted bytes; the ninth clock releases SDA for the target ACK. -/
def releaseData (r : Request) (slot : Fin 27) : Bool :=
  if slot.val % 9 == 8 then true
  else (wireByte r ⟨slot.val / 9, by omega⟩).getLsbD (7 - slot.val % 9)

def dataDrive (r : Request) (slot : Fin 27) : Drive :=
  if releaseData r slot then .release else .low

def pins (r : Request) (phase : Phase) : Pins :=
  match phase with
  | .startHold | .stopRise | .stopHigh => ⟨.release, .low⟩
  | .setup slot | .fall slot => ⟨.low, dataDrive r slot⟩
  | .rise slot | .high slot => ⟨.release, dataDrive r slot⟩
  | .stopLow => ⟨.low, .low⟩
  | _ => {}

def sampleAt (slot : Fin 27) : Option (Fin 16) :=
  if slot.val == 8 then some 0
  else if slot.val == 17 then some 1
  else if slot.val == 26 then some 2
  else none

def latch (samples : Vector Bool 16) (slot : Fin 27) (sda : Bool) : Vector Bool 16 :=
  match sampleAt slot with
  | none => samples
  | some k => samples.set k sda

def afterFall (r : Request) (samples : Vector Bool 16) (slot : Fin 27) : Phase :=
  if (slot.val == 8 && samples[0]) || (slot.val == 17 && samples[1]) ||
      (slot.val == 26 && samples[2]) then .stopLow
  else if slot.val == 17 && r.countMinusOne.val == 0 then .stopLow
  else if h : slot.val + 1 < 27 then .setup ⟨slot.val + 1, h⟩
  else .stopLow

def move (cfg : Config) (s : State) (phase : Phase) : State :=
  {s with phase, remaining := cfg.phaseMinusOne, waitLeft := cfg.waitMinusOne}

def count (s : State) : State := {s with remaining := ⟨s.remaining.val - 1, by omega⟩}
def finish (s : State) (phase : Phase) : State := {s with phase, remaining := 0, waitLeft := 0}
def blocked (cfg : Config) (s : State) : State :=
  if h : 0 < s.waitLeft.val then
    {s with remaining := cfg.phaseMinusOne, waitLeft := ⟨s.waitLeft.val - 1, by omega⟩}
  else finish s .timeout

def timed (cfg : Config) (s : State) (next : Phase) : State :=
  if s.remaining.val == 0 then move cfg s next else count s

def guarded (cfg : Config) (s : State) (ready : Bool) (next : Phase) : State :=
  if ready then timed cfg s next else finish s .fault

def step (cfg : Config) (r : Request) (s : State) (bus : Bus) : State :=
  match s.phase with
  | .finished | .timeout | .fault => s
  | .free => if bus.scl && bus.sda then
      if s.remaining.val == 0 then move cfg s .startHold
      else {count s with waitLeft := cfg.waitMinusOne}
    else blocked cfg s
  | .startHold => guarded cfg s bus.scl (.setup 0)
  | .setup slot => timed cfg s (.rise slot)
  | .rise slot => if bus.scl then move cfg s (.high slot) else blocked cfg s
  | .high slot => if !bus.scl then finish s .fault
    else if s.remaining.val == 0 then move cfg {s with samples := latch s.samples slot bus.sda} (.fall slot)
    else count s
  | .fall slot => timed cfg s (afterFall r s.samples slot)
  | .stopLow => timed cfg s .stopRise
  | .stopRise => if bus.scl then move cfg s .stopHigh else blocked cfg s
  | .stopHigh => guarded cfg s bus.scl .stopFree
  -- The qualified interval tolerates registered observations of our own previous low SDA.
  | .stopFree => if bus.scl && bus.sda then
      if s.remaining.val == 0 then move cfg s .finished
      else {count s with waitLeft := cfg.waitMinusOne}
    else blocked cfg s

def outcome (r : Request) (samples : Vector Bool 16) : Outcome :=
  if samples[0] then .addressNack else if samples[1] then .payload1Nack
  else if r.countMinusOne.val != 0 && samples[2] then .payload2Nack else .success

def result (r : Request) (s : State) : Option Outcome :=
  match s.phase with
  | .finished => some (outcome r s.samples)
  | .timeout => some .timeout
  | .fault => some .busFault
  | _ => none

def run (cfg : Config) (r : Request) (s : State) (incoming : Nat → Bus) : Nat → State
  | 0 => s
  | n + 1 => step cfg r (run cfg r s incoming n) (incoming (n + 1))

end Pinwheel.I2C.WriteTransaction
