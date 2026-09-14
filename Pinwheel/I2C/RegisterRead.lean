import Pinwheel.I2C.Spec

/-! Bounded combined transaction: write a register index, repeated START, read one byte.
The reference retains four phases per clock and treats the wire as an ideal digital bus. -/
namespace Pinwheel.I2C.RegisterRead

structure Request where
  address : Fin 128
  register : BitVec 8
  deriving DecidableEq, Repr

inductive Outcome where
  | success (byte : BitVec 8)
  | writeAddressNack | registerNack | readAddressNack | timeout | busFault
  deriving DecidableEq, Repr

inductive Phase where
  | free | startHold
  | setup (slot : Fin 36) | rise (slot : Fin 36) | high (slot : Fin 36) | fall (slot : Fin 36)
  | restartSetup | restartRise | restartHigh | restartHold
  | stopLow | stopRise | stopHigh | stopFree
  | finished | timeout | fault
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  remaining : Fin 256
  waitLeft : Fin 256
  samples : Vector Bool 16
  deriving DecidableEq, Repr

def initial (cfg : Config) : State := ⟨.free, cfg.phaseMinusOne, cfg.waitMinusOne, Vector.replicate 16 false⟩

/-- Three transmitted bytes; the final byte and its NACK are released by the controller. -/
def releaseData (r : Request) (slot : Fin 36) : Bool :=
  if slot.val < 8 then (r.address.val * 2).testBit (7 - slot.val)
  else if slot.val < 9 then true
  else if slot.val < 17 then r.register.getLsbD (16 - slot.val)
  else if slot.val < 18 then true
  else if slot.val < 26 then (r.address.val * 2 + 1).testBit (25 - slot.val)
  else true

def dataDrive (r : Request) (slot : Fin 36) : Drive :=
  if releaseData r slot then .release else .low

def pins (r : Request) (phase : Phase) : Pins :=
  match phase with
  | .startHold | .restartHold | .stopRise | .stopHigh => ⟨.release, .low⟩
  | .setup slot | .fall slot => ⟨.low, dataDrive r slot⟩
  | .rise slot | .high slot => ⟨.release, dataDrive r slot⟩
  | .restartSetup => ⟨.low, .release⟩
  | .stopLow => ⟨.low, .low⟩
  | _ => {}

/-- ACK status has separate storage from received data. -/
def sampleAt (slot : Fin 36) : Option (Fin 16) :=
  if slot.val == 8 then some 8
  else if slot.val == 17 then some 9
  else if slot.val == 26 then some 10
  else if h : 27 ≤ slot.val ∧ slot.val < 35 then some ⟨slot.val - 27, by omega⟩
  else none

def latch (samples : Vector Bool 16) (slot : Fin 36) (sda : Bool) : Vector Bool 16 :=
  match sampleAt slot with
  | none => samples
  | some k => samples.set k sda

def afterFall (samples : Vector Bool 16) (slot : Fin 36) : Phase :=
  if (slot.val == 8 && samples[8]) || (slot.val == 17 && samples[9]) ||
      (slot.val == 26 && samples[10]) then .stopLow
  else if slot.val == 17 then .restartSetup
  else if h : slot.val + 1 < 36 then .setup ⟨slot.val + 1, h⟩
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

def step (cfg : Config) (s : State) (bus : Bus) : State :=
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
  | .fall slot => timed cfg s (afterFall s.samples slot)
  | .restartSetup => timed cfg s .restartRise
  | .restartRise => if bus.scl then move cfg s .restartHigh else blocked cfg s
  | .restartHigh => guarded cfg s (bus.scl && bus.sda) .restartHold
  | .restartHold => guarded cfg s bus.scl (.setup 18)
  | .stopLow => timed cfg s .stopRise
  | .stopRise => if bus.scl then move cfg s .stopHigh else blocked cfg s
  | .stopHigh => guarded cfg s bus.scl .stopFree
  | .stopFree => guarded cfg s (bus.scl && bus.sda) .finished

def received (samples : Vector Bool 16) : BitVec 8 :=
  BitVec.ofBoolListBE [samples[0], samples[1], samples[2], samples[3],
    samples[4], samples[5], samples[6], samples[7]]

def outcome (samples : Vector Bool 16) : Outcome :=
  if samples[8] then .writeAddressNack else if samples[9] then .registerNack
  else if samples[10] then .readAddressNack else .success (received samples)

def result (s : State) : Option Outcome :=
  match s.phase with
  | .finished => some (outcome s.samples)
  | .timeout => some .timeout
  | .fault => some .busFault
  | _ => none

def run (cfg : Config) (s : State) (incoming : Nat → Bus) : Nat → State
  | 0 => s
  | n + 1 => step cfg (run cfg s incoming n) (incoming (n + 1))

end Pinwheel.I2C.RegisterRead
