import Pinwheel.I2C.Spec

/-! One or two bytes after a register-index write and repeated START. The compact
result reuses ACK destinations only after all three ACKs succeed. Success owns
all sixteen payload bits; timeout and NACK/bus-fault results discard partial data.
The diagnostic NACK stage belongs to the reference, not the hardware result. -/
namespace Pinwheel.I2C.RegisterReadTransaction

structure Request where
  address : Fin 128
  register : BitVec 8
  countMinusOne : Fin 2
  deriving DecidableEq, Repr

def Request.byteCount (r : Request) : Nat := r.countMinusOne.val + 1

inductive NackStage where
  | writeAddress | register | readAddress
  deriving DecidableEq, Repr

inductive Outcome where
  | success (payload : BitVec 16)
  | timeout | nackOrBusFault
  deriving DecidableEq, Repr

inductive Phase where
  | free | startHold
  | setup (slot : Fin 45) | rise (slot : Fin 45) | high (slot : Fin 45) | fall (slot : Fin 45)
  | restartSetup | restartRise | restartHigh | restartHold
  | stopLow (nack : Bool) | stopRise (nack : Bool) | stopHigh (nack : Bool) | stopFree (nack : Bool)
  | nackTerminal | finished | timeout | fault
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  remaining : Fin 256
  waitLeft : Fin 256
  samples : Vector Bool 16
  /-- Ghost diagnostic retained after a first NACK; absent from the compact packet. -/
  nackStage : Option NackStage := none
  deriving DecidableEq, Repr

def initial (cfg : Config) : State :=
  ⟨.free, cfg.phaseMinusOne, cfg.waitMinusOne, Vector.replicate 16 false, none⟩

def releaseData (r : Request) (slot : Fin 45) : Bool :=
  if slot.val < 8 then (r.address.val * 2).testBit (7 - slot.val)
  else if slot.val < 9 then true
  else if slot.val < 17 then r.register.getLsbD (16 - slot.val)
  else if slot.val < 18 then true
  else if slot.val < 26 then (r.address.val * 2 + 1).testBit (25 - slot.val)
  else if slot.val == 35 then r.countMinusOne.val == 0
  else true

def dataDrive (r : Request) (slot : Fin 45) : Drive :=
  if releaseData r slot then .release else .low

def pins (r : Request) (phase : Phase) : Pins :=
  match phase with
  | .startHold | .restartHold | .stopRise _ | .stopHigh _ => ⟨.release, .low⟩
  | .setup slot | .fall slot => ⟨.low, dataDrive r slot⟩
  | .rise slot | .high slot => ⟨.release, dataDrive r slot⟩
  | .restartSetup => ⟨.low, .release⟩
  | .stopLow _ => ⟨.low, .low⟩
  | _ => {}

/-- ACKs use slots 0–2 before reception; payload then overwrites those slots. -/
def sampleAt (slot : Fin 45) : Option (Fin 16) :=
  if slot.val == 8 then some 0
  else if slot.val == 17 then some 1
  else if slot.val == 26 then some 2
  else if h : 27 ≤ slot.val ∧ slot.val < 35 then some ⟨slot.val - 27, by omega⟩
  else if h : 36 ≤ slot.val ∧ slot.val < 44 then some ⟨slot.val - 28, by omega⟩
  else none

def latch (samples : Vector Bool 16) (slot : Fin 45) (sda : Bool) : Vector Bool 16 :=
  match sampleAt slot with
  | none => samples
  | some k => samples.set k sda

def nackAt (samples : Vector Bool 16) (slot : Fin 45) : Option NackStage :=
  if slot.val == 8 && samples[0] then some .writeAddress
  else if slot.val == 17 && samples[1] then some .register
  else if slot.val == 26 && samples[2] then some .readAddress
  else none

def afterFall (r : Request) (samples : Vector Bool 16) (slot : Fin 45) : Phase :=
  if (slot.val == 8 && samples[0]) || (slot.val == 17 && samples[1]) ||
      (slot.val == 26 && samples[2]) then .stopLow true
  else if slot.val == 17 then .restartSetup
  else if slot.val == 35 && r.countMinusOne.val == 0 then .stopLow false
  else if h : slot.val + 1 < 45 then .setup ⟨slot.val + 1, h⟩
  else .stopLow false

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
  | .fall slot => if s.remaining.val == 0 then
      move cfg {s with nackStage := (nackAt s.samples slot).or s.nackStage} (afterFall r s.samples slot)
    else count s
  | .restartSetup => timed cfg s .restartRise
  | .restartRise => if bus.scl then move cfg s .restartHigh else blocked cfg s
  | .restartHigh => guarded cfg s (bus.scl && bus.sda) .restartHold
  | .restartHold => guarded cfg s bus.scl (.setup 18)
  | .stopLow nack => timed cfg s (.stopRise nack)
  | .stopRise nack => if bus.scl then move cfg s (.stopHigh nack) else blocked cfg s
  | .stopHigh nack => guarded cfg s bus.scl (.stopFree nack)
  | .stopFree nack => if bus.scl && bus.sda then
      if s.remaining.val == 0 then
        if nack then {move cfg s .nackTerminal with remaining := 0}
        else move cfg s .finished
      else {count s with waitLeft := cfg.waitMinusOne}
    else blocked cfg s
  -- One idle edge after qualified STOP; the compiler then reaches its structural bound.
  | .nackTerminal => finish s .fault

def received (r : Request) (samples : Vector Bool 16) : BitVec 16 :=
  if r.countMinusOne.val == 0 then
    BitVec.zeroExtend 16 (BitVec.ofBoolListBE [samples[0], samples[1], samples[2], samples[3],
      samples[4], samples[5], samples[6], samples[7]])
  else BitVec.ofBoolListBE [samples[0], samples[1], samples[2], samples[3],
    samples[4], samples[5], samples[6], samples[7], samples[8], samples[9],
    samples[10], samples[11], samples[12], samples[13], samples[14], samples[15]]

def result (r : Request) (s : State) : Option Outcome :=
  match s.phase with
  | .finished => some (.success (received r s.samples))
  | .timeout => some .timeout
  | .fault => some .nackOrBusFault
  | _ => none

def run (cfg : Config) (r : Request) (s : State) (incoming : Nat → Bus) : Nat → State
  | 0 => s
  | n + 1 => step cfg r (run cfg r s incoming n) (incoming (n + 1))

end Pinwheel.I2C.RegisterReadTransaction
