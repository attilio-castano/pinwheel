import Pinwheel.I2C.Spec

namespace Pinwheel.I2C

inductive Phase where
  | free | startHold | setup | rise | high | fall
  | stopLow | stopRise | stopHigh | stopFree | finished
  deriving DecidableEq, Repr

/-- Bounded reference controller. Result is visible only in finished phase. -/
structure State where
  request : Request
  phase : Phase
  slot : Fin 18
  remaining : Fin 256
  waitLeft : Fin 256
  outcome : Outcome
  deriving DecidableEq, Repr

def initial (cfg : Config) (r : Request) : State :=
  ⟨r, .free, 0, cfg.phaseMinusOne, cfg.waitMinusOne, .success⟩

def busy (s : State) : Bool := s.phase != .finished

def result (s : State) : Option Outcome := if busy s then none else some s.outcome

/-- Controller bit selection, independent of the explicit wireBits vector. -/
def releaseData (r : Request) (slot : Fin 18) : Bool :=
  if slot.val < 7 then r.address.val.testBit (6 - slot.val)
  else if slot.val == 7 then false
  else if slot.val == 8 || slot.val == 17 then true
  else r.data.getLsbD (16 - slot.val)

def dataDrive (s : State) : Drive := if releaseData s.request s.slot then .release else .low

def pins (s : State) : Pins :=
  match s.phase with
  | .free | .stopFree | .finished => ⟨.release, .release⟩
  | .startHold | .stopRise | .stopHigh => ⟨.release, .low⟩
  | .setup | .fall => ⟨.low, dataDrive s⟩
  | .rise | .high => ⟨.release, dataDrive s⟩
  | .stopLow => ⟨.low, .low⟩

def move (cfg : Config) (s : State) (phase : Phase) : State :=
  {s with phase := phase, remaining := cfg.phaseMinusOne, waitLeft := cfg.waitMinusOne}

def finish (s : State) (outcome : Outcome) : State :=
  {s with phase := .finished, remaining := 0, waitLeft := 0, outcome := outcome}

def count (s : State) : State :=
  {s with remaining := ⟨s.remaining.val - 1, by omega⟩}

/-- A wait budget counts blocked observations. A ready observation wins at the deadline. -/
def blocked (cfg : Config) (s : State) : State :=
  if h : 0 < s.waitLeft.val then
    {s with waitLeft := ⟨s.waitLeft.val - 1, by omega⟩, remaining := cfg.phaseMinusOne}
  else finish s .timeout

def afterHigh (cfg : Config) (s : State) (sda : Bool) : State :=
  let outcome := if s.slot.val == 8 && sda then Outcome.addressNack
    else if s.slot.val == 17 && sda then Outcome.dataNack else s.outcome
  move cfg {s with outcome := outcome} .fall

def afterFall (cfg : Config) (s : State) : State :=
  if s.outcome != .success then move cfg s .stopLow
  else if h : s.slot.val + 1 < 18 then move cfg {s with slot := ⟨s.slot.val + 1, h⟩} .setup
  else move cfg s .stopLow

/-- Input is the resolved bus immediately before this edge. All commands are post-edge. -/
def step (cfg : Config) (s : State) (bus : Bus) (reset : Bool := false) : State :=
  if reset then finish s .resetAbort else
  match s.phase with
  | .finished => s
  | .free =>
    if bus.scl && bus.sda then
      if s.remaining.val == 0 then move cfg s .startHold
      else {count s with waitLeft := cfg.waitMinusOne}
    else blocked cfg s
  | .rise => if bus.scl then move cfg s .high else blocked cfg s
  | .stopRise => if bus.scl then move cfg s .stopHigh else blocked cfg s
  | .high =>
    if !bus.scl then finish s .busFault
    else if s.remaining.val == 0 then afterHigh cfg s bus.sda else count s
  | .stopHigh =>
    if !bus.scl then finish s .busFault
    else if s.remaining.val == 0 then move cfg s .stopFree else count s
  -- Bus-free time after STOP is qualified exactly as it is before START. Behind input
  -- registers the first observations still show the controller's own SDA low.
  | .stopFree =>
    if bus.scl && bus.sda then
      if s.remaining.val == 0 then finish s s.outcome
      else {count s with waitLeft := cfg.waitMinusOne}
    else blocked cfg s
  | .startHold =>
    if !bus.scl then finish s .busFault
    else if s.remaining.val == 0 then move cfg s .setup else count s
  | .setup => if s.remaining.val == 0 then move cfg s .rise else count s
  | .fall => if s.remaining.val == 0 then afterFall cfg s else count s
  | .stopLow => if s.remaining.val == 0 then move cfg s .stopRise else count s

def run (cfg : Config) (s : State) (incoming : Nat → Bus) : Nat → State
  | 0 => s
  | n + 1 => step cfg (run cfg s incoming n) (incoming (n + 1))

end Pinwheel.I2C
