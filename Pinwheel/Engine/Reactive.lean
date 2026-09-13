import Pinwheel.Engine.Step

/-! Candidate extended engine. The existing engine and encoded circuit remain the baseline. -/
namespace Pinwheel.Engine.Reactive

abbrev Inputs := BitVec 2

/-- Values and drive enables are commands; neither is an observed input level. -/
structure Pins where
  levels : Levels := 0
  enabled : Levels := 0
  deriving DecidableEq, Repr

def Pins.pushPull (levels : Levels) : Pins := ⟨levels, 7⟩
def Pins.openDrain (pullLow : Levels) : Pins := ⟨0, pullLow⟩

structure Capture where
  input : Fin 2
  destination : Fin 8
  deriving DecidableEq, Repr

structure Action where
  pins : Pins
  durationMinusOne : Fin 256
  capture : Option Capture := none
  deriving DecidableEq, Repr

def Action.duration (a : Action) : Nat := a.durationMinusOne.val + 1

structure Condition where
  input : Fin 2
  level : Bool
  deriving DecidableEq, Repr

def Condition.ready (c : Condition) (inputs : Inputs) : Bool := inputs[c.input.val] == c.level

structure Wait where
  pins : Pins
  condition : Condition
  budgetMinusOne : Fin 256
  deriving DecidableEq, Repr

inductive Instruction where
  | action (a : Action)
  | wait (w : Wait)
  | halt
  deriving DecidableEq, Repr

/-- Idle commands also apply to reset, timeout, and malformed execution. -/
structure Program where
  memory : Vector Instruction 32
  idle : Pins
  deriving DecidableEq, Repr

def Program.fetch (p : Program) (pc : Fin 32) : Instruction := p.memory[pc.val]

inductive Stop where
  | ready | completed | fault | timeout
  deriving DecidableEq, Repr

inductive Control where
  | stopped (reason : Stop)
  | active (pc : Fin 32) (remaining : Fin 256)
  | waiting (pc : Fin 32) (remaining : Fin 256)
  deriving DecidableEq, Repr

structure State where
  control : Control
  pins : Pins
  samples : Samples
  deriving DecidableEq, Repr

def busy (s : State) : Bool := match s.control with
  | .stopped _ => false
  | _ => true

def result (s : State) : Option Samples := match s.control with
  | .stopped .completed => some s.samples
  | _ => none

def capture (slots : Samples) (c : Option Capture) (inputs : Inputs) : Samples :=
  match c with
  | none => slots
  | some c => Engine.capture slots (some c.destination) inputs[c.input.val]

def stop (p : Program) (reason : Stop) (slots : Samples) : State :=
  ⟨.stopped reason, p.idle, slots⟩

def reset (p : Program) : State := stop p .ready (Vector.replicate 8 false)

/-- Wait entry only applies commands. Its first observation is on the following edge. -/
def enter (p : Program) (pc : Fin 32) (slots : Samples) (inputs : Inputs) : State :=
  match p.fetch pc with
  | .halt => stop p .completed slots
  | .action a => ⟨.active pc a.durationMinusOne, a.pins, capture slots a.capture inputs⟩
  | .wait w => ⟨.waiting pc w.budgetMinusOne, w.pins, slots⟩

def start (p : Program) (inputs : Inputs) : State := enter p 0 (Vector.replicate 8 false) inputs

def next (p : Program) (pc : Fin 32) (slots : Samples) (inputs : Inputs) : State :=
  if h : pc.val + 1 < 32 then enter p ⟨pc.val + 1, h⟩ slots inputs
  else stop p .fault slots

def advance (p : Program) (s : State) (inputs : Inputs) : State :=
  match s.control with
  | .stopped _ => s
  | .active pc remaining =>
    if h : 0 < remaining.val then
      {s with control := .active pc ⟨remaining.val - 1, by omega⟩}
    else next p pc s.samples inputs
  | .waiting pc remaining =>
    match p.fetch pc with
    | .wait w =>
      if w.condition.ready inputs then next p pc s.samples inputs
      else if h : 0 < remaining.val then
        {s with control := .waiting pc ⟨remaining.val - 1, by omega⟩}
      else stop p .timeout s.samples
    | _ => stop p .fault s.samples

def step (p : Program) (s : State) (resetRequested startRequested : Bool) (inputs : Inputs) : State :=
  if resetRequested then reset p
  else if busy s then advance p s inputs
  else if startRequested then start p inputs
  else s

def run (p : Program) (s : State) (incoming : Nat → Inputs) : Nat → State
  | 0 => s
  | n + 1 => advance p (run p s incoming n) (incoming (n + 1))

structure Machine where
  program : Program
  state : State
  deriving DecidableEq, Repr

def load (m : Machine) (p : Program) : Machine × Bool :=
  if busy m.state then (m, false) else (⟨p, reset p⟩, true)

end Pinwheel.Engine.Reactive
