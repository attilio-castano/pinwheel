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

structure Capture (lastSample : Nat := 7) where
  input : Fin 2
  destination : Fin (lastSample + 1)
  deriving DecidableEq, Repr

structure Action (lastSample : Nat := 7) where
  pins : Pins
  durationMinusOne : Fin 256
  capture : Option (Capture lastSample) := none
  deriving DecidableEq, Repr

def Action.duration (a : Action lastSample) : Nat := a.durationMinusOne.val + 1

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

/-- Match selected observed bits; bits outside the mask are irrelevant. -/
structure Check where
  mask : Inputs
  value : Inputs
  deriving DecidableEq, Repr

def Check.ready (c : Check) (inputs : Inputs) : Bool :=
  inputs &&& c.mask == c.value &&& c.mask

inductive Finish (lastAddress : Nat := 127) (lastSample : Nat := 7) where
  | sequential
  | jump (target : Fin (lastAddress + 1))
  | branch (sample : Fin (lastSample + 1)) (whenTrue whenFalse : Fin (lastAddress + 1))
  deriving DecidableEq, Repr

/-- Guard each edge, capture at the terminal edge, then choose the successor. -/
structure Checked (lastAddress : Nat := 127) (lastSample : Nat := 7) where
  action : Action lastSample
  guard : Check
  terminalCapture : Option (Capture lastSample) := none
  finish : Finish lastAddress lastSample := .sequential
  deriving DecidableEq, Repr

/-- Require a consecutive ready interval; blocked input resets it and consumes wait budget. -/
structure Qualify where
  pins : Pins
  condition : Check
  durationMinusOne : Fin 256
  budgetMinusOne : Fin 256
  deriving DecidableEq, Repr

inductive Instruction (lastAddress : Nat := 127) (lastSample : Nat := 7) where
  | action (a : Action lastSample)
  | wait (w : Wait)
  | checked (a : Checked lastAddress lastSample)
  | qualify (q : Qualify)
  | halt
  deriving DecidableEq, Repr

/-- Idle commands also apply to reset, timeout, and malformed execution. -/
structure Program (lastAddress : Nat := 127) (lastSample : Nat := 7) where
  memory : Vector (Instruction lastAddress lastSample) (lastAddress + 1)
  idle : Pins
  last : Fin (lastAddress + 1) := ⟨lastAddress, by omega⟩
  deriving DecidableEq, Repr

def Program.fetch (p : Program lastAddress lastSample) (pc : Fin (lastAddress + 1)) : Instruction lastAddress lastSample := p.memory[pc.val]

inductive Stop where
  | ready | completed | fault | timeout
  deriving DecidableEq, Repr

inductive Control (lastAddress : Nat := 127) where
  | stopped (reason : Stop)
  | active (pc : Fin (lastAddress + 1)) (remaining : Fin 256)
  | waiting (pc : Fin (lastAddress + 1)) (remaining : Fin 256)
  | checked (pc : Fin (lastAddress + 1)) (remaining : Fin 256)
  | qualifying (pc : Fin (lastAddress + 1)) (remaining waitLeft : Fin 256)
  deriving DecidableEq, Repr

structure State (lastAddress : Nat := 127) (lastSample : Nat := 7) where
  control : Control lastAddress
  pins : Pins
  samples : Vector Bool (lastSample + 1)
  deriving DecidableEq, Repr

def busy (s : State lastAddress lastSample) : Bool := match s.control with
  | .stopped _ => false
  | _ => true

def result (s : State lastAddress lastSample) : Option (Vector Bool (lastSample + 1)) := match s.control with
  | .stopped .completed => some s.samples
  | _ => none

def capture (slots : Vector Bool (lastSample + 1)) (c : Option (Capture lastSample)) (inputs : Inputs) : Vector Bool (lastSample + 1) :=
  match c with
  | none => slots
  | some c => Engine.capture slots (some c.destination) inputs[c.input.val]

def stop (p : Program lastAddress lastSample) (reason : Stop) (slots : Vector Bool (lastSample + 1)) : State lastAddress lastSample :=
  ⟨.stopped reason, p.idle, slots⟩

def reset (p : Program lastAddress lastSample) : State lastAddress lastSample := stop p .ready (Vector.replicate (lastSample + 1) false)

/-- Wait entry only applies commands. Its first observation is on the following edge. -/
def enter (p : Program lastAddress lastSample) (pc : Fin (lastAddress + 1)) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) : State lastAddress lastSample :=
  match p.fetch pc with
  | .halt => stop p .completed slots
  | .action a => ⟨.active pc a.durationMinusOne, a.pins, capture slots a.capture inputs⟩
  | .wait w => ⟨.waiting pc w.budgetMinusOne, w.pins, slots⟩
  | .checked a => ⟨.checked pc a.action.durationMinusOne, a.action.pins,
      capture slots a.action.capture inputs⟩
  | .qualify q => ⟨.qualifying pc q.durationMinusOne q.budgetMinusOne, q.pins, slots⟩

def start (p : Program lastAddress lastSample) (inputs : Inputs) : State lastAddress lastSample := enter p 0 (Vector.replicate (lastSample + 1) false) inputs

def next (p : Program lastAddress lastSample) (pc : Fin (lastAddress + 1)) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) : State lastAddress lastSample :=
  if h : pc.val < p.last.val then enter p ⟨pc.val + 1, by omega⟩ slots inputs
  else stop p .fault slots

def jump (p : Program lastAddress lastSample) (target : Fin (lastAddress + 1)) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) : State lastAddress lastSample :=
  if target.val ≤ p.last.val then enter p target slots inputs else stop p .fault slots

def dispatch (p : Program lastAddress lastSample) (pc : Fin (lastAddress + 1)) (finish : Finish lastAddress lastSample) (slots : Vector Bool (lastSample + 1)) (inputs : Inputs) : State lastAddress lastSample :=
  match finish with
  | .sequential => next p pc slots inputs
  | .jump target => jump p target slots inputs
  | .branch sample yes no => jump p (if slots[sample.val] then yes else no) slots inputs

def advance (p : Program lastAddress lastSample) (s : State lastAddress lastSample) (inputs : Inputs) : State lastAddress lastSample :=
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
  | .checked pc remaining =>
    match p.fetch pc with
    | .checked a =>
      if !a.guard.ready inputs then stop p .fault s.samples
      else if h : 0 < remaining.val then
        {s with control := .checked pc ⟨remaining.val - 1, by omega⟩}
      else dispatch p pc a.finish (capture s.samples a.terminalCapture inputs) inputs
    | _ => stop p .fault s.samples
  | .qualifying pc remaining waitLeft =>
    match p.fetch pc with
    | .qualify q =>
      if q.condition.ready inputs then
        if h : 0 < remaining.val then
          {s with control := .qualifying pc ⟨remaining.val - 1, by omega⟩ q.budgetMinusOne}
        else next p pc s.samples inputs
      else if h : 0 < waitLeft.val then
        {s with control := .qualifying pc q.durationMinusOne ⟨waitLeft.val - 1, by omega⟩}
      else stop p .timeout s.samples
    | _ => stop p .fault s.samples

def step (p : Program lastAddress lastSample) (s : State lastAddress lastSample) (resetRequested startRequested : Bool) (inputs : Inputs) : State lastAddress lastSample :=
  if resetRequested then reset p
  else if busy s then advance p s inputs
  else if startRequested then start p inputs
  else s

def run (p : Program lastAddress lastSample) (s : State lastAddress lastSample) (incoming : Nat → Inputs) : Nat → State lastAddress lastSample
  | 0 => s
  | n + 1 => advance p (run p s incoming n) (incoming (n + 1))

structure Machine (lastAddress : Nat := 127) (lastSample : Nat := 7) where
  program : Program lastAddress lastSample
  state : State lastAddress lastSample
  deriving DecidableEq, Repr

def load (m : Machine lastAddress lastSample) (p : Program lastAddress lastSample) : Machine lastAddress lastSample × Bool :=
  if busy m.state then (m, false) else (⟨p, reset p⟩, true)

end Pinwheel.Engine.Reactive
